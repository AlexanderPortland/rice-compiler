use std::collections::HashMap;

use crate::bc::{
    dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
    types::{BasicBlockIdx, Function, Local, Location, Operand, Rvalue, Statement, TerminatorKind},
    visit::{Visit, VisitMut},
};
use indexical::{ArcIndexSet, ArcIndexVec, RcIndexSet, pointer::PointerFamily, vec::IndexVec};
use itertools::Itertools;

pub fn remove_unused_blocks(func: &mut Function) -> bool {
    let mut global_changed = false;
    'done: loop {
        let mut changed = false;
        'try_again: for b in func.body.blocks().collect::<Vec<_>>() {
            let cfg_edges_in = func
                .body
                .cfg()
                .neighbors_directed(b.into(), petgraph::Direction::Incoming)
                .collect::<Vec<_>>();

            if cfg_edges_in.is_empty() && b != 0 {
                func.body.remove_block_cfg_edges(b);
                changed = true;
                global_changed = true;
            }
        }

        if !changed {
            break 'done;
        } else {
            // TODO: i dont think this is the right way to do this
            // as there's still a chance a change way down the tree could get lost
            func.body.regenerate_everything();
        }
    }

    global_changed
}

pub fn skip_empty_blocks(func: &mut Function) -> bool {
    let mut just_goes_to: HashMap<BasicBlockIdx, BasicBlockIdx> = HashMap::new();
    let body = &mut func.body;

    for block_idx in body.blocks() {
        let block = body.data(block_idx);
        if block.statements.is_empty()
            && let TerminatorKind::Jump(to_idx) = block.terminator.kind()
        {
            just_goes_to.insert(block_idx, *to_idx);
        }
    }

    let mut changed = false;

    for block_idx in body.blocks().collect::<Vec<_>>() {
        let block = body.data_mut(block_idx);
        let mut new_point_to = Vec::new();
        let mut removed_to = Vec::new();

        match &mut block.terminator.kind {
            TerminatorKind::CondJump {
                cond,
                true_,
                false_,
            } => {
                if let Some(true_instead) = just_goes_to.get(true_) {
                    new_point_to.push(*true_instead);
                    removed_to.push(*true_);
                    *true_ = *true_instead;
                }
                if let Some(false_instead) = just_goes_to.get(false_) {
                    new_point_to.push(*false_instead);
                    removed_to.push(*false_);
                    *false_ = *false_instead;
                }
            }
            TerminatorKind::Jump(to) => {
                if let Some(instead) = just_goes_to.get(to) {
                    // we no longer go to `to`
                    new_point_to.push(*instead);
                    removed_to.push(*to);
                    *to = *instead;
                }
            }
            _ => (),
        };

        for removed_edge in removed_to {
            changed |= true;

            let e = body
                .cfg()
                .find_edge(block_idx.into(), removed_edge.into())
                .expect("should have an edge");

            body.cfg_mut()
                .remove_edge(e)
                .expect("should be able to remove it");
        }

        for new_edge in new_point_to {
            changed |= true;
            body.cfg_mut()
                .add_edge(block_idx.into(), new_edge.into(), ());
        }
    }

    false
}
