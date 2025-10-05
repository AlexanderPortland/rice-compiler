use std::collections::HashMap;

use crate::bc::{
    dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
    types::{BasicBlockIdx, Function, Local, Location, Operand, Rvalue, Statement},
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

pub fn remove_empty_block(func: &mut Function) -> bool {
    false
}

#[derive(Debug, Default)]
struct DeadBlockFinder {
    just_goes_to: HashMap<BasicBlockIdx, BasicBlockIdx>,
}

impl Visit for DeadBlockFinder {
    fn visit_terminator(&mut self, term: &crate::bc::types::Terminator, loc: Location) {}
}
