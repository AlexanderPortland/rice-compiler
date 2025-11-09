use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::bc::{
    dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
    print,
    types::{
        BasicBlockIdx, Function, Local, LocalIdx, Location, Operand, Place, ProjectionElem, Rvalue,
        Statement, TerminatorKind,
    },
    visit::{Visit, VisitMut},
};
use indexical::{
    ArcIndexSet, ArcIndexVec, IndexedDomain, RcIndexSet, pointer::PointerFamily, vec::IndexVec,
};
use itertools::{Itertools, chain};
use petgraph::visit::{EdgeRef, NodeRef};

/// Remove **all unreachable basic blocks** from the CFG.
///
/// This has no real effect in terms of immediate functionality, but can simplify control flow
/// in a way that will allow us to do other optimizations.
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

        if changed {
            // println!("did SOMETHING for unused");
            // TODO: i dont think this is the right way to do this
            // as there's still a chance a change way down the tree could get lost
            func.body.regenerate_everything();
        } else {
            // println!("did nothing for unused");
            break 'done;
        }
    }

    global_changed
}

// TODO: could also do some sort of terminator
// TODO: also can probably merge straight-line blocks into a single one

/// Modifies terminators to **skip over any empty basic blocks** that will immediately jump to another block.
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
            TerminatorKind::Return(_) => (),
        }

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

pub fn merge_straight_line_blocks(func: &mut Function) -> bool {
    let merge_into = mergeable_blocks(func);
    let merge_into_me = merge_into_me(&merge_into, func);

    if merge_into_me.is_empty() {
        return false;
    }
    for base in func.body.blocks().collect::<Vec<_>>() {
        if let Some(merge_in) = merge_into_me.get(&base) {
            let mut new_stmts = Vec::new();

            for bring_in in merge_in {
                let bring_in_block = func.body.data_mut(*bring_in);
                new_stmts.append(&mut bring_in_block.statements);
            }

            let Some(last_block) = merge_in.last() else {
                panic!("no blocks in here...");
            };

            let new_term = func.body.data(*last_block).terminator.clone();

            let base_mut = func.body.data_mut(base);
            base_mut.statements.extend(new_stmts);
            base_mut.terminator = new_term;

            let Some(first_bring_in) = merge_in.first() else {
                panic!("should have a first element");
            };

            // Add an edge to whoever we point to now
            for out_target in func
                .body
                .cfg()
                .edges_directed((*last_block).into(), petgraph::Direction::Outgoing)
                .map(|a| a.target())
                .collect::<Vec<_>>()
            {
                func.body.cfg_mut().add_edge(base.into(), out_target, ());
            }

            // Remove edges between the merged jawns
            let edge = func
                .body
                .cfg()
                .find_edge(base.into(), (*first_bring_in).into())
                .expect("edge should exist");
            func.body
                .cfg_mut()
                .remove_edge(edge)
                .expect("edge should exist");
            for bring_in in merge_in {
                func.body.remove_block_cfg_edges(*bring_in);
            }
        }
    }

    func.body.regenerate_everything();

    true
}

fn merge_into_me(
    merge_into: &HashMap<BasicBlockIdx, BasicBlockIdx>,
    func: &Function,
) -> HashMap<BasicBlockIdx, Vec<BasicBlockIdx>> {
    let roots: HashSet<BasicBlockIdx> = func
        .body
        .blocks()
        .filter(|b| !merge_into.contains_key(b))
        .collect();

    let mut parent_to_child: HashMap<BasicBlockIdx, BasicBlockIdx> = HashMap::new();
    for (&child, &parent) in merge_into {
        parent_to_child.insert(parent, child);
    }

    // println!("roots {:?}", roots);

    let mut chains = HashMap::new();
    for &root in &roots {
        let mut chain = vec![];
        let mut current = root;

        // Follow the chain until we reach a node with no child
        while let Some(&child) = parent_to_child.get(&current) {
            chain.push(child);
            current = child;
        }

        if !chain.is_empty() {
            chains.insert(root, chain);
        }
    }

    chains
}

fn mergeable_blocks(func: &Function) -> HashMap<BasicBlockIdx, BasicBlockIdx> {
    let mut merge_into = HashMap::new();
    // Loop through basic blocks, seeing which ones have a single outgoing edge
    for block in func.body.blocks() {
        let data = func.body.data(block);

        // Ensure there's only one outgoing edge
        let [outgoing] = &*func
            .body
            .cfg()
            .edges_directed(block.into(), petgraph::Direction::Outgoing)
            .collect::<Box<[_]>>()
        else {
            continue;
        };

        let to: BasicBlockIdx = outgoing.target().into();
        match data.terminator.kind() {
            TerminatorKind::Jump(jmp_to) if *jmp_to == to => (),
            _ => panic!(
                "if we only have one outgoing edge, our terminator should just be a jump there, anything else is malformed"
            ),
        }

        // And we're the only block that points to them
        let [coming_back] = &*func
            .body
            .cfg()
            .edges_directed(outgoing.target(), petgraph::Direction::Incoming)
            .collect::<Box<[_]>>()
        else {
            continue;
        };

        let coming_back_to: BasicBlockIdx = coming_back.source().into();
        assert_eq!(coming_back_to, block);

        merge_into.insert(to, block);
    }
    merge_into
}

pub fn remove_unused_locals(func: &mut Function) -> bool {
    let used = used_locals(func);
    let old_local_domain = func.locals.clone();

    if used.len() == old_local_domain.len() {
        // println!("did nothing for locals");
        return false;
    }
    // println!("did SOMETHING for locals");

    let mut new_locals: Vec<Local> = Vec::new();
    let mut mapping: HashMap<LocalIdx, LocalIdx> = HashMap::new();

    // Add locals to the new domain and build a mapping between them
    for (old_idx, local) in func.locals.iter_enumerated() {
        if used.contains(&old_idx) {
            let new_idx = new_locals.len();
            new_locals.push(*local);
            mapping.insert(old_idx, new_idx.into());
        }
    }

    let new_local_domain = IndexedDomain::from_iter(new_locals);

    // Update all the local idxs in the function
    let mut updater =
        LocalUpdater(&|idx: LocalIdx| *mapping.get(&idx).expect("should have an entry"));
    updater.visit_function(func);

    // Then update the old domain to be the new one
    func.locals = Arc::new(new_local_domain);

    // We only went through all this if there were locals to trim down,
    // so things must have changed
    true
}

pub fn update_locals_w(func: &mut Function, f: &dyn Fn(LocalIdx) -> LocalIdx) {
    let mut updater = LocalUpdater(f);
    updater.visit_function(func);
}

fn used_locals(func: &Function) -> HashSet<LocalIdx> {
    let mut visit = LocalVisitor::new(&func.locals);
    visit.visit_function(func);
    std::iter::once(0.into()).chain(visit.0.indices()).collect()
}

struct LocalVisitor(ArcIndexSet<Local>);

impl LocalVisitor {
    pub fn new(domain: &Arc<IndexedDomain<Local>>) -> Self {
        LocalVisitor(ArcIndexSet::new(domain))
    }
}

impl Visit for LocalVisitor {
    fn visit_function(&mut self, func: &Function) {
        for (param, _) in func.params() {
            self.0.insert(param);
        }

        self.super_visit_function(func);
    }

    fn visit_lvalue(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        self.0.insert(place.local);
    }

    fn visit_rvalue_place(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        self.0.insert(place.local);
    }
}

/// TODO: merge these jawns...
pub struct BBUpdater<'z>(pub &'z dyn Fn(BasicBlockIdx) -> BasicBlockIdx);

impl VisitMut for BBUpdater<'_> {
    fn visit_terminator(&mut self, term: &mut crate::bc::types::Terminator, loc: Location) {
        match &mut term.kind {
            TerminatorKind::CondJump {
                cond,
                true_,
                false_,
            } => {
                *true_ = self.0(*true_);
                *false_ = self.0(*false_);
            }
            TerminatorKind::Jump(to) => *to = self.0(*to),
            TerminatorKind::Return(_) => (),
        }
        self.super_visit_terminator(term, loc);
    }
}

pub struct LocalUpdater<'z>(pub &'z dyn Fn(LocalIdx) -> LocalIdx);

impl VisitMut for LocalUpdater<'_> {
    #[allow(clippy::only_used_in_recursion)]
    fn visit_place(&mut self, place: &mut crate::bc::types::Place, loc: Location) {
        let new_local = self.0(place.local);

        let new_proj = place
            .projection
            .iter()
            .cloned()
            .map(|mut proj| {
                if let ProjectionElem::Index {
                    index: Operand::Place(index_place),
                    ty,
                } = &mut proj
                {
                    self.visit_place(index_place, loc);
                }

                proj
            })
            .collect::<Vec<_>>();

        *place = Place::new(new_local, new_proj, place.ty);
    }
}
