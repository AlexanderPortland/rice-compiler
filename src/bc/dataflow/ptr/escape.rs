use std::{collections::HashMap, sync::Arc};

use crate::{
    bc::{
        dataflow::{
            self, Analysis, JoinSemiLattice, analyze_to_fixpoint,
            ptr::{Allocation, InitialPointerAnalysis, Ptr},
        },
        types::{
            AllocLoc, Function, Local, Location, Operand, Place, Rvalue, Statement, TerminatorKind,
            Type,
        },
        visit::{Visit, VisitMut},
    },
    utils::Symbol,
};
use indexical::{
    ArcIndexSet, ArcIndexVec, IndexedDomain, RcIndexSet, pointer::PointerFamily, vec::IndexVec,
};
use itertools::Itertools;

/// Changes any heap allocations that don't escape their current function to be stack allocated instead.
pub fn stack_for_non_escaping(func: &mut Function) -> bool {
    if func.name == Symbol::main() {
        return false;
    }
    let alloc_domain = Arc::new(IndexedDomain::from_iter(
        func.body.locations().iter().map(|a| Allocation(*a)),
    ));

    let mut analysis = InitialPointerAnalysis::new(alloc_domain.clone());

    analysis.visit_function(func);

    let p = analysis.points_to();

    let ret_places = ret_places(func);
    // println!("ret places of {} are {:?}", func.name, ret_places);

    let mut escapes = escapes(p, ret_places, alloc_domain);

    // todo!();
    escapes.visit_function(func);

    escapes.1
}

pub struct Escapes(ArcIndexSet<Allocation>, bool);

impl VisitMut for Escapes {
    fn visit_statement(&mut self, stmt: &mut Statement, loc: Location) {
        if let Rvalue::Alloc {
            kind,
            loc: alloc_loc,
            args,
        } = &mut stmt.rvalue
            && self.0.contains(Allocation(loc))
            && *alloc_loc != crate::bc::types::AllocLoc::Stack
        {
            *alloc_loc = crate::bc::types::AllocLoc::Stack;
            self.1 |= true;
        }
        self.super_visit_statement(stmt, loc);
    }
}

fn escapes(
    points_to: HashMap<Ptr, ArcIndexSet<Allocation>>,
    ret_places: Vec<Place>,
    domain: Arc<IndexedDomain<Allocation>>,
) -> Escapes {
    let mut escaping_allocations = ArcIndexSet::new(&domain);

    for ret_place in ret_places {
        if let Some(direct_points_to) = points_to.get(&Ptr::Place(Place::new(
            ret_place.local,
            ret_place.projection.clone(),
            Type::unit(),
        ))) {
            for direct in direct_points_to.iter() {
                escaping_allocations.insert(direct);
            }
        }
    }

    loop {
        let old_size = escaping_allocations.len();

        for allocation in escaping_allocations.iter().cloned().collect::<Vec<_>>() {
            for (ptr, allocs) in &points_to {
                if let Ptr::AllocationEl(alloc, _proj) = ptr
                    && *alloc == allocation
                {
                    escaping_allocations.union(allocs);
                }
            }
        }

        if old_size == escaping_allocations.len() {
            break;
        }
    }

    for alloc in escaping_allocations.iter() {
        // println!("{alloc:?} escapes!");
    }

    Escapes(escaping_allocations, false)
}

fn ret_places(func: &Function) -> Vec<Place> {
    let mut places = RetPlaces(Vec::new());
    places.visit_function(func);
    places.0
}

pub struct RetPlaces(Vec<Place>);

impl Visit for RetPlaces {
    fn visit_terminator(&mut self, term: &crate::bc::types::Terminator, loc: Location) {
        if let TerminatorKind::Return(Operand::Place(place)) = term.kind() {
            self.0.push(*place);
        }
        self.super_visit_terminator(term, loc);
    }
}
