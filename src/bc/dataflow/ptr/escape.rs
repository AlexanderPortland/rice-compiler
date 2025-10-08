use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::bc::{
    dataflow::ptr::{
        pointer_analysis,
        types::{Allocation, MemLoc},
    },
    types::{
        AllocLoc, Function, LocalIdx, Location, Operand, Place, Rvalue, Statement, TerminatorKind,
        Type,
    },
    visit::{Visit, VisitMut},
};
use indexical::{
    ArcIndexSet, ArcIndexVec, IndexedDomain, RcIndexSet, pointer::PointerFamily, vec::IndexVec,
};
use itertools::Itertools;

/// Changes any heap allocations that don't escape their current function to be stack allocated instead.
pub fn stack_for_non_escaping(func: &mut Function) -> bool {
    let analysis = pointer_analysis(func);

    for (ptr, allocations) in analysis.points_to() {
        // println!("{}: {ptr} points to: ", func.name);
        for alloc in allocations.iter() {
            // println!("{}: \t->{alloc:?}", func.name);
        }
    }

    let mut escapes = escapes(func, analysis.points_to(), analysis.alloc_domain().clone());

    escapes.visit_function(func);

    escapes.1
}

#[derive(Debug)]
pub struct Escapes(ArcIndexSet<Allocation>, bool);

impl VisitMut for Escapes {
    fn visit_statement(&mut self, stmt: &mut Statement, loc: Location) {
        if let Rvalue::Alloc {
            kind,
            loc: alloc_loc,
            args,
        } = &mut stmt.rvalue
            && !self.0.contains(Allocation::from_loc(loc))
            && *alloc_loc != crate::bc::types::AllocLoc::Stack
        {
            *alloc_loc = crate::bc::types::AllocLoc::Stack;
            self.1 |= true;
        }
        self.super_visit_statement(stmt, loc);
    }
}

fn escapes(
    func: &Function,
    points_to: &HashMap<MemLoc, ArcIndexSet<Allocation>>,
    domain: Arc<IndexedDomain<Allocation>>,
) -> Escapes {
    let mut escaping_allocations = ArcIndexSet::new(&domain);
    let mut places = EscapingPlaces::default();
    places.visit_function(func);

    for escaping in places.into_iter() {
        for (ptr, allocations) in points_to {
            if let MemLoc::Local(l) = ptr
                && *l == escaping.local
            {
                // if p.projection.len() >=
                // println!("{}: {p} IS part of escaping {escaping}", func.name);
                // let proj = &p.projection[..escaping.projection.len()]
                escaping_allocations.union(allocations);
            } else {
                // println!("{}: {ptr} is NOT a part of escaping {escaping}", func.name);
            }
        }
    }

    loop {
        let old_size = escaping_allocations.len();

        for allocation in escaping_allocations.iter().cloned().collect::<Vec<_>>() {
            for (ptr, allocs) in points_to {
                if let MemLoc::Allocated(alloc, _proj) = ptr
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

#[derive(Default, Debug)]
pub struct EscapingPlaces {
    returned: Vec<Place>,
    passed_to_callees: Vec<Place>,
    caller_args: Vec<Place>,
}

impl EscapingPlaces {
    fn into_iter(self) -> impl Iterator<Item = Place> {
        self.returned
            .into_iter()
            .chain(self.passed_to_callees)
            .chain(self.caller_args)
    }
}

impl Visit for EscapingPlaces {
    fn visit_function(&mut self, func: &Function) {
        for param_no in 0..func.num_params {
            // println!("param no {param_no:?} of {:?}", func.num_params);
            self.caller_args.push(Place::new(
                LocalIdx::from_usize(param_no),
                vec![],
                Type::bool(),
            ))
        }

        self.super_visit_function(func);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        if let Rvalue::Call { args, .. } | Rvalue::MethodCall { args, .. } = rvalue {
            for arg in args {
                if let Operand::Place(place) = arg {
                    self.passed_to_callees.push(*place);
                }
            }
        }

        self.super_visit_rvalue(rvalue, loc);
    }

    fn visit_terminator(&mut self, term: &crate::bc::types::Terminator, loc: Location) {
        if let TerminatorKind::Return(Operand::Place(place)) = term.kind() {
            self.returned.push(*place);
        }
        self.super_visit_terminator(term, loc);
    }
}
