use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::bc::{
    dataflow::ptr::{
        PointerAnalysis, pointer_analysis,
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

    let mut escapes = escapes(func, analysis);

    escapes.visit_function(func);

    escapes.1
}

#[derive(Debug)]
/// Switch all allocations not in the escaping set to the stack.
pub struct StackAllocate(ArcIndexSet<Allocation>, bool);

impl VisitMut for StackAllocate {
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

fn escapes(func: &Function, analysis: PointerAnalysis) -> StackAllocate {
    let mut escaping_allocations = ArcIndexSet::new(analysis.alloc_domain());
    let mut places = EscapingPlaces::default();
    places.visit_function(func);

    // For all places that might escape...
    for escaping in places.into_iter() {
        // And all of the memory locations they could alias..
        for mem_loc in analysis.could_refer_to(escaping) {
            // The allocations those memory locations could point to may escape.
            if let Some(allocations) = analysis.points_to().get(&mem_loc) {
                escaping_allocations.union(allocations);
            }
        }
    }

    // Repeatedly keep trying to learn more about the escaping allocations from aliases.
    loop {
        let old_size = escaping_allocations.len();

        for allocation in escaping_allocations.iter().cloned().collect::<Vec<_>>() {
            for (ptr, allocs) in analysis.points_to() {
                if let MemLoc::Allocated(alloc, _proj) = ptr
                    && *alloc == allocation
                {
                    escaping_allocations.union(allocs);
                }
            }
        }

        // If we don't learn anything new, we're done.
        if old_size == escaping_allocations.len() {
            break;
        }
    }

    StackAllocate(escaping_allocations, false)
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
        // All params can escape if you write into their allocations.
        // We skip one because x0 is the environment.
        for param_no in 1..func.num_params {
            self.caller_args.push(Place::new(
                LocalIdx::from_usize(param_no),
                vec![],
                Type::bool(),
            ))
        }

        self.super_visit_function(func);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        // Arguments to function & method calls escape.
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
        // Returned places escape.
        if let TerminatorKind::Return(Operand::Place(place)) = term.kind() {
            self.returned.push(*place);
        }
        self.super_visit_terminator(term, loc);
    }
}
