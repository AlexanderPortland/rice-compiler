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

#[allow(clippy::needless_pass_by_value)]
fn escapes(func: &Function, analysis: PointerAnalysis) -> StackAllocate {
    let mut escaping_allocations = ArcIndexSet::new(analysis.alloc_domain());
    let mut places = EscapingPlaces::for_function(func);

    // For all places that might escape...
    for escaping in places.into_iter() {
        // And all of the memory locations they could alias..
        for mem_loc in analysis.could_refer_to(&escaping) {
            // The allocations those memory locations could point to may escape.
            if let Some(allocations) = analysis.points_to().get(&mem_loc) {
                escaping_allocations.union(allocations);
            }
        }
    }

    // Repeatedly keep trying to learn more about the escaping allocations from aliases.
    loop {
        let old_size = escaping_allocations.len();

        for allocation in escaping_allocations.iter().copied().collect::<Vec<_>>() {
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

    let _ = analysis;

    StackAllocate(escaping_allocations, false)
}

#[derive(Default, Debug)]
pub struct EscapingPlaces {
    returned: HashSet<Place>,
    passed_to_callees: HashSet<Place>,
    num_params: usize,
    caller_args: HashSet<Place>,
}

impl EscapingPlaces {
    fn new(num_params: usize) -> Self {
        Self {
            num_params,
            ..Default::default()
        }
    }

    fn for_function(func: &Function) -> Self {
        let mut escape = Self::new(func.num_params);
        escape.visit_function(func);
        escape
    }

    fn into_iter(self) -> impl Iterator<Item = Place> {
        self.returned
            .into_iter()
            .chain(self.passed_to_callees)
            .chain(self.caller_args)
    }
}

impl Visit for EscapingPlaces {
    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        // Arguments to function & method calls escape.
        if let Rvalue::Call { args, .. } | Rvalue::MethodCall { args, .. } = rvalue {
            for arg in args {
                if let Operand::Place(place) = arg {
                    self.passed_to_callees.insert(*place);
                }
            }
        }

        self.super_visit_rvalue(rvalue, loc);
    }

    fn visit_lvalue(&mut self, place: &Place, _loc: Location) {
        /// Assigns to params escape...
        if place.local < self.num_params {
            self.passed_to_callees.insert(*place);
        }
    }

    fn visit_terminator(&mut self, term: &crate::bc::types::Terminator, loc: Location) {
        // Returned places escape.
        if let TerminatorKind::Return(Operand::Place(place)) = term.kind() {
            self.returned.insert(*place);
        }
        self.super_visit_terminator(term, loc);
    }
}
