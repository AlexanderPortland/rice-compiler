use crate::bc::{
    dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
    types::{
        AllocArgs, AllocKind, Binop, Function, Local, Location, Operand, Program, Rvalue, Statement,
    },
    visit::{Visit, VisitMut},
};
use indexical::{ArcIndexSet, ArcIndexVec, RcIndexSet, pointer::PointerFamily, vec::IndexVec};
use itertools::Itertools;

// TODO: elimate dead functions that are never called.

/// Eliminates **any 'dead' statement** that binds a place which isn't used in the rest of the program.
pub fn eliminate_dead_code(func: &mut Function) -> bool {
    // println!("before DCE have func {func}");
    let analysis_result = analyze_to_fixpoint(&DeadCodeAnalyis, func);

    let mut eliminator = DeadCodeElimination::new(&analysis_result);
    eliminator.visit_function(func);
    // println!("after DCE have func {func}");
    eliminator.any_change
}

struct DeadCodeAnalyis;

type IndexSet<T> = ArcIndexSet<T>;

impl JoinSemiLattice for IndexSet<Local> {
    /// Union the two sets
    fn join(&mut self, other: &Self) -> bool {
        self.union_changed(other)
    }
}

impl dataflow::Analysis for DeadCodeAnalyis {
    type Domain = IndexSet<Local>;
    const DIRECTION: dataflow::Direction = dataflow::Direction::Backward;

    fn bottom(&self, func: &Function) -> Self::Domain {
        IndexSet::new(&func.locals)
    }

    fn handle_statement(
        &self,
        state: &mut Self::Domain,
        statement: &crate::bc::types::Statement,
        loc: crate::bc::types::Location,
    ) {
        UpdateLiveSet(state).visit_statement(statement, loc);
    }

    fn handle_terminator(
        &self,
        state: &mut Self::Domain,
        terminator: &crate::bc::types::Terminator,
        loc: crate::bc::types::Location,
    ) {
        UpdateLiveSet(state).visit_terminator(terminator, loc);
    }
}

struct UpdateLiveSet<'z>(&'z mut <DeadCodeAnalyis as Analysis>::Domain);

impl crate::bc::visit::Visit for UpdateLiveSet<'_> {
    fn visit_rvalue_place(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        self.0.insert(place.local);
    }

    fn visit_lvalue(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        if place.projection.is_empty() {
            self.0.remove(place.local);
        } else {
            self.0.insert(place.local);
        }
    }
}

struct DeadCodeElimination<'z> {
    any_change: bool,
    dead_locals: &'z ArcIndexVec<Location, IndexSet<Local>>,
}

#[derive(Default)]
// Checks for alloc use and divisions (things that could fail or have side effects at runtime)
struct AnyAllocUse(bool);

impl Visit for AnyAllocUse {
    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        if matches!(rvalue, Rvalue::Binop { op: Binop::Div, .. }) {
            self.0 |= true;
        }

        self.super_visit_rvalue(rvalue, loc);
    }
    fn visit_rvalue_place(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        if !place.projection.is_empty() {
            self.0 |= true;
        }
    }

    fn visit_lvalue(&mut self, place: &crate::bc::types::Place, _loc: Location) {
        if !place.projection.is_empty() {
            self.0 |= true;
        }
    }
}

impl<'z> DeadCodeElimination<'z> {
    pub fn new(dead_locals: &'z ArcIndexVec<Location, IndexSet<Local>>) -> Self {
        Self {
            any_change: false,
            dead_locals,
        }
    }

    /// Checks if an rvalue could possibly have a sideffect beyond what it returns.
    ///
    /// Currently checks for any function or method calls, and any array indexing that could fail at runtime.
    fn has_effect(num_params: usize, stmt: &Statement, loc: Location) -> bool {
        // All calls and copy arrays can have side effects. (Copy arrays can be 0).
        if matches!(
            stmt.rvalue,
            Rvalue::MethodCall { .. }
                | Rvalue::Call { .. }
                | Rvalue::Alloc {
                    args: AllocArgs::Repeated { .. },
                    ..
                }
        ) {
            return true;
        }

        // Check if we access an element of an array.
        // This could fail at runtime, so should not be optimized away
        let mut has_arrays = AnyAllocUse::default();
        has_arrays.visit_statement(stmt, loc);
        if has_arrays.0 {
            return true;
        }

        // Check if we modify a heap allocation passed into the function.
        if !stmt.place.projection.is_empty() && stmt.place.local <= num_params {
            return true;
        }

        false
    }
}

impl VisitMut for DeadCodeElimination<'_> {
    fn visit_function(&mut self, func: &mut Function) {
        let mut change_here = false;
        let body = &mut func.body;
        for block in body.blocks().collect_vec() {
            let (data, block) = (body.data_mut(block), block);
            let mut instr = 0;
            data.statements.retain(|stmt| {
                let loc = Location { block, instr };
                let is_used = self.dead_locals.get(loc).contains(stmt.place.local);
                instr += 1;

                if !is_used && !Self::has_effect(func.num_params, stmt, loc) {
                    // REMOVE
                    self.any_change |= true;
                    change_here |= true;
                    false
                } else {
                    true
                }
            });
        }
        if change_here {
            body.regenerate_domain();
        }
    }
}
