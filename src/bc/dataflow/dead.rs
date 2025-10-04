use indexical::{ArcIndexSet, ArcIndexVec, RcIndexSet, pointer::PointerFamily, vec::IndexVec};
use itertools::Itertools;
use wasmtime::StoreContextMut;

use crate::bc::{
    dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
    types::{Function, Local, Location, Operand, Rvalue, Statement},
    visit::{Visit, VisitMut},
};

pub fn eliminate_dead_code(func: &mut Function) -> bool {
    // println!("func body {:?}", func.body);
    let analysis_result = analyze_to_fixpoint(&DeadCodeAnalyis, func);

    // for loc in func.body.locations().iter() {
    //     println!(
    //         "location {loc:?} has domain {:?}",
    //         analysis_result
    //             .get(loc)
    //             .iter()
    //             .map(|loc| { format!("{:?}", func.locals.index(loc)) })
    //             .join(",")
    //     )
    // }

    let mut eliminator = DeadCodeElimination::new(&analysis_result);
    eliminator.visit_function(func);
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
        }
    }
}

struct DeadCodeElimination<'z> {
    any_change: bool,
    dead_locals: &'z ArcIndexVec<Location, IndexSet<Local>>,
}

impl<'z> DeadCodeElimination<'z> {
    pub fn new(dead_locals: &'z ArcIndexVec<Location, IndexSet<Local>>) -> Self {
        Self {
            any_change: false,
            dead_locals,
        }
    }

    fn has_side_effects(stmt: &Statement) -> bool {
        matches!(
            stmt.rvalue,
            Rvalue::Closure { .. } | Rvalue::MethodCall { .. }
        )
    }
}

impl VisitMut for DeadCodeElimination<'_> {
    fn visit_body(&mut self, body: &mut crate::bc::types::Body) {
        let mut change_here = false;
        for block in body.blocks().collect_vec() {
            let (data, block) = (body.data_mut(block), block);
            let mut instr = 0;
            data.statements.retain(|stmt| {
                let is_used = self
                    .dead_locals
                    .get(Location { block, instr })
                    .contains(stmt.place.local);
                instr += 1;
                let has_sideffect = DeadCodeElimination::has_side_effects(stmt);
                // println!(
                //     "stmt {stmt} @ {instr} has is_dead {is_used}, has_sideffect {}",
                //     has_sideffect
                // );
                if !is_used && !has_sideffect {
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
