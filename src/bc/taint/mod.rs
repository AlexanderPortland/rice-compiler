use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use crate::{
    bc::{
        dataflow::{
            self, JoinSemiLattice, analyze_to_fixpoint, join_ret_locations,
            ptr::{
                PointerAnalysis,
                types::{AllocProj, MemLoc, PtrPlace},
            },
        },
        taint::{detect::place_could_be_tainted, facts::Facts, loc::all_memlocs},
        types::{
            AllocArgs, AllocKind, BasicBlockIdx, Const, Function, Operand, Place, Program,
            ProjectionElem, Rvalue, Type,
        },
    },
    utils::Symbol,
};
use indexical::ArcIndexSet;
use miette::Result;

mod control;
mod facts;
mod loc;

pub fn check_taints(prog: &Program) -> Result<()> {
    // 1. Get intraprocedural facts
    let facts = facts::intraprocedural_facts(prog);
    for func in prog.functions() {
        println!("{}: {:?}", func.name, facts[&func.name]);
    }

    // 2. Compute interprocedural taint
    let taint = GlobalAnalysis::new(prog, facts).analyze_program();

    Ok(())
}

type CallingContext = Vec<Place>;
type TaintedPlaces = ArcIndexSet<MemLoc>;

struct GlobalAnalysis<'p> {
    prog: &'p Program,

    facts: HashMap<Symbol, Facts>,

    /// For each function, maps the calling context (of tainted inputs)
    /// to the resulting tainted places after execution.
    results: RefCell<HashMap<Symbol, HashMap<CallingContext, TaintedPlaces>>>,
}

impl<'p> GlobalAnalysis<'p> {
    pub fn new(prog: &'p Program, facts: HashMap<Symbol, Facts>) -> Self {
        GlobalAnalysis {
            prog,
            facts,
            results: RefCell::new(HashMap::new()),
        }
    }
}

impl GlobalAnalysis<'_> {
    /// Fully analyzes a program, returning all the resulting information gathered about tainted places.
    pub fn analyze_program(self) -> HashMap<Symbol, HashMap<CallingContext, TaintedPlaces>> {
        self.analyze_function(self.prog.main_function());
        self.results.take()
    }

    fn analyze_function(&self, func: &Function) {
        // let local = LocalAnalysiss
        LocalAnalysis::analyze_call_with_context(func, Vec::new(), &self);
    }
}

struct LocalAnalysis<'f> {
    func: &'f Function,
    calling_context: &'f CallingContext,
    facts: &'f Facts,
    global: &'f GlobalAnalysis<'f>,
}

impl LocalAnalysis<'_> {
    fn analyze_call_with_context(
        call_to: &Function,
        calling_context: CallingContext,
        global: &GlobalAnalysis,
    ) -> TaintedPlaces {
        println!(
            "analyzing call of {} w/ context {:#?}",
            call_to.name, calling_context
        );

        global
            .results
            .borrow_mut()
            .entry(call_to.name)
            .or_default()
            .entry(calling_context)
            .or_insert_with_key(|calling_context| {
                let facts = global
                    .facts
                    .get(&call_to.name)
                    .expect("should have facts entry");
                let local = LocalAnalysis {
                    func: call_to,
                    calling_context,
                    global,
                    facts,
                };

                let all = analyze_to_fixpoint(&local, call_to);
                join_ret_locations(&local, all, call_to)
            })
            .clone()
    }
}

impl JoinSemiLattice for TaintedPlaces {
    fn join(&mut self, other: &Self) -> bool {
        self.union_changed(other)
    }
}

mod detect {
    use std::collections::HashSet;
    use std::collections::VecDeque;

    use crate::bc::taint::PointerAnalysis;
    use crate::bc::taint::TaintedPlaces;
    use crate::bc::types::Operand;
    use crate::bc::types::Place;

    pub fn op_could_be_tainted(
        tainted: &TaintedPlaces,
        ptr: &PointerAnalysis,
    ) -> impl Fn(&Operand) -> bool {
        let place_could_be = place_could_be_tainted(tainted, ptr);
        move |op| {
            if let Operand::Place(p) = op
                && place_could_be(p)
            {
                return true;
            }

            return false;
        }
    }

    pub fn op_could_be_tainted_deep(
        tainted: &TaintedPlaces,
        ptr: &PointerAnalysis,
    ) -> impl Fn(&Operand) -> bool {
        let place_could_be = place_could_be_tainted_deep(tainted, ptr);
        move |op| {
            if let Operand::Place(p) = op
                && place_could_be(p)
            {
                return true;
            }

            return false;
        }
    }

    pub fn place_could_be_tainted_deep(
        tainted: &TaintedPlaces,
        ptr: &PointerAnalysis,
    ) -> impl Fn(&Place) -> bool {
        move |place| {
            let mut visited = HashSet::new();
            let mut to_visit = VecDeque::new();
            to_visit.extend(ptr.could_refer_to(place));

            while let Some(next) = to_visit.pop_front() {
                if visited.contains(&next) {
                    continue;
                }
                if tainted.contains(&next) {
                    return true;
                }

                // to_visit.extend(ptr.po(next));
                todo!();

                visited.insert(next);
            }

            return false;
        }
    }

    pub fn place_could_be_tainted(
        tainted: &TaintedPlaces,
        ptr: &PointerAnalysis,
    ) -> impl Fn(&Place) -> bool {
        move |place| {
            for mem_loc in ptr.could_refer_to(place) {
                if tainted.contains(mem_loc) {
                    return true;
                }
            }

            return false;
        }
    }
}

impl LocalAnalysis<'_> {
    fn output_tainted(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        for memloc in self.facts.ptr().could_refer_to(&statement.place) {
            state.insert(memloc);
        }
    }

    fn output_not_tainted(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        // TODO: (WILL) we can't erase based on an over approximation, right?
        let c = self.facts.ptr().could_refer_to(&statement.place);

        // In the happy case there's only one, we can just remove that...
        assert_eq!(c.len(), 1);
        state.remove(c[0]);
    }

    fn handle_alloc(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        let Rvalue::Alloc { kind, loc, args } = &statement.rvalue else {
            unreachable!();
        };

        match (kind, args) {
            (AllocKind::Tuple, AllocArgs::Lit(literals)) => {
                // For each literal, mark the corresponding memloc as tainted if the operand is tainted
                for (i, lit) in literals.iter().enumerate() {
                    if detect::op_could_be_tainted(&state, self.facts.ptr())(lit) {
                        let new_place =
                            PtrPlace::from(statement.place).extend_projection(AllocProj::Field(i));
                        for memloc in self.facts.ptr().could_refer_to(&new_place) {
                            state.insert(memloc);
                        }
                    }
                }
            }
            (AllocKind::Array, _) => {
                // If anything is tainted, mark the output as tainted
                if statement
                    .rvalue
                    .places()
                    .iter()
                    .any(detect::place_could_be_tainted(&state, self.facts.ptr()))
                {
                    self.output_tainted(state, statement);
                } else {
                }
            }
            _ => todo!(),
        }
    }

    fn track_call(&self, func: &Operand, loc: &super::types::Location) -> Option<Symbol> {
        match func {
            Operand::Func { f, .. } => Some(*f),
            Operand::Place(p) => {
                if p.projection.is_empty()
                    && let local = p.local
                    && let dataflow::r#const::ConstInfo::Closure(closure) =
                        self.facts._const().get(loc).get(local)
                {
                    Some(*closure)
                } else {
                    None
                }
            }
            _ => unreachable!("shouldn't typecheck"),
        }
    }

    /// This means the output is tainted if any reachable input is tainted.
    fn handle_std_call(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        let Rvalue::Call { f, args } = &statement.rvalue else {
            unreachable!();
        };

        let inputs_tainted = args
            .iter()
            .any(detect::op_could_be_tainted(state, self.facts.ptr()));

        todo!()
    }

    fn implicit_flow_for_block(&self, state: &TaintedPlaces, block: &BasicBlockIdx) -> bool {
        self.facts.control().cdep_on(*block).any(|cond_block| {
            // println!("conditional on block {cond_block}");
            let term = &self.func.body.data(cond_block).terminator;
            let places = term.places();
            // println!("terminator {term:?}, places {:?}", places);

            places
                .iter()
                .any(place_could_be_tainted(&state, self.facts.ptr()))
        })
    }

    fn handle_call(
        &self,
        state: &mut TaintedPlaces,
        statement: &super::types::Statement,
        loc: &super::types::Location,
    ) {
        let Rvalue::Call { f, args } = &statement.rvalue else {
            unreachable!();
        };

        let call_to = self
            .track_call(f, loc)
            .expect("should know all calls for now");

        let Some(func) = self.global.prog.find_function(call_to) else {
            return self.handle_std_call(state, statement);
        };
        if call_to == self.func.name {
            todo!("what about recurisve calls??");
        }

        // If we're secure, just mark the output as secure.
        if func.secure() {
            return self.output_tainted(state, statement);
        }

        // Otherwise, recur into the call...
        todo!();
        // let res = LocalAnalysis::analyze_call_with_context(call_to, calling_context, global);

        todo!()
    }
}

impl dataflow::Analysis for LocalAnalysis<'_> {
    type Domain = TaintedPlaces;
    const DIRECTION: dataflow::Direction = dataflow::Direction::Forward;

    fn bottom(&self, func: &super::types::Function) -> Self::Domain {
        assert!(
            !func.secure(),
            "this function shouldn't be analyzed if it's secure"
        );

        let mut initial = TaintedPlaces::new(&self.facts.domains().memloc);

        // TODO: (WILL) this might be an over approximation bc we know EXACTLY what it points to at the start
        for tainted_place in self.calling_context {
            for potential_memloc in self.facts.ptr().could_refer_to(tainted_place) {
                initial.insert(potential_memloc);
            }
        }

        initial
    }

    fn handle_statement(
        &self,
        state: &mut Self::Domain,
        statement: &super::types::Statement,
        loc: super::types::Location,
    ) {
        for s in state.iter() {
            println!("\t{s} is tainted!");
        }

        println!("now analyzing statement {statement}");

        if self.implicit_flow_for_block(state, &loc.block) {
            println!("implicit flow!!");
            return self.output_tainted(state, statement);
        }

        match statement.rvalue {
            Rvalue::Binop { .. }
            | Rvalue::Operand(_)
            | Rvalue::Closure { .. }
            | Rvalue::Cast { .. } => {
                // default case, just taint output based on inputs
                if statement
                    .rvalue
                    .places()
                    .iter()
                    .any(detect::place_could_be_tainted(&state, self.facts.ptr()))
                {
                    for memloc in self.facts.ptr().could_refer_to(&statement.place) {
                        state.insert(memloc);
                    }
                } else {
                    self.output_not_tainted(state, statement);
                }
            }
            Rvalue::Alloc { .. } => self.handle_alloc(state, statement),
            Rvalue::Call { .. } => self.handle_call(state, statement, &loc),
            Rvalue::MethodCall { .. } => todo!(),
        }
    }

    fn handle_terminator(
        &self,
        state: &mut Self::Domain,
        terminator: &super::types::Terminator,
        loc: super::types::Location,
    ) {
        // Don't do anything here...
    }
}
