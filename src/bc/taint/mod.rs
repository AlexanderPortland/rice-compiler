use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    ast::types::Span,
    bc::{
        dataflow::{
            self, JoinSemiLattice, analyze_to_fixpoint, join_ret_locations,
            ptr::{
                PointerAnalysis,
                types::{AllocProj, MemLoc, PtrPlace},
            },
            ret_places,
        },
        taint::{
            detect::{op_could_be_tainted_deep, place_could_be_tainted},
            facts::Facts,
            loc::all_memlocs,
        },
        types::{
            AllocArgs, AllocKind, BasicBlockIdx, Const, Function, Local, LocalIdx, Operand, Place,
            Program, ProjectionElem, Rvalue, Statement, Type, TypeKind,
        },
    },
    utils::{Symbol, sym},
};
use indexical::{ArcIndexSet, IndexedDomain, set::IndexSet};
use itertools::Itertools;
use miette::{Diagnostic, Result, bail};
use thiserror::Error;

mod control;
mod facts;
mod loc;

#[derive(Debug, Diagnostic, Error)]
enum IllegalCall {
    #[error("illegal call to function `{sym}` with tainted values")]
    TaintedArgs {
        sym: Symbol,
        #[label]
        span: Span,
    },
    #[error("illegal call to function `{to_sym}` control dependent on tainted values")]
    ImplicitFlow {
        #[label("from here")]
        from_span: Span,
        from_place: Place,
        to_sym: Symbol,
        #[label("to here")]
        to_span: Span,
    },
}

impl IllegalCall {
    fn tainted_args(sym: Symbol, span: Span) -> Self {
        IllegalCall::TaintedArgs { sym, span }
    }
    fn implicit_flow(from: (Place, Span), to: (Symbol, Span)) -> Self {
        IllegalCall::ImplicitFlow {
            from_span: from.1,
            from_place: from.0,
            to_sym: to.0,
            to_span: to.1,
        }
    }
}

pub fn check_taints(prog: &Program) -> Result<()> {
    // 1. Get intraprocedural facts
    let facts = facts::intraprocedural_facts(prog);
    for func in prog.functions() {
        // println!("{}: {:?}", func.name, facts[&func.name]);
    }

    // 2. Compute interprocedural taint
    let mut taint = GlobalAnalysis::new(prog, facts).analyze_program();
    if let Some(first_err) = taint.pop() {
        bail!(first_err);
    }

    Ok(())
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
struct CallingContext {
    all: bimap::BiBTreeMap<PtrPlace, CalleePlace>,
    tainted: Vec<CalleePlace>,
}

impl CallingContext {
    pub fn empty() -> Self {
        CallingContext {
            all: bimap::BiBTreeMap::new(),
            tainted: Vec::new(),
        }
    }
}

type CallingContextTainted = Vec<CalleePlace>;
type TaintedPlaces = ArcIndexSet<MemLoc>;

struct GlobalAnalysis<'p> {
    prog: &'p Program,

    facts: HashMap<Symbol, Facts>,

    /// For each function, maps the calling context (of tainted inputs)
    /// to the resulting tainted places after execution.
    results: RefCell<HashMap<Symbol, HashMap<CallingContextTainted, TaintedPlaces>>>,

    illegal_calls: RefCell<Vec<IllegalCall>>,
}

impl<'p> GlobalAnalysis<'p> {
    pub fn new(prog: &'p Program, facts: HashMap<Symbol, Facts>) -> Self {
        GlobalAnalysis {
            prog,
            facts,
            results: RefCell::new(HashMap::new()),
            illegal_calls: RefCell::new(Vec::new()),
        }
    }
}

impl GlobalAnalysis<'_> {
    /// Fully analyzes a program, returning all the resulting information gathered about tainted places.
    pub fn analyze_program(self) -> Vec<IllegalCall> {
        self.analyze_function(self.prog.main_function());
        self.illegal_calls.take()
    }

    fn analyze_function(&self, func: &Function) {
        // let local = LocalAnalysiss
        LocalAnalysis::analyze_call_with_context(func, CallingContext::empty(), &self);
    }
}

struct LocalAnalysis<'f> {
    func: &'f Function,
    initial_tainted: &'f CallingContextTainted,
    facts: &'f Facts,
    global: &'f GlobalAnalysis<'f>,
}

impl LocalAnalysis<'_> {
    fn analyze_call_with_context(
        call_to: &Function,
        calling_context: CallingContext,
        global: &GlobalAnalysis,
    ) -> TaintedPlaces {
        let facts = global
            .facts
            .get(&call_to.name)
            .expect("should have facts entry");

        assert!(global.results.try_borrow_mut().is_ok());

        // initialize fn calling ctxts if not already
        if global.results.borrow_mut().get(&call_to.name).is_none() {
            assert_eq!(
                global
                    .results
                    .borrow_mut()
                    .insert(call_to.name, HashMap::new()),
                None
            );
        }

        if let Some(s) = global
            .results
            .borrow_mut()
            .get(&call_to.name)
            .expect("initialized above")
            .get(&calling_context.tainted)
        {
            return s.clone();
        }

        let local = LocalAnalysis {
            func: call_to,
            initial_tainted: &calling_context.tainted,
            global,
            facts,
        };

        let all = analyze_to_fixpoint(&local, call_to);
        let ret = join_ret_locations(&local, all, call_to);

        assert_eq!(
            global
                .results
                .borrow_mut()
                .get_mut(&call_to.name)
                .expect("initialized above")
                .insert(calling_context.tainted, ret.clone()),
            None
        );

        ret
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

    use crate::bc::dataflow::ptr::types::PtrPlace;
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
            ptr.reachable_memlocs(place)
                .iter()
                .any(|loc| tainted.contains(loc))
        }
    }

    pub fn place_could_be_tainted<T: Into<PtrPlace> + Copy>(
        tainted: &TaintedPlaces,
        ptr: &PointerAnalysis,
    ) -> impl Fn(&T) -> bool {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
struct CalleePlace(PtrPlace);

impl CalleePlace {
    pub fn extend_projection(self, proj: AllocProj) -> Self {
        CalleePlace(self.0.extend_projection(proj))
    }
}

fn map_arg_place(
    ptr: &PointerAnalysis,
    arg_place: &PtrPlace,
    to_place: CalleePlace,
    ty: &Type,
) -> bimap::BiMap<PtrPlace, CalleePlace> {
    match ty.kind() {
        TypeKind::Array(inner) => {
            // okay so we have
            [(*arg_place, to_place)]
                .into_iter()
                .chain(
                    map_arg_place(
                        ptr,
                        &arg_place.extend_projection(AllocProj::Index),
                        to_place.extend_projection(AllocProj::Index),
                        inner,
                    )
                    .into_iter(),
                )
                .collect()
        }
        TypeKind::Tuple(inners) => {
            // okay so we have smth along the line of (x1, x2) passed in to arg_place
            // we want to say, for each
            [(*arg_place, to_place)]
                .into_iter()
                .chain(inners.iter().enumerate().flat_map(|(i, inner_ty)| {
                    map_arg_place(
                        ptr,
                        &arg_place.extend_projection(AllocProj::Field(i)),
                        to_place.extend_projection(AllocProj::Field(i)),
                        inner_ty,
                    )
                    .into_iter()
                }))
                .collect()
        }
        TypeKind::Struct(inners) => {
            todo!()
        }
        _ => [(*arg_place, to_place)].into_iter().collect(),
    }
}

impl LocalAnalysis<'_> {
    fn output_tainted(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        for memloc in self.facts.ptr().could_refer_to(&statement.place) {
            state.insert(memloc);
        }
    }

    fn output_proj_tainted(
        &self,
        state: &mut TaintedPlaces,
        statement: &super::types::Statement,
        proj: AllocProj,
    ) {
        for memloc in self
            .facts
            .ptr()
            .could_refer_to(&PtrPlace::from(statement.place).extend_projection(proj))
        {
            // println!(
            //     "inserting memloc {memloc} to {} from {}",
            //     self.func.name,
            //     PtrPlace::from(statement.place).extend_projection(proj)
            // );
            // println!(
            //     "{}: domain is {:?}",
            //     self.func.name,
            //     state.indices().collect::<Vec<_>>()
            // );
            // println!("{}: inserting memloc {memloc}", self.func.name);
            state.insert(memloc);
            // println!("{}: done inserting memloc {memloc}", self.func.name);
        }
    }

    fn output_not_tainted(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        // TODO: (WILL) we can't erase based on an over approximation, right?
        let c = self.facts.ptr().could_refer_to(&statement.place);

        // In the happy case there's only one, we can just remove that...
        assert_eq!(c.len(), 1);
        // println!("{:?} is NEWLY NOT tainted!", c[0]);
        state.remove(c[0]);
    }

    fn handle_alloc(
        &self,
        state: &mut TaintedPlaces,
        statement: &super::types::Statement,
        implicit_flow: Option<(Place, Span)>,
    ) {
        let Rvalue::Alloc { kind, loc, args } = &statement.rvalue else {
            unreachable!();
        };

        match (kind, args) {
            (AllocKind::Tuple, AllocArgs::Lit(literals))
            | (AllocKind::Struct, AllocArgs::Lit(literals)) => {
                // For each literal, mark the corresponding memloc as tainted if the operand is tainted
                for (i, lit) in literals.iter().enumerate() {
                    if detect::op_could_be_tainted(&state, self.facts.ptr())(lit)
                        || implicit_flow.is_some()
                    {
                        self.output_proj_tainted(state, statement, AllocProj::Field(i));
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
                    || implicit_flow.is_some()
                {
                    self.output_proj_tainted(state, statement, AllocProj::Index);
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
    fn handle_std_call(
        &self,
        state: &mut TaintedPlaces,
        statement: &super::types::Statement,
        sym: &Symbol,
        implicit_flow: Option<(Place, Span)>,
    ) {
        let Rvalue::Call { f, args } = &statement.rvalue else {
            unreachable!();
        };

        // Println call!
        if *sym == crate::utils::sym("println") {
            if args
                .iter()
                .any(|op| op_could_be_tainted_deep(&state, self.facts.ptr())(op))
            {
                self.global
                    .illegal_calls
                    .borrow_mut()
                    .push(IllegalCall::tainted_args(*sym, statement.span));
            } else if let Some(implicit_flow) = implicit_flow {
                self.global
                    .illegal_calls
                    .borrow_mut()
                    .push(IllegalCall::implicit_flow(
                        implicit_flow,
                        (*sym, statement.span),
                    ));
            }
        }

        // Check if any of our inputs could be deeply tainted.
        if args
            .iter()
            .any(detect::op_could_be_tainted_deep(state, self.facts.ptr()))
        {
            self.output_tainted(state, statement);
        } else {
            self.output_not_tainted(state, statement);
        }
    }

    fn implicit_flow_for_block(
        &self,
        state: &TaintedPlaces,
        block: &BasicBlockIdx,
    ) -> Option<(Place, Span)> {
        self.facts
            .control()
            .cdep_on(*block)
            .filter_map(|cond_block| {
                // println!("conditional on block {cond_block}");
                let term = &self.func.body.data(cond_block).terminator;
                let places = term.places();
                // println!("terminator {term:?}, places {:?}", places);

                if let Some(place) = places
                    .iter()
                    .find(|a| place_could_be_tainted(&state, self.facts.ptr())(*a))
                {
                    Some((*place, term.span))
                } else {
                    None
                }
            })
            .next()
    }

    fn build_calling_ctxt_for(
        &self,
        state: &TaintedPlaces,
        statement: &super::types::Statement,
        sym: &Symbol,
        args: &[Operand],
    ) -> CallingContext {
        let func = self
            .global
            .prog
            .find_function(sym)
            .expect("invalid function {sym:?}");

        let mut ctxt = CallingContext::empty();
        for ((arg_idx, ty), arg) in func.params().skip(1).zip_eq(args.iter()) {
            if let Operand::Place(p) = arg {
                let new_info = map_arg_place(
                    self.facts.ptr(),
                    &(*p).into(),
                    CalleePlace(Place::new(arg_idx, vec![], ty).into()),
                    &ty,
                );
                ctxt.all.extend(new_info);
            }
        }

        // For all caller places that are tainted, mark the corresponding callee place as tainted
        for (caller_place, callee_place) in &ctxt.all {
            if place_could_be_tainted(state, self.facts.ptr())(caller_place) {
                ctxt.tainted.push(*callee_place);
            }
        }

        ctxt
    }

    fn handle_unknown_call(&self, state: &mut TaintedPlaces, statement: &super::types::Statement) {
        let Rvalue::Call { f, args } = &statement.rvalue else {
            unreachable!();
        };

        for a in args {
            if let Operand::Place(p) = a {
                for (sub_place, _) in map_arg_place(
                    self.facts.ptr(),
                    &(*p).into(),
                    CalleePlace((*p).into()),
                    &a.ty(),
                ) {
                    for loc in self.facts.ptr().could_refer_to(&sub_place) {
                        state.insert(loc);
                    }
                }
            }
        }

        self.output_tainted(state, statement);
        // TODO: I think we need to deeply handle this here...
    }

    fn handle_call(
        &self,
        state: &mut TaintedPlaces,
        statement: &super::types::Statement,
        loc: &super::types::Location,
        implicit_flow: Option<(Place, Span)>,
    ) {
        let Rvalue::Call { f, args } = &statement.rvalue else {
            unreachable!();
        };

        let Some(call_to) = self.track_call(f, loc) else {
            return self.handle_unknown_call(state, statement);
        };

        let Some(func) = self.global.prog.find_function(call_to) else {
            return self.handle_std_call(state, statement, &call_to, implicit_flow);
        };
        if call_to == self.func.name {
            todo!("what about recurisve calls??");
        }

        // If we're secure, just mark the output as secure.
        if func.secure() {
            return self.output_tainted(state, statement);
        }

        let calling_context = self.build_calling_ctxt_for(state, statement, &call_to, args);
        let callee_ptr = self
            .global
            .facts
            .get(&func.name)
            .expect("should have")
            .ptr();

        let res =
            LocalAnalysis::analyze_call_with_context(func, calling_context.clone(), self.global);

        let ret_places = ret_places(func).collect::<Vec<_>>();
        assert_eq!(ret_places.len(), 1);
        let ret_place = ret_places.first().expect("just checked this has a value");
        if place_could_be_tainted(&res, callee_ptr)(&ret_place.1) {
            self.output_tainted(state, statement);
        } else {
            self.output_not_tainted(state, statement);
        }

        for (caller_place, callee_place) in &calling_context.all {
            // if the callee place could be tainted (and has a projection making it not pass by value),
            // we mark the corresponding caller place as tainted
            if place_could_be_tainted(&res, callee_ptr)(&callee_place.0)
                && !caller_place.projection.is_empty()
            {
                for loc in self.facts.ptr().could_refer_to(caller_place) {
                    state.insert(loc);
                }
            }
        }

        for i in res.iter() {
            // println!("{i} is tainted on return!");
        }

        // Otherwise, recur into the call...
        if implicit_flow.is_some() {
            todo!("not sure what to do in this case...");
        }
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
        for CalleePlace(tainted_place) in self.initial_tainted {
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
            // println!("\t{s} is tainted!");
        }

        // println!("analyzing statment {statement}");

        let implicit_flow = self.implicit_flow_for_block(state, &loc.block);

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
                    || implicit_flow.is_some()
                {
                    for memloc in self.facts.ptr().could_refer_to(&statement.place) {
                        state.insert(memloc);
                    }
                } else {
                    self.output_not_tainted(state, statement);
                }
            }
            Rvalue::Alloc { .. } => self.handle_alloc(state, statement, implicit_flow),
            Rvalue::Call { .. } => self.handle_call(state, statement, &loc, implicit_flow),
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
