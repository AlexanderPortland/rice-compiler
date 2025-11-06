use core::panic;
use itertools::Itertools;
use std::{
    collections::{HashMap, VecDeque, vec_deque},
    hash::{DefaultHasher, RandomState},
    sync::Arc,
};
use thiserror::Error;

use crate::{
    ast::types::Span,
    bc::types::{
        AllocArgs, BasicBlock, BasicBlockIdx, Binop, Const, Function, Local, LocalIdx, Location,
        Operand, Place, Program, ProjectionElem, Rvalue, Statement, Terminator, TerminatorKind,
        Type, TypeKind,
    },
    utils::{Symbol, sym},
};
use either::Either::{Left, Right};
use miette::{Diagnostic, Result};
use smallvec::SmallVec;
use z3::{SatResult, ast as symb};

mod step;

pub struct SymexOptions {
    pub max_steps: usize,
}

pub fn symex_func(func: &Function, in_prog: &Program, opts: &SymexOptions) -> Result<()> {
    // println!("[*] symex for func {}", func.name);
    let mut configs = VecDeque::from(vec![SymexConfig::entry(func, in_prog)]);
    // println!("initial configs {:#?}", configs);

    while let Some(step_next) = configs.pop_front() {
        if step_next.should_continue(opts) {
            // println!("config {:#?} will be stepped", step_next);
            configs.extend(step_next.step()?);
        } else {
            // println!("config {:#?} has been CANCELLED", step_next);
        }
    }
    Ok(())
}

#[derive(Debug, Default, Clone)]
struct Heap(Vec<symb::Dynamic>);

// type HeapPtrType = z3::Sort::new

pub fn sort_from_ty(ty: Type) -> z3::Sort {
    match ty.kind() {
        TypeKind::Array(_) => z3::Sort::int(),
        TypeKind::Tuple(_) | TypeKind::Struct(_) => {
            todo!("dont have to handle any of these yet")
        }
        TypeKind::Int => z3::Sort::int(),
        TypeKind::Bool => z3::Sort::bool(),
        TypeKind::Float => z3::Sort::float32(),
        TypeKind::Func { .. } | TypeKind::Self_ | TypeKind::Interface(_) => {
            todo!("who the hell knows")
        }
        TypeKind::Hole(_) => unreachable!("holes should be removed during typechecking"),
        TypeKind::String => todo!("should handle strings, but being lazy for now"),
    }
}

impl Heap {
    pub fn next_id(&self) -> usize {
        self.0.len()
    }

    pub fn insert_el(&mut self, el: impl Into<symb::Dynamic>) -> symb::Dynamic {
        self.0.push(el.into());
        symb::Int::from_u64((self.0.len() - 1).try_into().unwrap()).into()
    }

    pub fn sym_var(&mut self, l: LocalIdx, ty: Type) -> symb::Dynamic {
        let name = sym_var_name(l);
        match ty.kind() {
            TypeKind::Array(inner) => {
                // get new unique heap id
                let symb_arr = symb::Array::fresh_const(
                    &("A".to_owned() + &sym_var_name(l)),
                    &z3::Sort::int(),
                    &sort_from_ty(*inner),
                );
                self.insert_el(symb_arr)
            }
            TypeKind::Tuple(_) | TypeKind::Struct(_) | TypeKind::Func { .. } => {
                todo!("dont have to handle any of these yet")
            }
            TypeKind::Bool => symb::Bool::fresh_const(&name).into(),
            TypeKind::Int => symb::Int::fresh_const(&name).into(),
            TypeKind::String => todo!("should handle strings, but being lazy for now"),
            TypeKind::Hole(_) => unreachable!("holes should be removed during typechecking"),
            TypeKind::Float => symb::Float::fresh_const_float32(&name).into(),
            TypeKind::Self_ | TypeKind::Interface(_) => todo!("don't have to handle these ever"),
        }
    }
}

#[derive(Clone)]
struct SymexConfig<'f> {
    /// The path taken by this config.
    path: symb::Bool,
    /// The number of symbolic steps this config has taken.
    steps: usize,
    /// The function
    curr_func: &'f Function,

    // TODO: simplify curr_func, in_prog, and stack into this logic, making things cleaner.
    call_stack: Vec<(&'f Function, Location, HashMap<LocalIdx, StackVal>)>,

    heap: Heap,

    in_prog: &'f Program,

    inputs: HashMap<LocalIdx, symb::Dynamic>,
    /// The location of the instruction to execute next.
    next_instr: Location,
    /// Our 'stack' used to keep track of the symbolic values of local variables.
    stack: HashMap<LocalIdx, StackVal>,
}

#[derive(Debug, Clone)]
pub enum StackVal {
    KnownClosure(Symbol),
    SymbVal(symb::Dynamic),
}

impl<T: Into<symb::Dynamic>> From<T> for StackVal {
    fn from(value: T) -> Self {
        let t: symb::Dynamic = value.into();
        StackVal::SymbVal(t)
    }
}

impl StackVal {
    pub fn as_expect_val(&self) -> &symb::Dynamic {
        let Self::SymbVal(val) = self else {
            panic!("not a val");
        };
        val
    }

    pub fn expect_val(self) -> symb::Dynamic {
        let Self::SymbVal(val) = self else {
            panic!("not a val");
        };
        val
    }
}

#[derive(Diagnostic, Error, Debug)]
#[error("potential assertion failure")]
struct SymexError {
    #[label("here with inputs {problem_inputs}")]
    span: Span,

    problem_inputs: String,
}

impl std::fmt::Debug for SymexConfig<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymexConfig")
            .field("path", &self.path)
            .field("steps", &self.steps)
            .field("next_instr", &self.next_instr)
            .field("stack", &self.stack)
            .finish()
    }
}

pub fn sym_var_name(l: LocalIdx) -> String {
    format!("{l}")
}

pub fn symb_const(c: &Const) -> StackVal {
    match c {
        Const::Bool(b) => symb::Bool::from_bool(*b).into(),
        Const::Int(i) => symb::Int::from_i64(*i as i64).into(),
        Const::Float(f) => symb::Float::from_f32(f.into_inner()).into(),
        Const::String(_) => todo!("not sure how to handle strings yet"),
    }
}

impl<'f> SymexConfig<'f> {
    /// Constructs a config for right after entry to a function.
    pub fn entry(func: &'f Function, in_prog: &'f Program) -> Self {
        let mut stack = HashMap::new();
        let mut inputs = HashMap::new();
        let mut heap = Heap::default();
        for (local, ty) in func.params().skip(1) {
            let val = heap.sym_var(local, ty);
            inputs.insert(local, val.clone());
            stack.insert(local, val.into());
        }

        SymexConfig {
            path: symb::Bool::from_bool(true),
            steps: 0,
            curr_func: func,
            inputs,
            in_prog,
            heap,
            call_stack: Vec::new(),
            next_instr: func.body.entry_loc(),
            stack,
        }
    }

    pub fn assume(mut self, cond: symb::Bool) -> Self {
        self.path = symb::Bool::and(&[self.path, cond]);
        self
    }

    pub fn goto_block(mut self, block: &BasicBlockIdx) -> Self {
        self.next_instr = Location {
            block: *block,
            instr: 0,
        };
        self
    }

    pub fn symb_place(&self, p: &Place) -> StackVal {
        let mut proj = p.projection.clone();
        let mut current_val = self.stack[&p.local].clone();

        while let Some(proj) = proj.pop() {
            current_val = self.proj(current_val, proj);
        }

        current_val
    }

    fn proj(&self, val: StackVal, proj: ProjectionElem) -> StackVal {
        let ptr_i = val
            .expect_val()
            .as_int()
            .expect("ptr that is projected on should be an int index into the stack")
            .as_u64()
            .expect("should be const too");

        let alloc = &self.heap.0[ptr_i as usize];

        match proj {
            ProjectionElem::Field { index, ty } => {
                todo!()
            }
            ProjectionElem::Index { index, .. } => {
                let index = self
                    .symb_operand(&index)
                    .expect_val()
                    .as_int()
                    .expect("index should be int");

                let arr = alloc.as_array().expect("should be array");
                StackVal::SymbVal(arr.select(&index))
            }
        }
    }

    pub fn symb_operand(&self, op: &Operand) -> StackVal {
        match op {
            Operand::Const(c) => symb_const(c),
            Operand::Place(p) => self.symb_place(p),
            Operand::Func { f, .. } => StackVal::KnownClosure(*f),
        }
    }

    pub fn symb_binop(&self, op: &Binop, left: &Operand, right: &Operand) -> StackVal {
        let left_val = self.symb_operand(left).expect_val();
        let right_val = self.symb_operand(right).expect_val();

        macro_rules! commute_binop {
            ($expect: ident, $z3_ty: ident, $z3_fun: ident) => {
                symb::$z3_ty::$z3_fun(&[
                    left_val.$expect().expect("should be an int"),
                    right_val.$expect().expect("should be an int"),
                ])
                .into()
            };
        }

        macro_rules! dir_binop {
            ($expect: ident, $z3_fun: ident) => {
                left_val
                    .$expect()
                    .expect("should be a bool")
                    .$z3_fun(right_val.$expect().expect("should be a bool"))
                    .into()
            };
        }

        match (op, left.ty().kind()) {
            (Binop::Add, TypeKind::Int) => commute_binop!(as_int, Int, add),
            (Binop::Sub, TypeKind::Int) => commute_binop!(as_int, Int, sub),
            (Binop::Mul, TypeKind::Int) => commute_binop!(as_int, Int, mul),
            (Binop::And, TypeKind::Bool) => commute_binop!(as_bool, Bool, and),
            (Binop::Eq, TypeKind::Bool) => dir_binop!(as_bool, eq),
            (Binop::Eq, TypeKind::Int) => dir_binop!(as_int, eq),
            (Binop::Div, TypeKind::Int) => dir_binop!(as_int, div),
            (Binop::Gt, TypeKind::Int) => dir_binop!(as_int, gt),
            (Binop::Lt, TypeKind::Int) => dir_binop!(as_int, lt),
            (Binop::Ge, TypeKind::Int) => dir_binop!(as_int, ge),
            (Binop::Le, TypeKind::Int) => dir_binop!(as_int, le),
            _ => todo!(),
        }
    }

    fn known_closure(&self, op: &Operand) -> Option<Symbol> {
        if let StackVal::KnownClosure(c) = self.symb_operand(op) {
            Some(c)
        } else {
            None
        }
    }

    fn model_string(&self, model: z3::Model) -> String {
        let val_map = self
            .curr_func
            .params()
            .skip(1)
            .map(|(local, _ty)| {
                let val = model
                    .eval(self.inputs.get(&local).expect("should have value"), false)
                    .unwrap();
                format!("x{local:?} -> {val}")
            })
            .join(",");
        format!("[{val_map}]")
    }

    fn handle_assert(&self, on: &Operand, span: Span) -> Result<()> {
        // println!("handling assert on {on:?}");
        let cond = self
            .symb_operand(on)
            .expect_val()
            .as_bool()
            .expect("condition should be bool");

        let solver = z3::Solver::new();
        solver.assert(&self.path);
        solver.assert(cond.not());

        let solve = matches!(solver.check(), SatResult::Sat);

        let problem_inputs = solver
            .get_model()
            .map(|model| self.model_string(model))
            .unwrap_or_default();

        miette::ensure!(
            !solve,
            SymexError {
                // model: solver.get_model(),
                span,
                problem_inputs
            }
        );
        Ok(())
    }

    pub fn call(mut self, f: Symbol, args: &[Operand]) -> Self {
        let Some(new_func) = self.in_prog.find_function(f) else {
            panic!("unknown call to {f}");
        };

        // let params = new_func.params().skip(1).enumerate().collect::<Vec<_>>();

        // panic!("args to {f:?} are {args:?}, params are {params:?}");

        let mut new_stack = HashMap::new();
        for (i, (local, ty)) in new_func.params().skip(1).enumerate() {
            new_stack.insert(local, self.symb_operand(&args[i]));
        }

        // panic!("args for {f:?} is {new_stack:?}");

        // Save where to return to on the call stack
        let ret_to = (
            self.curr_func,
            self.next_instr,
            // This implicitly empties our current stack
            std::mem::take(&mut self.stack),
        );
        self.call_stack.push(ret_to);
        self.stack = new_stack;

        self.curr_func = new_func;
        self.next_instr = new_func.body.entry_loc();

        self
    }

    fn ret_place(func: &'f Function, loc: Location) -> Place {
        let ret_instr = func
            .body
            .instr(loc)
            .left()
            .expect("should be a statement at ret_loc");
        let Rvalue::Call { f, args } = &ret_instr.rvalue else {
            panic!("not a call rvalue at ret loc");
        };
        ret_instr.place
    }

    pub fn ret(mut self, op: &Operand) -> Option<Self> {
        let Some((ret_func, ret_loc, ret_stack)) = self.call_stack.pop() else {
            // Otherwise, we're returning from the main symex function, and don't have to do anything.
            return None;
        };
        let ret_val = self.symb_operand(op);
        self.curr_func = ret_func;
        self.next_instr = ret_loc;
        self.stack = ret_stack;
        self.inc_instr();
        self.assign_place(&Self::ret_place(ret_func, ret_loc), ret_val);

        Some(self)
    }

    /// Returns the value, and any new conditions added to the path if any
    pub fn symb_rvalue(&self, rv: &Rvalue) -> Result<(Option<StackVal>, Option<symb::Bool>)> {
        match rv {
            Rvalue::Operand(op) => Ok((Some(self.symb_operand(op).into()), None)),
            Rvalue::Binop { op, left, right } => Ok((Some(self.symb_binop(op, left, right)), None)),
            Rvalue::Closure { f, env } => {
                if env.is_empty() {
                    Ok((Some(StackVal::KnownClosure(*f)), None))
                } else {
                    panic!("closures w symex");
                }
            }
            Rvalue::Call { .. } => unreachable!("handled in step_stmt"),
            e => todo!("{e} nyi"),
        }
    }

    pub fn assign_place(&mut self, p: &Place, val: StackVal) {
        if p.projection.is_empty() {
            // add to stack
            self.stack.insert(p.local, val);
        } else {
            panic!("ahhh dont have heap shit yet");
        }
    }

    pub fn inc_instr(&mut self) {
        let mut next = self.curr_func.body.successors(self.next_instr);
        assert_eq!(next.len(), 1);
        self.next_instr = next.remove(0);
    }

    pub fn step_stmt(mut self, stmt: &'f Statement) -> Result<Self> {
        if let Rvalue::Call { f, args } = &stmt.rvalue {
            let to = self.known_closure(f).expect("should know all closures");
            if to == sym("assert") {
                self.handle_assert(
                    args.first()
                        .expect("assert should have at least one argument"),
                    stmt.span,
                )?;
                return Ok(self);
            } else {
                return Ok(self.call(to, args));
            }
        }

        if !matches!(&stmt.rvalue, Rvalue::Alloc {
            args: AllocArgs::Lit(e), ..
        } if e.is_empty())
        {
            let (new_val, path_ext) = self.symb_rvalue(&stmt.rvalue)?;
            if let Some(path_ext) = path_ext {
                self = self.assume(path_ext);
            }

            if let Some(new_val) = new_val {
                self.assign_place(&stmt.place, new_val);
            }
        }

        self.inc_instr();
        Ok(self)
    }

    pub fn step_term(self, term: &'f Terminator) -> Result<SmallVec<[Self; 2]>> {
        match term.kind() {
            TerminatorKind::Jump(j) => {
                // just set our next instruction to be there
                Ok(SmallVec::from_elem(self.goto_block(j), 1))
            }
            TerminatorKind::Return(op) => match self.ret(op) {
                Some(more) => Ok(SmallVec::from_iter(std::iter::once(more))),
                None => Ok(SmallVec::new()),
            },
            TerminatorKind::CondJump {
                cond,
                true_,
                false_,
            } => {
                let symb_cond = self
                    .symb_operand(cond)
                    .expect_val()
                    .as_bool()
                    .expect("condition should be bool");

                let false_branch = self.clone().assume(symb_cond.not()).goto_block(false_);
                let true_branch = self.assume(symb_cond).goto_block(true_);
                Ok(SmallVec::from_buf([true_branch, false_branch]))
            }
        }
    }
}

impl SymexConfig<'_> {
    pub fn step(mut self) -> Result<SmallVec<[Self; 2]>> {
        self.steps += 1;

        match self.curr_func.body.instr(self.next_instr) {
            Left(stmt) => self
                .step_stmt(stmt)
                .map(|config| SmallVec::from_vec(vec![config])),
            Right(term) => self.step_term(term),
        }
    }

    /// Checks if this config is worth continuing symbolic execution for.
    pub fn should_continue(&self, opts: &SymexOptions) -> bool {
        (self.steps < opts.max_steps) && self.path_sat()
    }

    /// Checks if this config's path is satisfiable.
    pub fn path_sat(&self) -> bool {
        let solver = z3::Solver::new();
        solver.assert(&self.path);
        match solver.check() {
            z3::SatResult::Unsat => false,
            z3::SatResult::Sat => true,
            z3::SatResult::Unknown => todo!("shouldn't get unknown rn"),
        }
    }
}
