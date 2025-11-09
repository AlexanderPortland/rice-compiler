use std::collections::HashSet;

use crate::{
    bc::{
        types::{Operand, Program, Rvalue},
        visit::Visit,
    },
    utils::Symbol,
};

pub fn eliminate_dead_funcs(prog: &mut Program) {
    let mut called = CalledFuncs::default();
    called.0.insert(Symbol::main());
    for func in prog.functions() {
        called.visit_function(func);
    }

    let mut called = called.0;

    // println!("called is {:?}", called);
    prog.retain_functions(|func| called.contains(&func.name) || func.name.contains("__"));
}

#[derive(Default)]
struct CalledFuncs(HashSet<Symbol>);

impl Visit for CalledFuncs {
    fn visit_rvalue(&mut self, rvalue: &crate::bc::types::Rvalue, loc: crate::bc::types::Location) {
        match rvalue {
            Rvalue::Closure { f, .. }
            | Rvalue::Call {
                f: Operand::Func { f, .. },
                ..
            } => {
                self.0.insert(*f);
            }
            _ => (),
        }

        self.super_visit_rvalue(rvalue, loc);
    }
}
