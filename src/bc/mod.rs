//! Bytecode (BC) code representation.

use std::fmt::Debug;

use miette::Result;
use strum::{Display, EnumString};

use crate::bc::dataflow::{dead_control, ptr};

use self::types::{Function, Program};
use dataflow::r#const::const_prop;
use dataflow::dead_code::eliminate_dead_code;

mod dataflow;
mod lower;
mod print;
mod taint;
pub mod types;
mod visit;

pub use self::lower::lower;

#[derive(Clone, Copy, Debug, Display, EnumString)]
pub enum OptLevel {
    #[strum(serialize = "0")]
    NoOpt,
    #[strum(serialize = "1")]
    AllOpt,
}

/// Run correctness analyses on the whole program.
pub fn analyze(prog: &Program) -> Result<()> {
    // Only do our taint analysis if we have any secure functions.
    if prog.functions().iter().any(|func| func.secure()) {
        taint::check_taints(prog)
    } else {
        miette::Result::Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct OptimizeOptions {
    pub opt_level: OptLevel,
}

/// Run optimizations on the whole program.
///
/// Optimizations are disabled at [`OptLevel::NoOpt`].
pub fn optimize(prog: &mut Program, opts: OptimizeOptions) {
    if matches!(opts.opt_level, OptLevel::AllOpt) {
        for func in prog.functions_mut() {
            optimize_func(func);
        }
    }
}

type Pass = Box<dyn Fn(&mut Function) -> bool>;

/// Run optimization passes to a fixed point.
fn optimize_func(func: &mut Function) {
    let passes: Vec<Pass> = vec![
        // TODO: insert passes here
        Box::new(const_prop),
        Box::new(eliminate_dead_code),
        Box::new(dead_control::skip_empty_blocks),
        Box::new(ptr::escape::stack_for_non_escaping),
        Box::new(dead_control::merge_straight_line_blocks),
    ];

    let cleanup_passes: Vec<Pass> = vec![
        Box::new(dead_control::remove_unused_blocks),
        Box::new(dead_control::remove_unused_locals),
    ];

    loop {
        let mut changed = false;
        for pass in &passes {
            changed |= pass(func);

            for cleanup in &cleanup_passes {
                cleanup(func);
            }
        }
        if !changed {
            break;
        }
    }
}
