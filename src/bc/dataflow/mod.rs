//! Intraprocedural dataflow analysis for the bytecode.
//!
//! API design is heavily inspired by the [rustc_mir_dataflow](https://doc.rust-lang.org/stable/nightly-rustc/rustc_mir_dataflow/index.html) crate.

#![allow(unused)]

pub mod r#const;
pub mod dead_code;
pub mod dead_control;
pub mod ptr;

use either::Either;
use indexical::{
    IndexedValue, bitset::bitvec::ArcIndexSet as IndexSet, vec::ArcIndexVec as IndexVec,
};
use smallvec::SmallVec;
use std::collections::VecDeque;

use crate::bc::types::BasicBlockIdx;

use super::types::{Function, Location, Statement, Terminator};

/// A trait for types representing a [join-semilattice](https://en.wikipedia.org/wiki/Semilattice).
///
/// `join` must be associative, commutative, and idempotent.
pub trait JoinSemiLattice: Eq {
    /// Returns true if `self` is changed by `join`.
    fn join(&mut self, other: &Self) -> bool;
}

/// Direction for dataflow analysis.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Forward,
    Backward,
}

/// Interface for dataflow analyses.
pub trait Analysis {
    /// The type of dataflow analysis state held at each program location.
    type Domain: JoinSemiLattice + Clone;

    /// The direction of the dataflow analysis, forward or backward.
    const DIRECTION: Direction;

    /// The bottom element of the bounded join-semilattice [`Self::Domain`].
    ///
    /// This is the initial value of the analysis state.
    fn bottom(&self, func: &Function) -> Self::Domain;

    /// Transfer function for statements.
    fn handle_statement(&self, state: &mut Self::Domain, statement: &Statement, loc: Location);

    /// Transfer function for terminators.
    fn handle_terminator(&self, state: &mut Self::Domain, terminator: &Terminator, loc: Location);
}

pub type AnalysisState<A> = IndexVec<Location, <A as Analysis>::Domain>;

/// Executes the dataflow analysis on the given function to a fixpoint, returning
/// the analysis state at each location.
pub fn analyze_to_fixpoint<A: Analysis>(analysis: &A, func: &Function) -> AnalysisState<A> {
    // Create the initial state for our analysis -- every location has the bottom abstract domain.
    // REMEMBER, this represents the state BEFORE the given instruction is executed.
    let mut state = IndexVec::from_elem(analysis.bottom(func), func.body.locations());

    // Create the list of instructions we must visit
    let mut to_visit = func
        .body
        .locations()
        .iter()
        .copied()
        .collect::<VecDeque<_>>();

    while let Some(loc) = to_visit.pop_front() {
        let (flow_from, flow_to) = flow::<A>(func, loc);

        // Our current in, which must be joined with new info (if any)
        let mut new_in = state.get(loc).clone();

        let mut changed = false;

        for flow_from_loc in flow_from {
            changed |= new_in.join(&apply_transfer(analysis, &state, func, flow_from_loc));
        }

        if changed {
            *state.get_mut(loc) = new_in;
            for to in flow_to {
                to_visit.push_back(to);
            }
        }
    }

    state
}

fn apply_transfer<A: Analysis>(
    analysis: &A,
    state: &AnalysisState<A>,
    func: &Function,
    loc: Location,
) -> A::Domain {
    let mut my_state = state.get(loc).clone();
    match func.body.instr(loc) {
        Either::Right(term) => {
            analysis.handle_terminator(&mut my_state, term, loc);
        }
        Either::Left(stmt) => {
            analysis.handle_statement(&mut my_state, stmt, loc);
        }
    }
    my_state
}

fn flow<A: Analysis>(
    func: &Function,
    loc: Location,
) -> (SmallVec<[Location; 2]>, SmallVec<[Location; 2]>) {
    let predecessors = func.body.predecessors(loc);
    let successors = func.body.successors(loc);

    match A::DIRECTION {
        Direction::Forward => (predecessors, successors),
        Direction::Backward => (successors, predecessors),
    }
}
