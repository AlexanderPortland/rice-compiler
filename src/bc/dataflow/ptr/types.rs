use std::{collections::HashMap, sync::Arc};

use indexical::{ArcIndexSet, ArcIndexVec, IndexedDomain, set::IndexSet};

use crate::bc::{
    types::{
        AllocArgs, AllocKind, Function, Local, LocalIdx, Location, Operand, Place, ProjectionElem,
        Rvalue, Type,
    },
    visit::Visit,
};

/// A location in memeory.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum MemLoc {
    // TODO: should be a local instead
    /// A normal value stored in a place (on the stack).
    Local(LocalIdx),
    /// A tuple value within an allocation (that may be on the heap).
    Allocated(Allocation, AllocProj),
}

impl std::fmt::Display for MemLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemLoc::Local(l) => <LocalIdx as std::fmt::Display>::fmt(l, f),
            MemLoc::Allocated(..) => <Self as std::fmt::Debug>::fmt(self, f),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum AllocProj {
    Index,
    Field(usize),
}

/// An allocation, identified by the location at which it was allocated.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum Allocation {
    /// An abstract allocation that we know exists somewhere,
    /// but was not allocated in the given function.
    Abstract(usize),
    /// A 'real' allocation made within the current function at a given location.
    Real(Location),
}

indexical::define_index_type! {
    pub struct AllocationIdx for Allocation = u32;
}

impl Allocation {
    pub fn new_imaginary(existing: &mut Vec<Allocation>) -> Self {
        let new = Allocation::Abstract(existing.len());
        existing.push(new);
        new
    }

    pub fn from_loc(loc: Location) -> Self {
        Self::Real(loc)
    }

    pub fn with_index_proj(&self, proj: &ProjectionElem) -> MemLoc {
        let proj = match proj {
            ProjectionElem::Field { index, .. } => AllocProj::Field(*index),
            ProjectionElem::Index { .. } => AllocProj::Index,
        };

        MemLoc::Allocated(*self, proj)
    }
}
