use std::{collections::HashMap, sync::Arc};

use indexical::{ArcIndexSet, ArcIndexVec, IndexedDomain, set::IndexSet};

use crate::bc::{
    types::{
        AllocArgs, AllocKind, Function, Location, Operand, Place, ProjectionElem, Rvalue, Type,
    },
    visit::Visit,
};

/// A location in memeory.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum MemLoc {
    // TODO: should be a local instead
    /// A normal value stored in a place (on the stack).
    Place(Place),
    /// A tuple value within an allocation (that may be on the heap).
    Allocated(Allocation, AllocProj),
}

impl std::fmt::Display for MemLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemLoc::Place(p) => <Place as std::fmt::Display>::fmt(p, f),
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
pub struct Allocation(Location);

indexical::define_index_type! {
    pub struct AllocationIdx for Allocation = u32;
}

impl Allocation {
    pub fn from_loc(loc: Location) -> Self {
        Allocation(loc)
    }

    pub fn with_index_proj(&self, proj: &ProjectionElem) -> MemLoc {
        let proj = match proj {
            ProjectionElem::Field { index, .. } => AllocProj::Field(*index),
            ProjectionElem::Index { .. } => AllocProj::Index,
        };

        MemLoc::Allocated(*self, proj)
    }
}
