use std::{collections::HashMap, fmt, sync::Arc};

use indexical::{ArcIndexSet, ArcIndexVec, IndexedDomain, set::IndexSet};
use internment::Intern;
use serde::Serialize;

use crate::{
    bc::{
        types::{
            AllocArgs, AllocKind, Function, Local, LocalIdx, Location, Operand, Place,
            ProjectionElem, Rvalue, Type,
        },
        visit::Visit,
    },
    interned,
};

/// A location in memory.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum MemLoc {
    /// A normal value stored in a [Local] (on the stack).
    Local(LocalIdx),
    /// A tuple value within an [Allocation]. It's conceptually on the heap despite that
    /// optimizations might decide to actually allocate it on the stack instead.
    Allocated(Allocation, AllocProj),
}

indexical::define_index_type! {
    pub struct MemLocIdx for MemLoc = u32;
}

impl std::fmt::Display for MemLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemLoc::Local(l) => <LocalIdx as std::fmt::Display>::fmt(l, f),
            MemLoc::Allocated(..) => <Self as std::fmt::Debug>::fmt(self, f),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy, Serialize, PartialOrd, Ord)]
pub enum AllocProj {
    Index,
    Field(usize),
}

/// An allocation, identified by the location at which it was allocated.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum Allocation {
    /// An allocation passed into the function as an argument.
    FromArg(PtrPlace),
    /// A 'real' allocation made within the current function at a given location.
    Real(Location),
}

indexical::define_index_type! {
    pub struct AllocationIdx for Allocation = u32;
}

impl Allocation {
    pub fn from_arg(arg_p: impl Into<PtrPlace>) -> Self {
        Self::FromArg(arg_p.into())
    }

    pub fn from_loc(loc: Location) -> Self {
        Self::Real(loc)
    }

    pub fn with_index_proj(&self, proj: &AllocProj) -> MemLoc {
        MemLoc::Allocated(*self, *proj)
    }
}

/// A simplified version of places that ensure all indexes are identical and
/// projection types don't matter
#[derive(Debug, Hash, PartialEq, Eq, Clone, Serialize, PartialOrd, Ord)]
pub struct PtrPlaceData {
    pub local: LocalIdx,
    pub projection: Vec<AllocProj>,
}

interned!(PtrPlace, PtrPlaceData);

impl PtrPlace {
    pub fn extend_projection(self, proj: AllocProj) -> Self {
        let mut d = (*self.0).clone();
        d.projection.push(proj);
        PtrPlace(Intern::new(d))
    }
}

impl From<Place> for PtrPlace {
    fn from(value: Place) -> Self {
        PtrPlace(Intern::new(PtrPlaceData {
            local: value.local,
            projection: value
                .projection
                .iter()
                .map(|proj_el| match proj_el {
                    ProjectionElem::Field { index, ty } => AllocProj::Field(*index),
                    ProjectionElem::Index { index, ty } => AllocProj::Index,
                })
                .collect(),
        }))
    }
}

impl fmt::Display for PtrPlace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.local)?;
        for proj in &self.projection {
            match proj {
                AllocProj::Field(index) => write!(f, ".{index}")?,
                AllocProj::Index => write!(f, "[?]")?,
            }
        }
        Ok(())
    }
}
