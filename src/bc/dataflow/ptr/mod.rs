use std::{collections::HashMap, sync::Arc};

use indexical::{ArcIndexSet, ArcIndexVec, IndexedDomain, set::IndexSet};

use crate::bc::{
    types::{
        AllocArgs, AllocKind, Function, Location, Operand, Place, ProjectionElem, Rvalue, Type,
    },
    visit::Visit,
};

pub mod escape;

/// Something that can *point to* an allocation.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
enum Ptr {
    /// A normal value stored in a place (on the stack).
    Place(Place),
    /// A tuple value within an allocation (that may be on the heap).
    AllocationEl(Allocation, AllocProj),
}

impl std::fmt::Display for Ptr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ptr::Place(p) => <Place as std::fmt::Display>::fmt(p, f),
            Ptr::AllocationEl(..) => <Self as std::fmt::Debug>::fmt(self, f),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
enum AllocProj {
    Index,
    Field(usize),
}

/// An allocation, identified by the location at which it was allocated.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
struct Allocation(Location);

indexical::define_index_type! {
    struct AllocationIdx for Allocation = u32;
}

impl Allocation {
    fn with_index_proj(&self, proj: &ProjectionElem) -> Ptr {
        let proj = match proj {
            ProjectionElem::Field { index, .. } => AllocProj::Field(*index),
            ProjectionElem::Index { .. } => AllocProj::Index,
        };

        Ptr::AllocationEl(*self, proj)
    }
}

#[derive(Debug, Clone)]
struct InitialPointerAnalysis {
    domain: Arc<IndexedDomain<Allocation>>,
    /// `(a, p)` where `a` is in `p`
    el_constraints: Vec<(Allocation, Place)>,
    /// `(p1, p2)` where `p1 <= p2`
    subset_constraints: Vec<(Place, Place)>,
}

impl InitialPointerAnalysis {
    pub fn new(domain: Arc<IndexedDomain<Allocation>>) -> Self {
        InitialPointerAnalysis {
            domain,
            el_constraints: Vec::new(),
            subset_constraints: Vec::new(),
        }
    }

    fn points_to(self) -> HashMap<Ptr, ArcIndexSet<Allocation>> {
        let mut points_to: HashMap<Ptr, ArcIndexSet<Allocation>> = HashMap::new();

        // Handle all element constraints
        for (alloc, to_place) in self.el_constraints {
            for alias in Self::aliases(&points_to, to_place) {
                let set = points_to
                    .entry(alias)
                    .or_insert(IndexSet::new(&self.domain));

                set.insert(alloc);
            }
        }

        // println!("AFTER EL CONSTRAINTS...");
        for (ptr, allocs) in &points_to {
            // println!("pointer {ptr}:");
            for alloc in allocs.iter() {
                // println!("\t -> {alloc:?}");
            }
        }

        // Handle all subset constraints
        for (subset, superset) in self.subset_constraints {
            for subset_alias in Self::aliases(&points_to, subset) {
                for superset_alias in Self::aliases(&points_to, superset) {
                    // println!("subset: {} <= {}", subset_alias, superset_alias);
                    if let Some(subset) = points_to.get(&subset_alias).cloned() {
                        let superset = points_to
                            .entry(superset_alias)
                            .or_insert(IndexSet::new(&self.domain));

                        superset.union(&subset);
                    } else {
                        // println!("AHHHH - nothing found for subset {:?}", subset_alias)
                    }
                }
            }
        }

        // println!("FINAL BINDINGS");
        for (ptr, allocs) in &points_to {
            // println!("pointer {ptr}:");
            for alloc in allocs.iter() {
                // println!("\t -> {alloc:?}");
            }
        }

        // todo!();
        points_to
    }

    fn aliases(points_to: &HashMap<Ptr, ArcIndexSet<Allocation>>, place: Place) -> Vec<Ptr> {
        // println!("who aliases place {}?", place);
        let ptrs = Self::ptr_aliases(
            points_to,
            vec![Ptr::Place(Place::new(place.local, vec![], Type::unit()))],
            &place.projection,
        );
        for p in &ptrs {
            // println!("\t -> {}", p);
        }
        ptrs
    }

    fn ptr_aliases(
        points_to: &HashMap<Ptr, ArcIndexSet<Allocation>>,
        ptrs: Vec<Ptr>,
        proj: &[ProjectionElem],
    ) -> Vec<Ptr> {
        if proj.is_empty() {
            // println!("nvm proj is empty...");
            return ptrs;
        }

        let new_ptrs = ptrs
            .into_iter()
            .flat_map(|ptr| {
                let Some(allocs) = points_to.get(&ptr) else {
                    // println!("no info found for ptr {ptr:?}");
                    // println!("on {:?}", points_to);
                    return Vec::new();
                };

                // println!("looking for what {ptr} points to, found allocs");

                allocs
                    .iter()
                    .map(|alloc| alloc.with_index_proj(&proj[0]))
                    .collect()
            })
            .collect();
        // println!("new ptrs are {:?}", new_ptrs);
        Self::ptr_aliases(points_to, new_ptrs, &proj[1..])
    }
}

impl Visit for InitialPointerAnalysis {
    fn visit_statement(&mut self, stmt: &crate::bc::types::Statement, loc: Location) {
        match &stmt.rvalue {
            Rvalue::Alloc { args, kind, .. } => {
                // println!("alloc at loc {loc:?}");
                self.el_constraints.push((Allocation(loc), stmt.place));

                match kind {
                    AllocKind::Array => match args {
                        AllocArgs::Lit(ops) => {
                            for (index, op) in ops.iter().enumerate() {
                                if let Operand::Place(place) = op {
                                    self.subset_constraints.push((
                                        *place,
                                        stmt.place.extend_projection(
                                            [ProjectionElem::Index {
                                                index: Operand::Const(
                                                    crate::bc::types::Const::Int(
                                                        index.try_into().unwrap(),
                                                    ),
                                                ),
                                                ty: op.ty(),
                                            }],
                                            op.ty(),
                                        ),
                                    ));
                                }
                            }
                        }
                        AllocArgs::Repeated { op, count } => {
                            if let Operand::Place(place) = op {
                                self.subset_constraints.push((
                                    *place,
                                    stmt.place.extend_projection(
                                        [ProjectionElem::Index {
                                            index: Operand::Const(crate::bc::types::Const::Int(0)),
                                            ty: op.ty(),
                                        }],
                                        op.ty(),
                                    ),
                                ));
                            }
                        }
                    },
                    AllocKind::Struct | AllocKind::Tuple => {
                        // we can set each individually
                        if let AllocArgs::Lit(ops) = args {
                            for (index, op) in ops.iter().enumerate() {
                                if let Operand::Place(place) = op {
                                    self.subset_constraints.push((
                                        *place,
                                        stmt.place.extend_projection(
                                            [ProjectionElem::Field { index, ty: op.ty() }],
                                            op.ty(),
                                        ),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            Rvalue::MethodCall { args, .. } | Rvalue::Call { args, .. } => {
                for arg in args {
                    if let Operand::Place(p) = arg {
                        // All args can flow to output
                        self.subset_constraints.push((*p, stmt.place));

                        // All args can flow to each other
                        for other_arg in args {
                            if let Operand::Place(other_p) = other_arg
                                && other_arg != arg
                            {
                                self.subset_constraints.push((*p, *other_p));
                                self.subset_constraints.push((*other_p, *p));
                            }
                        }
                    }
                }
            }
            Rvalue::Cast {
                op: Operand::Place(p),
                ..
            }
            | Rvalue::Operand(Operand::Place(p)) => self.subset_constraints.push((*p, stmt.place)),
            _ => (),
        }

        self.super_visit_statement(stmt, loc);
    }
}
