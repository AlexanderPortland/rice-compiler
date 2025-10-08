use std::{collections::HashMap, sync::Arc};

use indexical::{ArcIndexSet, ArcIndexVec, IndexedDomain, set::IndexSet};

use crate::bc::{
    dataflow::ptr::types::{Allocation, MemLoc},
    types::{
        AllocArgs, AllocKind, Function, Location, Operand, Place, ProjectionElem, Rvalue, Type,
    },
    visit::Visit,
};

pub mod escape;
mod types;

pub fn pointer_analysis(func: &Function) -> PointerAnalysis {
    let mut analysis = InitialPointerAnalysis::new(func);
    analysis.visit_function(func);
    analysis.finalize()
}

pub struct PointerAnalysis {
    domain: Arc<IndexedDomain<Allocation>>,
    points_to: HashMap<MemLoc, ArcIndexSet<Allocation>>,
}

impl PointerAnalysis {
    fn new(from: &InitialPointerAnalysis) -> Self {
        Self {
            domain: from.domain.clone(),
            points_to: HashMap::new(),
        }
    }

    pub fn alloc_domain(&self) -> &Arc<IndexedDomain<Allocation>> {
        &self.domain
    }

    pub fn points_to(&self) -> &HashMap<MemLoc, ArcIndexSet<Allocation>> {
        &self.points_to
    }

    pub fn aliases(&self, place: Place) -> Vec<MemLoc> {
        let alias = MemLoc::Place(Place::new(place.local, vec![], Type::unit()));
        let then_project = &place.projection;

        let ptrs = self.ptr_aliases(vec![alias], then_project);

        if ptrs.is_empty() {
            return vec![MemLoc::Place(place)];
        }
        ptrs
    }

    fn ptr_aliases(&self, ptrs: Vec<MemLoc>, proj: &[ProjectionElem]) -> Vec<MemLoc> {
        if proj.is_empty() {
            // println!("nvm proj is empty...");
            return ptrs;
        }

        let new_ptrs = ptrs
            .into_iter()
            .flat_map(|ptr| {
                let Some(allocs) = self.points_to.get(&ptr) else {
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
        self.ptr_aliases(new_ptrs, &proj[1..])
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

fn handle_imaginary_allocations(
    of_ty: Type,
    to_place: Place,
    imaginary: &mut Vec<Allocation>,
    el_constraints: &mut Vec<(Allocation, Place)>,
) {
    match of_ty.kind() {
        crate::bc::types::TypeKind::Array(inner_ty) => {
            let array_alloc = Allocation::new_imaginary(imaginary);
            el_constraints.push((array_alloc, to_place));
            handle_imaginary_allocations(
                *inner_ty,
                to_place.extend_projection(
                    [ProjectionElem::Index {
                        index: Operand::Const(crate::bc::types::Const::Int(0)),
                        ty: Type::unit(),
                    }],
                    Type::unit(),
                ),
                imaginary,
                el_constraints,
            );
        }
        crate::bc::types::TypeKind::Tuple(inner_tys) => {
            let array_alloc = Allocation::new_imaginary(imaginary);
            el_constraints.push((array_alloc, to_place));
            for (i, inner) in inner_tys.iter().enumerate() {
                handle_imaginary_allocations(
                    *inner,
                    to_place.extend_projection(
                        [ProjectionElem::Field {
                            index: i,
                            ty: Type::unit(),
                        }],
                        Type::unit(),
                    ),
                    imaginary,
                    el_constraints,
                );
            }
        }
        _ => (),
    }
}

impl InitialPointerAnalysis {
    pub fn new(func: &Function) -> Self {
        let mut el_constraints = Vec::new();
        let mut subset_constraints = Vec::new();
        let mut imaginary_allocations = Vec::new();

        for (idx, ty) in func.params().skip(1) {
            let place = Place::new(idx, vec![], Type::unit());
            handle_imaginary_allocations(
                ty,
                place,
                &mut imaginary_allocations,
                &mut el_constraints,
            );
        }

        // let mut num_allocs =
        // TODO: construct imaginary allocations here...
        // println!("el constraints {:?}", el_constraints);
        // todo!();

        let domain = Arc::new(IndexedDomain::from_iter(
            func.body
                .locations()
                .iter()
                .map(|a| Allocation::from_loc(*a))
                .chain(imaginary_allocations),
        ));

        // let imaginary_allocations =
        InitialPointerAnalysis {
            domain,
            el_constraints,
            subset_constraints,
        }
    }

    fn finalize(self) -> PointerAnalysis {
        let mut analysis = PointerAnalysis::new(&self);

        // Handle all element constraints
        for (alloc, to_place) in self.el_constraints {
            for alias in analysis.aliases(to_place) {
                let set = analysis
                    .points_to
                    .entry(alias)
                    .or_insert(IndexSet::new(&self.domain));

                set.insert(alloc);
            }
        }

        // println!("AFTER EL CONSTRAINTS...");
        for (ptr, allocs) in &analysis.points_to {
            // println!("pointer {ptr}:");
            for alloc in allocs.iter() {
                // println!("\t -> {alloc:?}");
            }
        }

        // Handle all subset constraints
        for (subset, superset) in self.subset_constraints {
            for subset_alias in analysis.aliases(subset) {
                for superset_alias in analysis.aliases(superset) {
                    // println!("subset: {} <= {}", subset_alias, superset_alias);
                    if let Some(subset) = analysis.points_to.get(&subset_alias).cloned() {
                        let superset = analysis
                            .points_to
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
        for (ptr, allocs) in &analysis.points_to {
            // println!("pointer {ptr}:");
            for alloc in allocs.iter() {
                // println!("\t -> {alloc:?}");
            }
        }

        // todo!();
        analysis
    }
}

impl Visit for InitialPointerAnalysis {
    fn visit_statement(&mut self, stmt: &crate::bc::types::Statement, loc: Location) {
        match &stmt.rvalue {
            Rvalue::Alloc { args, kind, .. } => {
                // println!("alloc at loc {loc:?}");
                self.el_constraints
                    .push((Allocation::from_loc(loc), stmt.place));

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
