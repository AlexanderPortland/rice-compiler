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

    /// Gets the domain for allocations within this analysis.
    pub fn alloc_domain(&self) -> &Arc<IndexedDomain<Allocation>> {
        &self.domain
    }

    pub fn points_to(&self) -> &HashMap<MemLoc, ArcIndexSet<Allocation>> {
        &self.points_to
    }

    /// Find all memory locations a place could refer to.
    pub fn could_refer_to(&self, place: Place) -> Vec<MemLoc> {
        let alias = MemLoc::Local(place.local);
        let then_project = &place.projection;

        self.could_refer_to_inner(vec![alias.clone()], then_project)
    }

    // Recursively find all allocations `ptrs` can point to and project an element.
    fn could_refer_to_inner(&self, ptrs: Vec<MemLoc>, proj: &[ProjectionElem]) -> Vec<MemLoc> {
        if proj.is_empty() {
            return ptrs;
        }

        let new_ptrs = ptrs
            .into_iter()
            .flat_map(|ptr| {
                let Some(allocs) = self.points_to.get(&ptr) else {
                    return Vec::new();
                };

                allocs
                    .iter()
                    .map(|alloc| alloc.with_index_proj(&proj[0]))
                    .collect()
            })
            .collect();

        self.could_refer_to_inner(new_ptrs, &proj[1..])
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

struct ImaginaryAllocationsVisitor<'z>(&'z mut Vec<Allocation>, &'z mut Vec<(Allocation, Place)>);

impl Visit for ImaginaryAllocationsVisitor<'_> {
    fn visit_function(&mut self, func: &Function) {
        // println!("visiting for imaginary on func {}", func.name);
        for (idx, ty) in func.params().skip(1) {
            let place = Place::new(idx, vec![], Type::unit());
            handle_imaginary_allocations(ty, place, self.0, self.1);
        }

        self.super_visit_function(func);
    }

    fn visit_statement(&mut self, stmt: &crate::bc::types::Statement, loc: Location) {
        handle_imaginary_allocations(stmt.place.ty, stmt.place, self.0, self.1);
    }
}

impl InitialPointerAnalysis {
    pub fn new(func: &Function) -> Self {
        let mut el_constraints = Vec::new();
        let mut subset_constraints = Vec::new();
        let mut imaginary_allocations = Vec::new();

        // Have to handle the imaginary allocations here, so we can properly build the
        // allocation domain for the function. Otherwise, it might make more sense to do this with the other visitor.
        // TODO: LMAO im just realizing that's dumb and we totally could construct the domain after.
        ImaginaryAllocationsVisitor(&mut imaginary_allocations, &mut el_constraints)
            .visit_function(func);

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

        // Handle all element constraints first
        for (alloc, to_place) in self.el_constraints {
            for alias in analysis.could_refer_to(to_place) {
                let possible_allocations = analysis
                    .points_to
                    .entry(alias)
                    .or_insert(IndexSet::new(&self.domain));

                possible_allocations.insert(alloc);
            }
        }

        // Handle all subset constraints
        for (subset, superset) in self.subset_constraints {
            for subset_alias in analysis.could_refer_to(subset) {
                for superset_alias in analysis.could_refer_to(superset) {
                    if let Some(subset) = analysis.points_to.get(&subset_alias).cloned() {
                        let superset = analysis
                            .points_to
                            .entry(superset_alias)
                            .or_insert(IndexSet::new(&self.domain));

                        superset.union(&subset);
                    }
                }
            }
        }

        analysis
    }
}

impl Visit for InitialPointerAnalysis {
    fn visit_statement(&mut self, stmt: &crate::bc::types::Statement, loc: Location) {
        match &stmt.rvalue {
            Rvalue::Alloc { args, kind, .. } => {
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
                        AllocArgs::Repeated {
                            op: Operand::Place(place),
                            count,
                        } => {
                            self.subset_constraints.push((
                                *place,
                                stmt.place.extend_projection(
                                    [ProjectionElem::Index {
                                        index: Operand::Const(crate::bc::types::Const::Int(0)),
                                        ty: Type::unit(),
                                    }],
                                    Type::unit(),
                                ),
                            ));
                        }
                        _ => (),
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
