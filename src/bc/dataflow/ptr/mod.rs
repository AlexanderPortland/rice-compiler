use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

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
    let mut analysis = InitialPointerAnalysis::new();
    analysis.visit_function(func);
    analysis.finalize()
}

pub struct PointerAnalysis {
    domain: Arc<IndexedDomain<Allocation>>,
    points_to: HashMap<MemLoc, ArcIndexSet<Allocation>>,
}

impl PointerAnalysis {
    fn new(domain: Arc<IndexedDomain<Allocation>>) -> Self {
        Self {
            domain,
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

    // Find the allocations that `ptrs` could refer to and project into them, repeating until `proj` is empty.
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

                // Add the first projection to any allocations this location could point to.
                allocs
                    .iter()
                    .map(|alloc| alloc.with_index_proj(&proj[0]))
                    .collect()
            })
            .collect();

        // Then continue projecting with those memory locations and the rest of the projections.
        self.could_refer_to_inner(new_ptrs, &proj[1..])
    }
}

#[derive(Debug, Clone, Default)]
/// The early stages of pointer analysis where we have subset and element constraints, but haven't
/// fully constructed the points-to map yet.
///
/// Use [InitialPointerAnalysis::finalize] to finish the analysis by computing that.
struct InitialPointerAnalysis {
    imaginary: Vec<Allocation>,
    /// `(a, p)` where `a` is in `p`
    el_constraints: Vec<(Allocation, Place)>,
    /// `(p1, p2)` where `p1 <= p2`
    subset_constraints: Vec<(Place, Place)>,
}

fn index_extend(p: Place, i: i32) -> Place {
    p.extend_projection(
        [ProjectionElem::Index {
            index: Operand::Const(crate::bc::types::Const::Int(i)),
            ty: Type::unit(),
        }],
        Type::unit(),
    )
}

fn field_extend(p: Place, index: usize) -> Place {
    p.extend_projection(
        [ProjectionElem::Field {
            index,
            ty: Type::unit(),
        }],
        Type::unit(),
    )
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
                index_extend(to_place, 0),
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
                    field_extend(to_place, i),
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
    pub fn new() -> Self {
        Self::default()
    }

    fn alloc_domain(&self) -> Arc<IndexedDomain<Allocation>> {
        let mut allocs = HashSet::new();

        allocs.extend(self.imaginary.iter().cloned());
        for (alloc, _) in &self.el_constraints {
            allocs.insert(*alloc);
        }
        Arc::new(IndexedDomain::from_iter(allocs))
    }

    fn finalize(self) -> PointerAnalysis {
        let domain = self.alloc_domain();
        let mut analysis = PointerAnalysis::new(domain.clone());

        // Handle all element constraints first
        for (alloc, to_place) in self.el_constraints {
            for alias in analysis.could_refer_to(to_place) {
                let possible_allocations = analysis
                    .points_to
                    .entry(alias)
                    .or_insert(IndexSet::new(&domain));

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
                            .or_insert(IndexSet::new(&domain));

                        superset.union(&subset);
                    }
                }
            }
        }

        analysis
    }
}

impl Visit for InitialPointerAnalysis {
    fn visit_function(&mut self, func: &Function) {
        for (idx, ty) in func.params().skip(1) {
            let place = Place::new(idx, vec![], Type::unit());
            handle_imaginary_allocations(ty, place, &mut self.imaginary, &mut self.el_constraints);
        }

        self.super_visit_function(func);
    }

    fn visit_statement(&mut self, stmt: &crate::bc::types::Statement, loc: Location) {
        match &stmt.rvalue {
            Rvalue::Alloc { args, kind, .. } => {
                self.el_constraints
                    .push((Allocation::from_loc(loc), stmt.place));

                match kind {
                    AllocKind::Array => {
                        let places: Box<dyn Iterator<Item = Place>> = match args {
                            AllocArgs::Lit(ops) => {
                                Box::new(ops.iter().filter_map(Operand::as_place))
                            }
                            AllocArgs::Repeated { op, .. } => {
                                Box::new(std::iter::once(op).filter_map(Operand::as_place))
                            }
                        };

                        for place in places {
                            self.subset_constraints
                                .push((place, index_extend(stmt.place, 0)));
                        }
                    }
                    AllocKind::Struct | AllocKind::Tuple => {
                        // we can set each individually
                        if let AllocArgs::Lit(ops) = args {
                            for (index, op) in ops.iter().enumerate() {
                                if let Operand::Place(place) = op {
                                    self.subset_constraints
                                        .push((*place, field_extend(stmt.place, index)));
                                }
                            }
                        }
                    }
                }
            }
            Rvalue::MethodCall { args, .. } | Rvalue::Call { args, .. } => {
                for p in args.iter().filter_map(Operand::as_place) {
                    // All args can flow to output
                    self.subset_constraints.push((p, stmt.place));

                    // All args can flow to each other
                    for other_p in args.iter().filter_map(Operand::as_place) {
                        if p != other_p {
                            self.subset_constraints.push((p, other_p));
                            self.subset_constraints.push((other_p, p));
                        }
                    }
                }
            }
            // Just propagate if the stmt is a cast or assignment.
            Rvalue::Cast {
                op: Operand::Place(p),
                ..
            }
            | Rvalue::Operand(Operand::Place(p)) => self.subset_constraints.push((*p, stmt.place)),
            _ => (),
        }

        handle_imaginary_allocations(
            stmt.place.ty,
            stmt.place,
            &mut self.imaginary,
            &mut self.el_constraints,
        );

        self.super_visit_statement(stmt, loc);
    }
}
