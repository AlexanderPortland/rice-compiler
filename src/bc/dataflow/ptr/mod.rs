use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::Deref,
    sync::Arc,
};

use indexical::{ArcIndexSet, ArcIndexVec, FromIndexicalIterator, IndexedDomain, set::IndexSet};

use crate::bc::{
    dataflow::ptr::types::{AllocProj, Allocation, MemLoc, PtrPlace, PtrPlaceData},
    types::{
        AllocArgs, AllocKind, Function, Location, Operand, Place, ProjectionElem, Rvalue, Type,
    },
    visit::Visit,
};

pub mod escape;
pub mod types;

/// Conceptually should also
pub fn pointer_analysis(func: &Function) -> PointerAnalysis {
    let mut analysis = InitialPointerAnalysis::new(func);
    analysis.visit_function(func);
    analysis.finalize()
}

#[derive(Debug)]
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

    /// The list of all allocations that can be reached with additional projections
    /// from a given starting place.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn reachable_memlocs(&self, p: &Place) -> HashSet<MemLoc> {
        let memlocs = self.could_refer_to(p);

        let mut to_visit = memlocs
            .iter()
            .flat_map(|memloc| {
                self.points_to
                    .get(memloc)
                    .into_iter()
                    .flat_map(IndexSet::iter)
            })
            .collect::<Vec<_>>();
        let mut collect: HashSet<MemLoc> = memlocs.into_iter().collect();
        let mut visited = HashSet::new();

        while let Some(visit) = to_visit.pop() {
            if !visited.insert(visit) {
                /// Get all memlocs reachable from this allocation
                for (memloc, points_to) in &self.points_to {
                    if let MemLoc::Allocated(alloc, _) = memloc
                        && alloc == visit
                    {
                        collect.insert(*memloc);
                        to_visit.extend(points_to.iter());
                    }
                }
            }
        }

        // println!("found {collect:?}");

        collect
    }

    // NOTE: implemented this for like no reason bc i thought maybe it'd be useful in the future
    // and then it was a cool challenge to think about.
    pub fn with_function_arguments(
        self,
        arguments: impl IntoIterator<Item = (PtrPlace, Allocation)>,
    ) -> Result<Self, String> {
        let arguments = arguments.into_iter().collect::<HashMap<_, _>>();
        let new_allocs = self
            .alloc_domain()
            .iter()
            .filter(|alloc| match alloc {
                Allocation::Real(_) => true,
                Allocation::FromArg(_, _) => false,
            })
            .chain(arguments.iter().map(|(place, alloc)| alloc))
            .copied();
        let domain = Arc::new(new_allocs.collect::<IndexedDomain<_>>());

        let points_to = self
            .points_to
            .into_iter()
            .map(|(loc, allocs)| {
                let new_allocs = allocs
                    .iter()
                    .map(|alloc| Self::sub_alloc(alloc, &arguments))
                    .collect::<Result<Vec<Allocation>, String>>()?;
                let new_loc = match loc {
                    MemLoc::Allocated(alloc, proj) => {
                        MemLoc::Allocated(Self::sub_alloc(&alloc, &arguments)?, proj)
                    }
                    non_alloc @ MemLoc::Local(_) => non_alloc,
                };

                Ok((
                    new_loc,
                    IndexSet::from_indexical_iter(new_allocs.iter(), &domain),
                ))
            })
            .collect::<Result<HashMap<_, _>, String>>()?;

        Ok(Self { domain, points_to })
    }

    fn sub_alloc(
        alloc: &Allocation,
        replace: &HashMap<PtrPlace, Allocation>,
    ) -> Result<Allocation, String> {
        match alloc {
            Allocation::Real(_) => Ok(*alloc),
            Allocation::FromArg(place, ty) => replace
                .get(place)
                .ok_or(format!("no replacement found for arg place {place}"))
                .cloned(),
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
    pub fn could_refer_to<T: Into<PtrPlace> + Copy>(&self, place: &T) -> Vec<MemLoc> {
        let place: PtrPlace = (*place).into();
        let alias = MemLoc::Local(place.local);
        let then_project = &place.projection;

        self.could_refer_to_inner(vec![alias], then_project)
    }

    // Find the allocations that `ptrs` could refer to and project into them, repeating until `proj` is empty.
    fn could_refer_to_inner(&self, ptrs: Vec<MemLoc>, proj: &[AllocProj]) -> Vec<MemLoc> {
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

#[derive(Debug, Clone)]
/// The early stages of pointer analysis where we have subset and element constraints, but haven't
/// fully constructed the points-to map yet.
///
/// Use [`InitialPointerAnalysis::finalize`] to finish the analysis by computing that.
struct InitialPointerAnalysis {
    imaginary: Vec<Allocation>,
    /// `(a, p)` where `a` is in `p`
    el_constraints: Vec<(Allocation, PtrPlace)>,
    /// `(p1, p2)` where `p1 <= p2`
    subset_constraints: Vec<(PtrPlace, PtrPlace)>,
}

// TODO: remove
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

#[allow(clippy::only_used_in_recursion)]
fn handle_argument_alloc(
    of_ty: Type,
    to_place: Place,
    arg_allocs: &mut Vec<Allocation>,
    el_constraints: &mut Vec<(Allocation, PtrPlace)>,
) {
    match of_ty.kind() {
        crate::bc::types::TypeKind::Array(inner_ty) => {
            let array_alloc = Allocation::from_arg(to_place, of_ty);
            el_constraints.push((array_alloc, to_place.into()));

            handle_argument_alloc(
                *inner_ty,
                index_extend(to_place, 0),
                arg_allocs,
                el_constraints,
            );
        }
        crate::bc::types::TypeKind::Tuple(inner_tys) => {
            let array_alloc = Allocation::from_arg(to_place, of_ty);
            el_constraints.push((array_alloc, to_place.into()));

            for (i, inner) in inner_tys.iter().enumerate() {
                handle_argument_alloc(
                    *inner,
                    field_extend(to_place, i),
                    arg_allocs,
                    el_constraints,
                );
            }
        }
        _ => (),
    }
}

impl InitialPointerAnalysis {
    pub fn new(func: &Function) -> Self {
        let mut new = Self {
            imaginary: Vec::new(),
            el_constraints: Vec::new(),
            subset_constraints: Vec::new(),
        };

        // Handle all allocations passed into the function
        for (idx, of_ty) in func.params() {
            handle_argument_alloc(
                of_ty,
                Place::new(idx, Vec::new(), of_ty),
                &mut new.imaginary,
                &mut new.el_constraints,
            );
        }

        new
    }

    fn alloc_domain(&self) -> Arc<IndexedDomain<Allocation>> {
        let mut allocs = HashSet::new();

        allocs.extend(self.imaginary.iter().copied());
        for (alloc, _) in &self.el_constraints {
            allocs.insert(*alloc);
        }
        Arc::new(IndexedDomain::from_iter(allocs))
    }

    fn finalize(self) -> PointerAnalysis {
        let domain = self.alloc_domain();
        let mut analysis = PointerAnalysis::new(domain.clone());

        // Have to keep looping through constraints until we hit a fixed point
        let mut was_changed = true;

        while (was_changed) {
            was_changed = false;

            // Handle all element constraints
            for (alloc, to_place) in &self.el_constraints {
                for alias in analysis.could_refer_to(to_place) {
                    let possible_allocations = analysis
                        .points_to
                        .entry(alias)
                        .or_insert(IndexSet::new(&domain));

                    if !possible_allocations.contains(alloc) {
                        possible_allocations.insert(*alloc);
                        was_changed |= true;
                    }
                }
            }

            // Handle all subset constraints
            for (subset, superset) in &self.subset_constraints {
                for subset_alias in analysis.could_refer_to(subset) {
                    for superset_alias in analysis.could_refer_to(superset) {
                        if let Some(subset) = analysis.points_to.get(&subset_alias).cloned() {
                            let superset = analysis
                                .points_to
                                .entry(superset_alias)
                                .or_insert(IndexSet::new(&domain));

                            was_changed |= superset.union_changed(&subset);
                        }
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
                    .push((Allocation::from_loc(loc), stmt.place.into()));

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
                                .push((place.into(), index_extend(stmt.place, 0).into()));
                        }
                    }
                    AllocKind::Struct | AllocKind::Tuple => {
                        // we can set each individually
                        if let AllocArgs::Lit(ops) = args {
                            for (index, op) in ops.iter().enumerate() {
                                if let Operand::Place(place) = op {
                                    self.subset_constraints.push((
                                        (*place).into(),
                                        field_extend(stmt.place, index).into(),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            Rvalue::MethodCall { args, .. } | Rvalue::Call { args, .. } => {
                for p in args
                    .iter()
                    .filter_map(Operand::as_place)
                    .map(PtrPlace::from)
                {
                    // All args can flow to output
                    self.subset_constraints.push((p, stmt.place.into()));

                    // All args can flow to each other
                    for other_p in args
                        .iter()
                        .filter_map(Operand::as_place)
                        .map(PtrPlace::from)
                    {
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
            | Rvalue::Operand(Operand::Place(p)) => self
                .subset_constraints
                .push(((*p).into(), stmt.place.into())),
            _ => (),
        }

        self.super_visit_statement(stmt, loc);
    }
}
