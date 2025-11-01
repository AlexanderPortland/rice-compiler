use std::collections::HashSet;

use either::Either;

use crate::bc::{
    dataflow::ptr::{
        PointerAnalysis,
        types::{AllocProj, Allocation, MemLoc, PtrPlace},
    },
    types::{AllocArgs, AllocKind, Function, Place, Rvalue, Type, TypeKind},
    visit::Visit,
};

pub fn all_memlocs(func: &Function, ptr: &PointerAnalysis) -> HashSet<MemLoc> {
    let all_allocs: HashSet<Allocation> = ptr.alloc_domain().iter().cloned().collect();
    let mut all_memlocs: HashSet<MemLoc> = func
        .locals
        .indices()
        .map(|local| MemLoc::Local(local))
        .collect();

    for alloc in all_allocs {
        match alloc {
            Allocation::FromArg(arg, ty) => match ty.kind() {
                TypeKind::Array(inner) => {
                    all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Index));
                }
                TypeKind::Tuple(inners) => {
                    for i in 0..inners.len() {
                        all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Field(i)));
                    }
                }
                TypeKind::Struct(_) => todo!(),
                _ => unreachable!("should never have this"),
            },
            Allocation::Real(loc) => {
                if let Either::Left(l) = func.body.instr(loc)
                    && let Rvalue::Alloc { kind, loc, args } = &l.rvalue
                {
                    match kind {
                        AllocKind::Array => {
                            all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Index));
                        }
                        AllocKind::Tuple => {
                            let AllocArgs::Lit(inners) = args else {
                                panic!("can only have literal tuples");
                            };
                            for i in 0..inners.len() {
                                all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Field(i)));
                            }
                        }
                        _ => todo!("handle structs"),
                    }
                } else {
                    panic!("should always have allocs at the location for an alloc");
                }
            }
        };
    }

    // println!("all memlocs in {} are {:?}", func.name, all_memlocs);
    all_memlocs
}

struct PlaceVisitor(HashSet<Place>);

impl Visit for PlaceVisitor {
    fn visit_rvalue_place(&mut self, _place: &Place, _loc: crate::bc::types::Location) {
        self.0.extend(_place.places());
    }

    fn visit_lvalue(&mut self, place: &Place, _loc: crate::bc::types::Location) {
        self.0.extend(place.places());
    }
}
