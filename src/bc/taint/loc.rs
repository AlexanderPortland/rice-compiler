use std::collections::HashSet;

use either::Either;

use crate::bc::{
    dataflow::ptr::{
        PointerAnalysis,
        types::{AllocProj, Allocation, MemLoc},
    },
    types::{AllocArgs, AllocKind, Function, Rvalue, TypeKind},
};

pub fn all_memlocs(func: &Function, ptr: &PointerAnalysis) -> HashSet<MemLoc> {
    let all_allocs: HashSet<Allocation> = ptr.alloc_domain().iter().copied().collect();

    let mut all_memlocs: HashSet<MemLoc> = func.locals.indices().map(MemLoc::Local).collect();

    for alloc in all_allocs {
        match alloc {
            Allocation::FromArg(_arg, ty) => match ty.kind() {
                TypeKind::Array(_inner) => {
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
                    && let Rvalue::Alloc { kind, args, .. } = &l.rvalue
                {
                    match kind {
                        AllocKind::Array => {
                            all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Index));
                        }
                        AllocKind::Tuple | AllocKind::Struct => {
                            let AllocArgs::Lit(inners) = args else {
                                panic!("can only have literal tuples");
                            };
                            for i in 0..inners.len() {
                                all_memlocs.insert(MemLoc::Allocated(alloc, AllocProj::Field(i)));
                            }
                        }
                    }
                } else {
                    panic!("should always have allocs at the location for an alloc");
                }
            }
        }
    }

    all_memlocs
}
