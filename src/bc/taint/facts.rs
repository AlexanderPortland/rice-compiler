use std::{collections::HashMap, sync::Arc};

use indexical::IndexedDomain;

use crate::{
    bc::{
        dataflow::{
            self, AnalysisState,
            r#const::ConstAnalysis,
            ptr::{PointerAnalysis, types::MemLoc},
        },
        taint::{
            control::{self, ControlDependencies},
            loc::all_memlocs,
        },
        types::{Function, Program},
    },
    utils::Symbol,
};

pub struct Facts {
    ptr: PointerAnalysis,
    _const: AnalysisState<ConstAnalysis>,
    control: ControlDependencies,
    domains: Domains,
}

pub struct Domains {
    pub memloc: Arc<IndexedDomain<MemLoc>>,
}

impl Facts {
    pub fn domains(&self) -> &Domains {
        &self.domains
    }

    pub fn ptr(&self) -> &PointerAnalysis {
        &self.ptr
    }

    pub fn control(&self) -> &ControlDependencies {
        &self.control
    }

    pub fn _const(&self) -> &AnalysisState<ConstAnalysis> {
        &self._const
    }
}

impl std::fmt::Debug for Facts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "facts[ptr: {:?}, control: {:?}]",
            self.ptr, self.control
        ))
    }
}

pub fn intraprocedural_facts(prog: &Program) -> HashMap<Symbol, Facts> {
    let mut facts = HashMap::new();
    for func in prog.functions() {
        facts.insert(func.name, generate_facts(func));
    }
    facts
}

fn generate_facts(func: &Function) -> Facts {
    let _const = dataflow::analyze_to_fixpoint(&dataflow::r#const::ConstAnalysis, func);
    let ptr = dataflow::ptr::pointer_analysis(func);
    let control = control::control_dependencies(func);

    // println!("POINTER REVIEW for {}", func.name);
    for (loc, points_to) in ptr.points_to() {
        for p in points_to.iter() {
            // println!("{loc} -> {p:?}");
        }
    }

    Facts {
        _const,
        control,
        domains: Domains {
            memloc: Arc::new(IndexedDomain::from_iter(
                all_memlocs(func, &ptr).into_iter(),
            )),
        },
        ptr,
    }
}
