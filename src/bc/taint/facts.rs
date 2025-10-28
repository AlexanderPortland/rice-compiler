use crate::bc::{
    dataflow::{self, AnalysisState, r#const::ConstAnalysis, ptr::PointerAnalysis},
    taint::control::{self, ControlDependencies},
    types::{Function, Program},
};

#[allow(clippy::used_underscore_binding)]
pub struct Facts {
    ptr: PointerAnalysis,
    _const: AnalysisState<ConstAnalysis>,
    control: ControlDependencies,
}

impl std::fmt::Debug for Facts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "facts[ptr: {:?}, control: {:?}]",
            self.ptr, self.control
        ))
    }
}

pub fn intraprocedural_facts(prog: &Program) -> Vec<Facts> {
    prog.functions().iter().map(generate_facts).collect()
}

fn generate_facts(func: &Function) -> Facts {
    let _const = dataflow::analyze_to_fixpoint(&dataflow::r#const::ConstAnalysis, func);
    let ptr = dataflow::ptr::pointer_analysis(func);
    let control = control::control_dependencies(func);

    Facts {
        ptr,
        _const,
        control,
    }
}
