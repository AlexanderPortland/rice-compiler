use crate::bc::types::Program;
use miette::Result;

mod control;
mod facts;

pub fn check_taints(prog: &Program) -> Result<()> {
    let facts = facts::intraprocedural_facts(prog);
    for (i, func) in prog.functions().iter().enumerate() {
        println!("{}: {:?}", func.name, facts[i]);
    }
    Ok(())
}
