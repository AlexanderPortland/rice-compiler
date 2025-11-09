use std::{collections::HashSet, sync::Arc};

use indexical::IndexedDomain;
use itertools::Itertools;
use petgraph::{
    Direction::Outgoing,
    visit::{EdgeIndexable, EdgeRef, IntoEdgesDirected},
};

use crate::{
    ast::types::Span,
    bc::{
        dataflow::dead_control::{BBUpdater, LocalUpdater, update_locals_w},
        types::{
            BasicBlock, BasicBlockIdx, Body, Cfg, Function, LocalIdx, Location, Operand, Place,
            Program, Rvalue, Statement, Terminator, TerminatorKind, Type,
        },
        visit::{Visit, VisitMut},
    },
    utils::Symbol,
};

#[derive(Debug)]
pub struct InlineOptions {
    inline_std_calls: bool,
}

const OPTS: InlineOptions = InlineOptions {
    inline_std_calls: false,
};

// pub fn pub_inline_calls(prog: &Program) -> impl Fn(&mut Function) -> bool {
//     move |func: &mut Function| inline_calls(prog, func)
// }

/// For now, just inlines the first call it sees
pub fn inline_calls(prog: &Program, func: &mut Function) -> bool {
    // println!("inlining on {func}");
    let Some((sym, loc, inlined_func)) = inlineable_calls(prog, func).next() else {
        return false;
    };
    // println!("i will inline {sym} @ {loc}");
    // println!("which has body {inlined_func}");
    // println!("inlined locals {:?}", inlined_func.locals.as_vec());

    let mut inlined_cfg = inlined_func.body.cfg().clone();
    let mut old_cfg = func.body.cfg().clone();

    let split_block = old_cfg
        .node_weight_mut(loc.block.into())
        .expect("should have a block here...");

    let stmts_after_call = split_block
        .statements
        .drain(loc.instr..)
        .skip(1)
        .collect::<Vec<_>>();
    let term_after_call = split_block.terminator.clone();
    // println!("now have split block {}", split_block);
    // println!("instructions after call is {:?}", stmts_after_call);

    let after_call_block: BasicBlockIdx = old_cfg
        .add_node(BasicBlock {
            statements: stmts_after_call,
            terminator: term_after_call,
        })
        .into();

    // Do this just so it makes sense intermediately
    old_cfg
        .node_weight_mut(loc.block.into())
        .expect("should have a block here...")
        .terminator
        .kind = TerminatorKind::Jump(after_call_block);

    // Move all CFG edges from that old block to the new one
    let curr_targets = old_cfg
        .edges_directed(loc.block.into(), Outgoing)
        .map(|a| a.target())
        .collect::<Vec<_>>();

    for t in curr_targets {
        old_cfg.add_edge(after_call_block.into(), t, ());
        old_cfg.remove_edge(
            old_cfg
                .find_edge(loc.block.into(), t)
                .expect("should be there..."),
        );
    }
    old_cfg.add_edge(loc.block.into(), after_call_block.into(), ());

    let old_body = Body::new(old_cfg.clone());
    // println!("new old cfg is {}", old_body);

    // Now update our to-inline cfg so that it all makes sense wrt the old cfg
    // We dont want local or bb collisions

    // -1 because we won't be taking the x0 env arg from our func
    let local_offset = func.locals.len();
    let bb_offset = old_cfg.node_count();
    let mut local_updater = LocalUpdater(&|idx: LocalIdx| idx - 1 + local_offset);
    let mut bb_updater = BBUpdater(&|bb| bb + bb_offset);

    // Update locals within the inlined func to avoid collisions
    for block in inlined_cfg.node_weights_mut() {
        // TODO: fix thsi zero
        let block_idx = 0.into();
        local_updater.visit_basic_block(block, block_idx);
        bb_updater.visit_basic_block(block, block_idx);
    }

    let inlined_body = Body::new(inlined_cfg.clone());
    // println!("which has body {inlined_body}");

    // todo!();

    let stmt = func.body.instr(loc).expect_left("should be stmt at call");
    let Rvalue::Call { args, .. } = &stmt.rvalue else {
        panic!("ahsdhf");
    };

    // Build statements for setting up args
    let setup = call_setup_stmts(args, inlined_func, local_offset);
    let first_block = inlined_cfg
        .node_weight_mut(BasicBlockIdx::new(0).into())
        .expect("should have first block");
    // println!("first block {}", first_block);
    let old_stmts = std::mem::take(&mut first_block.statements);
    first_block.statements.extend(setup);
    first_block.statements.extend(old_stmts);

    let inlined_body = Body::new(inlined_cfg.clone());
    // println!("after PRELUDE INSERTION -- {inlined_body}");

    // Build statements for handling returns
    let mut rep = ReplaceReturns {
        ret_assigned_to: stmt.place,
        ret_to_block: after_call_block,
    };
    for block in inlined_cfg.node_weights_mut() {
        rep.visit_basic_block(block, 0.into());
    }

    let inlined_body = Body::new(inlined_cfg.clone());
    // println!("after REPLACE RETURNS -- new cfg {inlined_body}");

    let new_entry = compose_cfg(inlined_cfg, &mut old_cfg, bb_offset);

    // println!("new entry is {new_entry}");

    match old_cfg
        .node_weight_mut(loc.block.into())
        .expect("should be there")
        .terminator
        .kind_mut()
    {
        TerminatorKind::Jump(t) => *t = new_entry,
        _ => panic!("unexpected..."),
    }

    recalculate_cfg_edges(&mut old_cfg);

    let cfg_body = Body::new(old_cfg.clone());
    // println!("inlining {cfg_body}");

    // let body_to_inline = prog.find_function(sym)
    // println!("inlining of {func}");
    func.body = Body::new(old_cfg);

    let new_locals = func
        .locals
        .as_vec()
        .into_iter()
        .chain(inlined_func.locals.as_vec().into_iter().skip(1))
        .copied()
        .collect::<Vec<_>>();
    // println!("inlined locals {:?}", inlined_func.locals.as_vec());
    // println!("old locals {:?}", new_locals);

    func.locals = Arc::new(IndexedDomain::from_iter(new_locals));

    // println!("inlining results in {func}");

    // todo!()
    true
}

/// Inlines `cfg` into `into`, returning the basic block of the entry point.
#[allow(clippy::needless_pass_by_value)]
fn compose_cfg(cfg: Cfg, into: &mut Cfg, bb_offset: usize) -> BasicBlockIdx {
    let cfg_body = Body::new(cfg.clone());
    // println!("inlining {cfg_body}");
    let into_body = Body::new(into.clone());
    // println!("\n\nINTO {into_body}");

    let mut first = None;

    for idx in cfg.node_indices().sorted() {
        let old_idx: BasicBlockIdx = BasicBlockIdx::from(idx);

        let data = cfg.node_weight(idx).expect("should have data").clone();
        // println!("adding idx {old_idx:?} from cfg w/ data {data}");
        let new_idx: BasicBlockIdx = into.add_node(data).into();

        if old_idx == 0 {
            first = Some(new_idx);
        }

        assert_eq!(new_idx, old_idx + bb_offset);

        for n in cfg.neighbors_directed(idx, Outgoing).collect::<Vec<_>>() {
            into.add_edge(idx, n, ());
        }
    }

    let into_body = Body::new(into.clone());
    // println!("\n\n RESULTING IN {into_body}");
    first.expect("should have a first block")
}

fn recalculate_cfg_edges(cfg: &mut Cfg) {
    cfg.clear_edges();

    for idx in cfg.node_indices().collect::<Vec<_>>() {
        let old_idx: BasicBlockIdx = BasicBlockIdx::from(idx);

        let data = cfg.node_weight(idx).expect("should have data");

        match data.terminator.kind().clone() {
            TerminatorKind::Jump(to) => {
                cfg.add_edge(idx, to.into(), ());
            }
            TerminatorKind::CondJump { true_, false_, .. } => {
                cfg.add_edge(idx, true_.into(), ());
                cfg.add_edge(idx, false_.into(), ());
            }
            TerminatorKind::Return(_) => (),
        }
    }
}

fn replace_returns(func: &mut Function, ret_assigned_to: Place, ret_to_block: BasicBlockIdx) {
    let mut rep = ReplaceReturns {
        ret_assigned_to,
        ret_to_block,
    };

    rep.visit_function(func);
}

struct ReplaceReturns {
    ret_assigned_to: Place,
    ret_to_block: BasicBlockIdx,
}

impl VisitMut for ReplaceReturns {
    fn visit_basic_block(&mut self, data: &mut crate::bc::types::BasicBlock, block: BasicBlockIdx) {
        // println!("visiting bb {data}");
        if let TerminatorKind::Return(val_to_ret) = data.terminator.kind().clone() {
            // Add a new statement to set our 'return' value
            data.statements.push(Statement {
                place: self.ret_assigned_to,
                rvalue: Rvalue::Operand(val_to_ret),
                span: Span::DUMMY,
            });

            // Jump to the new block
            data.terminator = Terminator {
                kind: TerminatorKind::Jump(self.ret_to_block),
                span: Span::DUMMY,
            }
        }
    }
}

fn call_setup_stmts(args: &[Operand], to: &Function, local_offset: usize) -> Vec<Statement> {
    let params = to.params().collect::<Vec<_>>();
    // println!("which has args {args:?}, {params:?}");

    to.params()
        .skip(1)
        .zip_eq(args)
        .map(|((local, ty), arg)| call_setup_stmt(local, ty, arg, to, local_offset))
        .collect::<Vec<_>>()
}

fn call_setup_stmt(
    local: LocalIdx,
    ty: Type,
    arg: &Operand,
    to: &Function,
    local_offset: usize,
) -> Statement {
    Statement {
        span: Span::DUMMY,
        place: Place::new(local + local_offset - 1, vec![], ty),
        rvalue: Rvalue::Operand(arg.clone()),
    }
}

fn inlineable_calls<'a>(
    prog: &'a Program,
    func: &Function,
) -> impl Iterator<Item = (Symbol, Location, &'a Function)> {
    let mut v = FnCallVisitor::default();
    v.visit_function(func);
    // println!("{:?}", v.0);
    v.0.into_iter().filter_map(|(sym, loc)| {
        let func = prog.find_function(sym)?;
        if func.jit() || func.secure() || func.dynamic() {
            // Can't inline secure, jit or interface functions
            None
        } else {
            Some((sym, loc, func))
        }
    })
}

#[derive(Debug, Default)]
struct FnCallVisitor(Vec<(Symbol, Location)>);

impl Visit for FnCallVisitor {
    fn visit_rvalue(&mut self, rvalue: &crate::bc::types::Rvalue, loc: Location) {
        if let Rvalue::Call {
            f: Operand::Func { f, ty },
            args,
        } = rvalue
        {
            self.0.push((*f, loc));
        }

        self.super_visit_rvalue(rvalue, loc);
    }
}
