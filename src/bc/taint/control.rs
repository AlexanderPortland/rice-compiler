use std::collections::{HashMap, HashSet};

use crate::bc::types::{BasicBlock, BasicBlockIdx, Body, Function, TerminatorKind};
use itertools::Itertools;
use petgraph::{Graph, algo::dominators::Dominators, prelude::NodeIndex};

#[derive(Debug)]
#[allow(dead_code)]
pub struct ControlDependencies(Graph<BasicBlockIdx, ()>);

impl ControlDependencies {
    fn from_map(map: HashMap<NodeIndex, HashSet<NodeIndex>>, body: &Body) -> Self {
        let mut g = Graph::new();
        for i in body.blocks() {
            g.add_node(i);
        }

        for (idx, cdep_on) in map {
            for cdep_on in cdep_on {
                g.add_edge(idx, cdep_on, ());
            }
        }

        ControlDependencies(g)
    }

    fn from_post_dominators<'a>(
        pdom: Dominators<NodeIndex>,
        reverse_cfg: &Graph<BlockKind, ()>,
        // return_block_idx: &NodeIndex,
        body: &Body,
    ) -> Self {
        // let a = reverse_post_order(g, entry)

        // The blocks a given block is cdep ON.
        let mut cdep: HashMap<NodeIndex, HashSet<NodeIndex>> = HashMap::new();

        // TODO: should maybe have an order thing here...
        for x in body.blocks() {
            let x = x.into();
            for goes_to_me in reverse_cfg.neighbors_directed(x, petgraph::Outgoing) {
                if !pdom
                    .dominators(goes_to_me)
                    .expect("should have pdom")
                    .contains(&x)
                {
                    // let goes_to_me = reverse_cfg[goes_to_me]
                    //     .block_idx()
                    //     .expect("should have idx");
                    println!("{x:?} cdep on {goes_to_me:?} -- by direct");
                    cdep.entry(x.into()).or_default().insert(goes_to_me);
                }

                for z in pdom.immediately_dominated_by(x) {
                    println!("\t{z:?} is immediately pdom by {x:?}");
                    for y in cdep.get(&z).unwrap_or(&HashSet::new()).clone() {
                        println!("\t\twhich is cdep on {y:?}");
                        if !pdom
                            .dominators(y)
                            .expect("should have dominators")
                            .contains(&x)
                        {
                            println!("{x:?} cdep on {y:?} -- by way of {z:?}");
                            cdep.entry(x.into()).or_default().insert(y);
                        }
                    }
                }
            }
        }

        // let bb_from_idx = |idx: NodeIndex| BasicBlockIdx::from(idx);

        // let cdep = cdep
        //     .into_iter()
        //     .map(|(key_idx, val)| {
        //         (
        //             bb_from_idx(key_idx),
        //             val.into_iter()
        //                 .map(|val_idx| bb_from_idx(val_idx))
        //                 .collect(),
        //         )
        //     })
        //     .collect();

        ControlDependencies::from_map(cdep, body)
    }
}

#[derive(Debug)]
enum BlockKind {
    Basic(BasicBlock, BasicBlockIdx),
    ReturnBlock,
}

pub fn control_dependencies(func: &Function) -> ControlDependencies {
    let (mut cfg, return_node) = cfg_w_shared_return(func);

    // 1. calculate the reverse CFG
    cfg.reverse();
    let reverse_cfg = cfg;
    println!("reverse cfg is {:?}", reverse_cfg);

    // 2. post dominator tree
    let post_dominators = petgraph::algo::dominators::simple_fast(&reverse_cfg, return_node);

    println!("post dominators are {:?}", post_dominators);

    ControlDependencies::from_post_dominators(post_dominators, &reverse_cfg, &func.body)
}

fn cfg_w_shared_return(func: &Function) -> (Graph<BlockKind, ()>, NodeIndex) {
    let mut cfg = func.body.cfg().map(
        |i, b| BlockKind::Basic(b.clone(), i.into()),
        |_, edge| *edge,
    );
    let return_node = cfg.add_node(BlockKind::ReturnBlock);

    for block in cfg.node_indices() {
        if let BlockKind::Basic(bb, _idx) = &cfg[block]
            && let TerminatorKind::Return(_) = bb.terminator.kind()
        {
            cfg.add_edge(block, return_node, ());
        }
    }

    (cfg, return_node)
}
