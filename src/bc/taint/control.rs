use std::collections::{HashMap, HashSet};

use crate::bc::types::{BasicBlock, BasicBlockIdx, Body, Function, TerminatorKind};
use itertools::Itertools;
use petgraph::visit::NodeRef;
use petgraph::{Graph, algo::dominators::Dominators, prelude::NodeIndex, visit::EdgeRef};

#[derive(Debug)]
#[allow(dead_code)]
pub struct ControlDependencies(Graph<BasicBlockIdx, ()>);

impl ControlDependencies {
    /// Iterator over all the nodes this one is control dependent on.
    pub fn cdep_on(&self, block: BasicBlockIdx) -> impl Iterator<Item = BasicBlockIdx> {
        println!("cdep on {block}");
        self.0
            .edges_directed(block.into(), petgraph::Direction::Outgoing)
            .flat_map(|edge| {
                let a = edge.target().id().into();
                println!("edge to {a}");
                self.cdep_on(a).chain([a]).collect::<Vec<_>>().into_iter()
            })
    }

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

    fn from_post_dominators(
        pdom: Dominators<NodeIndex>,
        reverse_cfg: &Graph<BlockKind, ()>,
        body: &Body,
    ) -> Self {
        // The blocks a given block is cdep ON.
        let mut cdep: HashMap<NodeIndex, HashSet<NodeIndex>> = HashMap::new();

        for x in body.blocks() {
            let x = x.into();
            for goes_to_me in reverse_cfg.neighbors_directed(x, petgraph::Outgoing) {
                if !pdom
                    .dominators(goes_to_me)
                    .expect("should have pdom")
                    .contains(&x)
                {
                    // println!("{x:?} cdep on {goes_to_me:?} -- by direct");
                    cdep.entry(x).or_default().insert(goes_to_me);
                }

                for z in pdom.immediately_dominated_by(x) {
                    // println!("\t{z:?} is immediately pdom by {x:?}");
                    for y in cdep.get(&z).unwrap_or(&HashSet::new()).clone() {
                        // println!("\t\twhich is cdep on {y:?}");
                        if !pdom
                            .dominators(y)
                            .expect("should have dominators")
                            .contains(&x)
                        {
                            // println!("{x:?} cdep on {y:?} -- by way of {z:?}");
                            cdep.entry(x).or_default().insert(y);
                        }
                    }
                }
            }
        }

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
    // println!("reverse cfg is {:?}", reverse_cfg);

    // 2. post dominator tree
    let post_dominators = petgraph::algo::dominators::simple_fast(&reverse_cfg, return_node);

    // println!("post dominators are {:?}", post_dominators);

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
