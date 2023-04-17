use std::collections::HashMap;

use derive_new::new;
use itertools::Itertools;
use petgraph::{stable_graph::NodeIndex, Graph};

pub use petgraph;

use crate::hir;

use super::{serialize, BlockId, Body, MExpr, SlotId};

pub mod cfg {
    use la_arena::ArenaMap;
    use petgraph::{algo::dominators::Dominators, visit::IntoNodeIdentifiers, Direction};

    use crate::mir::Terminator;

    use super::*;

    #[derive(Debug, Default)]
    pub struct Cfg {
        nodes: ArenaMap<BlockId, NodeIndex>,
        graph: Graph<BlockId, Terminator>,
    }

    #[derive(new, Debug)]
    struct CfgBuilder<'a> {
        body: &'a Body,
        #[new(default)]
        cfg: Cfg,
    }

    impl Cfg {
        pub fn compute(body: &Body) -> Cfg {
            CfgBuilder::new(body).finish()
        }
        fn bid_to_node(&mut self, bid: BlockId) -> NodeIndex {
            *self
                .nodes
                .entry(bid)
                .or_insert_with(|| self.graph.add_node(bid))
        }
        pub fn pretty(
            &self,
            db: &dyn crate::Db,
            cx: &hir::ItemContext,
            body: &Body,
        ) -> Graph<String, String> {
            let fmt_node =
                |n: &BlockId| serialize::serialize_block(serialize::Color::No, db, cx, body, *n);
            self.graph.map(
                |_idx, n| fmt_node(n),
                |_idx, e| serialize::serialize_terminator(serialize::Color::No, db, cx, body, e),
            )
        }
        #[allow(dead_code)]
        fn exit_nodes(&self) -> impl Iterator<Item = NodeIndex> + '_ {
            self.graph.externals(Direction::Outgoing)
        }
        fn exit_nodes_for(&self, entry: BlockId) -> impl Iterator<Item = NodeIndex> + '_ {
            let start = self.nodes[entry];
            let mut dfs = petgraph::visit::Dfs::new(&self.graph, start);
            std::iter::from_fn(move || loop {
                let n = dfs.next(&self.graph)?;
                if self
                    .graph
                    .neighbors_directed(n, Direction::Outgoing)
                    .next()
                    .is_none()
                {
                    break Some(n);
                }
            })
        }
        /// Computes the dominators for each block reachable from `entry`
        pub fn dominators(&self, entry: BlockId) -> ArenaMap<BlockId, BlockId> {
            let dominators =
                petgraph::algo::dominators::simple_fast(&self.graph, self.nodes[entry]);

            let mut result = ArenaMap::with_capacity(self.graph.node_count());
            for &n in self.graph.node_weights() {
                let Some(d) = dominators.immediate_dominator(self.nodes[n]) else { continue };
                result.insert(n, *self.graph.node_weight(d).unwrap());
            }
            result
        }
        /// Computes the postdominators for each block reachable from `entry`
        pub fn postdominators(&self, entry: BlockId) -> Postdominators {
            let mut reverse_graph = self.graph.clone();
            reverse_graph.reverse();
            let dominators = petgraph::algo::dominators::simple_fast(
                &reverse_graph,
                self.exit_nodes_for(entry).next().unwrap(),
            );

            let mut relation = ArenaMap::with_capacity(reverse_graph.node_count());
            for &n in reverse_graph.node_weights() {
                let Some(d) = dominators.immediate_dominator(self.nodes[n]) else { continue };
                relation.insert(n, *reverse_graph.node_weight(d).unwrap());
            }
            Postdominators { relation }
        }
        /// Computes the postdominance frontier for each block reachable from `entry`
        pub fn postdominance_frontier(&self, entry: BlockId) -> PostdominanceFrontier {
            let mut reverse_graph = self.graph.clone();
            reverse_graph.reverse();
            let f = frontiers(&reverse_graph, self.exit_nodes_for(entry).next().unwrap());
            let mut relation = ArenaMap::new();
            for (n, rest) in f.into_iter().sorted() {
                relation.insert(
                    *reverse_graph.node_weight(n).unwrap(),
                    rest.iter()
                        .map(|&m| *reverse_graph.node_weight(m).unwrap())
                        .collect(),
                );
            }
            PostdominanceFrontier { relation }
        }
        pub fn dot(&self, db: &dyn crate::Db, cx: &hir::ItemContext, body: &Body) -> String {
            petgraph::dot::Dot::new(&self.pretty(db, cx, body)).to_string()
        }
    }

    fn frontiers(
        g: &Graph<BlockId, Terminator>,
        e: NodeIndex,
    ) -> HashMap<NodeIndex, Vec<NodeIndex>> {
        let dominators: Dominators<NodeIndex> = petgraph::algo::dominators::simple_fast(g, e);

        let mut frontiers = HashMap::<NodeIndex, Vec<NodeIndex>>::from_iter(
            g.node_identifiers().map(|v| (v, vec![])),
        );

        for node in g.node_identifiers() {
            let (predecessors, predecessors_len) = {
                let ret = g.neighbors_directed(node, Direction::Incoming);
                let count = ret.clone().count();
                (ret, count)
            };

            if predecessors_len >= 2 {
                for p in predecessors {
                    let mut runner = p;

                    if let Some(dominator) = dominators.immediate_dominator(node) {
                        while runner != dominator {
                            frontiers.entry(runner).or_insert(vec![]).push(node);
                            runner = dominators.immediate_dominator(runner).unwrap();
                        }
                    }
                }
                for (_, frontier) in frontiers.iter_mut() {
                    frontier.sort();
                    frontier.dedup();
                }
            }
        }
        frontiers
    }

    impl<'a> CfgBuilder<'a> {
        fn finish(mut self) -> Cfg {
            for (bid, b) in self.body.blocks.iter() {
                let nid = self.cfg.bid_to_node(bid);
                if let Some(term) = b.terminator.clone() {
                    match &term {
                        Terminator::Return => {}
                        Terminator::Goto(next) => {
                            let next_nid = self.cfg.bid_to_node(*next);
                            self.cfg.graph.add_edge(nid, next_nid, term);
                        }
                        Terminator::Switch(_, s) => {
                            for t in s.targets.values() {
                                let t_nid = self.cfg.bid_to_node(*t);
                                self.cfg.graph.add_edge(nid, t_nid, term.clone());
                            }
                            let t_nid = self.cfg.bid_to_node(s.otherwise);
                            self.cfg.graph.add_edge(nid, t_nid, term.clone());
                        }
                        Terminator::Call { target, .. } => {
                            if let Some(next) = target {
                                let next_nid = self.cfg.bid_to_node(*next);
                                self.cfg.graph.add_edge(nid, next_nid, term);
                            }
                        }
                    }
                }
            }
            self.cfg
        }
    }

    #[derive(Debug, Default, Clone)]
    pub struct Postdominators {
        relation: ArenaMap<BlockId, BlockId>,
    }

    impl std::ops::Index<BlockId> for Postdominators {
        type Output = BlockId;

        fn index(&self, index: BlockId) -> &Self::Output {
            &self.relation[index]
        }
    }

    #[derive(Debug, Default, Clone)]
    pub struct PostdominanceFrontier {
        relation: ArenaMap<BlockId, Vec<BlockId>>,
    }

    impl std::ops::Index<BlockId> for PostdominanceFrontier {
        type Output = [BlockId];

        fn index(&self, index: BlockId) -> &Self::Output {
            &self.relation[index]
        }
    }

    /// Pipes the `dot` string generated into PNG into
    /// [imgcat](https://iterm2.com/documentation-images.html)
    ///
    /// `dot -T png | imgcat`
    pub fn dot_imgcat(dot: String) {
        use std::{
            io::Write,
            process::{Command, Stdio},
        };

        let dot_cmd = Command::new("dot")
            .args([
                "-Gmargin=0.7",
                "-Gbgcolor=#ffffff00",
                "-Gcolor=white",
                "-Gfontcolor=white",
                "-Gfontname=FiraCode NFM",
                "-Ncolor=white",
                "-Nfontcolor=white",
                "-Nfontname=FiraCode NFM",
                "-Ecolor=white",
                "-Efontcolor=white",
                "-Efontname=FiraCode NFM",
            ])
            .args(["-T", "png"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let imgcat = Command::new("imgcat")
            .stdin(Stdio::from(dot_cmd.stdout.unwrap()))
            .stdout(Stdio::inherit())
            .spawn()
            .unwrap();

        dot_cmd.stdin.unwrap().write_all(dot.as_bytes()).unwrap();

        imgcat.wait_with_output().unwrap();
    }
}

pub fn pretty_dot<N, E>(g: &Graph<N, E>) -> String
where
    N: std::fmt::Display,
    E: std::fmt::Display,
{
    petgraph::dot::Dot::with_config(g, &[]).to_string()
}

impl MExpr {
    pub fn all_slot_usages(&self) -> impl IntoIterator<Item = SlotId> {
        match self {
            MExpr::Literal(_) => vec![],
            MExpr::Call(_, args) => args.clone(),
            MExpr::Field(e, _) => vec![*e],
            MExpr::Struct(_, fields) => fields.iter().map(|f| f.1).collect(),
            MExpr::Slot(s) => vec![*s],
            // TODO
            MExpr::Quantifier(_, _, _, _) => vec![],
            MExpr::BinaryOp(_, l, r) => vec![*l, *r],
            MExpr::UnaryOp(_, o) => vec![*o],
        }
    }
}
