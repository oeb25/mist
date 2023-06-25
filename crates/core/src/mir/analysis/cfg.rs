use std::fmt;

use petgraph::{algo::dominators::Dominators, visit::IntoNodeIdentifiers, Direction};
use tracing::warn;

use crate::{
    mir::{Terminator, TerminatorKind},
    util::IdxMap,
};

use super::{
    monotone::{AnalysisResults, MonotoneFramework},
    *,
};

#[derive(Debug, Default)]
pub struct Cfg {
    nodes: IdxMap<BlockId, NodeIndex>,
    graph: Graph<BlockId, Terminator>,
}

#[derive(new, Debug)]
struct CfgBuilder<'a> {
    body: &'a Body,
    #[new(default)]
    cfg: Cfg,
}

impl Cfg {
    pub fn compute(db: &dyn crate::Db, body: &Body) -> Cfg {
        CfgBuilder::new(body).finish(db)
    }
    fn bid_to_node(&mut self, bid: BlockId) -> NodeIndex {
        *self.nodes.entry(bid).or_insert_with(|| self.graph.add_node(bid))
    }
    /// Construct a graph where the nodes and edge labes are replaced for
    /// serializations for their value
    pub fn pretty(&self, db: &dyn crate::Db, body: &Body) -> Graph<String, String> {
        let fmt_node = |n: BlockId| serialize::serialize_block(serialize::Color::No, db, body, n);
        self.map_graph(fmt_node, |e| {
            serialize::serialize_terminator(serialize::Color::No, db, body, e)
        })
    }
    pub fn analysis_dot<A: MonotoneFramework>(
        &self,
        body: &Body,
        result: &AnalysisResults<A>,
        fmt: impl Fn(&A::Domain) -> String,
    ) -> String
    where
        A::Domain: fmt::Debug,
    {
        let g = self.map_graph(|bid| fmt(result.value_at(bid.first_body_loc(body))), |_| "");
        petgraph::dot::Dot::new(&g).to_string()
    }
    pub fn map_graph<V, E>(
        &self,
        mut f: impl FnMut(BlockId) -> V,
        mut g: impl FnMut(Terminator) -> E,
    ) -> Graph<V, E> {
        self.graph.map(|_, &bid| f(bid), |_, &term| g(term))
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
            if self.graph.neighbors_directed(n, Direction::Outgoing).next().is_none() {
                break Some(n);
            }
        })
    }
    /// Computes the dominators for each block reachable from `entry`
    pub fn dominators(&self, entry: BlockId) -> IdxMap<BlockId, BlockId> {
        let dominators = petgraph::algo::dominators::simple_fast(&self.graph, self.nodes[entry]);

        let mut result = IdxMap::with_capacity(self.graph.node_count());
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

        let mut relation = IdxMap::with_capacity(reverse_graph.node_count());
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
        let mut relation = IdxMap::new();
        for (n, rest) in f.into_iter().sorted() {
            relation.insert(
                *reverse_graph.node_weight(n).unwrap(),
                rest.iter().map(|&m| *reverse_graph.node_weight(m).unwrap()).collect(),
            );
        }
        PostdominanceFrontier { relation }
    }
    /// Construct the DOT represenation of the CFG
    pub fn dot(&self, db: &dyn crate::Db, body: &Body) -> String {
        petgraph::dot::Dot::new(&self.pretty(db, body)).to_string()
    }
    /// Perform a DFS over all the reachable nodes from `entry`
    pub fn visit_dfs(&self, entry: BlockId, mut f: impl FnMut(BlockId)) {
        let mut dfs = petgraph::visit::Dfs::new(&self.graph, self.nodes[entry]);
        while let Some(b) = dfs.next(&self.graph) {
            f(*self.graph.node_weight(b).unwrap());
        }
    }
    /// Perform a reverse post-order over all the reachable nodes from `entry`
    pub fn visit_reverse_post_order(&self, entry: BlockId, mut f: impl FnMut(BlockId)) {
        let mut dfs = petgraph::visit::DfsPostOrder::new(&self.graph, self.nodes[entry]);
        let mut order = vec![];
        while let Some(n) = dfs.next(&self.graph) {
            order.push(n);
        }
        for n in order.into_iter().rev() {
            f(*self.graph.node_weight(n).unwrap());
        }
    }
    /// Perform a post-order over all the reachable nodes from `entry`
    pub fn direct_predecessors(&self, bid: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.graph
            .neighbors_directed(self.nodes[bid], Direction::Incoming)
            .map(|n| *self.graph.node_weight(n).unwrap())
    }

    pub fn scc(&self) -> impl Iterator<Item = StronglyConnectedComponent> + '_ {
        petgraph::algo::tarjan_scc(&self.graph).into_iter().filter_map(|nodes| {
            if nodes.len() == 1 {
                return None;
            }

            let blocks =
                nodes.into_iter().map(|n| *self.graph.node_weight(n).unwrap()).collect_vec();
            Some(StronglyConnectedComponent {
                entry: *blocks.last().unwrap(),
                exit: *blocks.last().unwrap(),
                blocks,
            })
        })
    }
}

fn frontiers(g: &Graph<BlockId, Terminator>, e: NodeIndex) -> HashMap<NodeIndex, Vec<NodeIndex>> {
    let dominators: Dominators<NodeIndex> = petgraph::algo::dominators::simple_fast(g, e);

    let mut frontiers =
        HashMap::<NodeIndex, Vec<NodeIndex>>::from_iter(g.node_identifiers().map(|v| (v, vec![])));

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
                        if let Some(r) = dominators.immediate_dominator(runner) {
                            runner = r;
                        } else {
                            warn!("node {} has no frontier", g.node_weight(node).unwrap());
                            break;
                        }
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
    fn finish(mut self, db: &dyn crate::Db) -> Cfg {
        for bid in self.body.blocks() {
            let nid = self.cfg.bid_to_node(bid);
            if let Some(term) = bid.terminator(self.body) {
                match term.kind(db) {
                    TerminatorKind::Return => {}
                    TerminatorKind::Quantify(_, _, next) => {
                        let next_nid = self.cfg.bid_to_node(*next);
                        self.cfg.graph.add_edge(nid, next_nid, term);
                    }
                    TerminatorKind::QuantifyEnd(next) => {
                        let next_nid = self.cfg.bid_to_node(*next);
                        self.cfg.graph.add_edge(nid, next_nid, term);
                    }
                    TerminatorKind::Goto(next) => {
                        let next_nid = self.cfg.bid_to_node(*next);
                        self.cfg.graph.add_edge(nid, next_nid, term);
                    }
                    TerminatorKind::Switch(_, s) => {
                        let (targets, otherwise) = s.targets();
                        for t in targets {
                            let t_nid = self.cfg.bid_to_node(t);
                            self.cfg.graph.add_edge(nid, t_nid, term);
                        }
                        let t_nid = self.cfg.bid_to_node(otherwise);
                        self.cfg.graph.add_edge(nid, t_nid, term);
                    }
                    TerminatorKind::Call { target, .. } => {
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
    relation: IdxMap<BlockId, BlockId>,
}

impl Postdominators {
    pub fn get(&self, index: BlockId) -> Option<BlockId> {
        self.relation.get(index).copied()
    }
    pub fn merge(&mut self, other: &Postdominators) {
        for (k, v) in other.relation.iter() {
            if self.relation.insert(k, *v).is_some() {
                todo!();
            }
        }
    }
}

impl std::ops::Index<BlockId> for Postdominators {
    type Output = BlockId;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.relation[index]
    }
}

#[derive(Debug, Default, Clone)]
pub struct PostdominanceFrontier {
    relation: IdxMap<BlockId, Vec<BlockId>>,
}
impl PostdominanceFrontier {
    pub fn merge(&mut self, other: &PostdominanceFrontier) {
        for (k, v) in other.relation.iter() {
            if self.relation.insert(k, v.clone()).is_some() {}
        }
    }
}

impl std::ops::Index<BlockId> for PostdominanceFrontier {
    type Output = [BlockId];

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.relation[index]
    }
}

#[derive(Debug, Clone)]
pub struct StronglyConnectedComponent {
    entry: BlockId,
    exit: BlockId,
    blocks: Vec<BlockId>,
}

impl StronglyConnectedComponent {
    pub fn entry(&self) -> BlockId {
        self.entry
    }

    pub fn exit(&self) -> BlockId {
        self.exit
    }

    pub fn blocks(&self) -> &[BlockId] {
        self.blocks.as_ref()
    }
}
