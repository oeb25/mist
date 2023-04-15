use std::collections::HashMap;

use derive_more::Display;
use derive_new::new;
use itertools::Itertools;
use petgraph::{
    data::Build,
    dot::Config,
    stable_graph::NodeIndex,
    visit::{depth_first_search, Control, DfsEvent},
    Graph,
};

pub use petgraph;

use crate::hir;

use super::{serialize, BlockId, Body, Instruction, MExpr, Slot, SlotId};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Edge {
    // #[display(fmt = "")]
    DirectUsage,
    // #[display(fmt = "?{_0}")]
    Condition(NodeIndex),
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub enum Node {
    Slot { id: SlotId },
    Branch { id: SlotId, success: bool },
    Construct { expr: MExpr },
}

// impl std::fmt::Display for Node {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Node::Slot { id, slot } => match &slot {
//                 Slot::Temp => write!(f, "%{}", id.into_raw()),
//                 Slot::Var(v) => write!(f, "%{}_", id.into_raw()),
//                 Slot::Literal(l) => write!(f, "${l}"),
//                 Slot::Result => write!(f, "%result"),
//             },
//             Node::Branch { id, slot } => {
//                 write!(f, "? ")?;
//                 match &slot {
//                     Slot::Temp => write!(f, "%{}", id.into_raw()),
//                     Slot::Var(v) => write!(f, "%{}_", id.into_raw()),
//                     Slot::Literal(l) => write!(f, "${l}"),
//                     Slot::Result => write!(f, "%result"),
//                 }
//             }
//             Node::Construct { expr } => write!(f, "{expr:?}"),
//         }
//     }
// }

#[derive(Debug, Default)]
pub struct Dataflow {
    nodes: HashMap<Node, NodeIndex>,
    graph: Graph<Node, Edge>,
}

#[derive(new, Debug)]
struct DataflowBuilder<'a> {
    body: &'a Body,
    #[new(default)]
    df: Dataflow,
}

pub fn compute_dataflow(body: &Body) -> Dataflow {
    let mut builder = DataflowBuilder::new(body);

    if let Some(bid) = body.body_block() {
        builder.block(&[], bid);
    }

    builder.df
}

impl DataflowBuilder<'_> {
    fn slot_node(&mut self, id: SlotId) -> NodeIndex {
        let node = Node::Slot { id };
        self.node(node)
    }
    fn node(&mut self, node: Node) -> NodeIndex {
        *self
            .df
            .nodes
            .entry(node)
            .or_insert_with_key(|node| self.df.graph.add_node(node.clone()))
    }
    fn block(&mut self, edge: &[NodeIndex], block: BlockId) {
        for inst in &self.body[block].instructions {
            match &self.body[inst] {
                Instruction::Assign(target, expr) => {
                    let t_node = self.slot_node(*target);
                    let c_node = self.node(Node::Construct { expr: expr.clone() });
                    if edge.is_empty() {
                        self.df.graph.add_edge(t_node, c_node, Edge::DirectUsage);
                    } else {
                        for &condition_node in edge {
                            self.df
                                .graph
                                .add_edge(t_node, condition_node, Edge::Condition(c_node));
                            self.df
                                .graph
                                .add_edge(condition_node, c_node, Edge::DirectUsage);
                        }
                    }

                    for slot in expr.all_slot_usages() {
                        let s_node = self.slot_node(slot);
                        // if !self.df.graph.contains_edge(t_node, s_node) {
                        self.df.graph.add_edge(c_node, s_node, Edge::DirectUsage);
                        // }
                    }
                }
                Instruction::If(cond, then_block, else_block) => {
                    let true_node = Node::Branch {
                        id: *cond,
                        success: true,
                    };
                    let false_node = Node::Branch {
                        id: *cond,
                        success: false,
                    };
                    let true_node_idx = self.node(true_node.clone());
                    let false_node_idx = self.node(false_node.clone());
                    let cond_slot_node = self.slot_node(*cond);
                    self.df
                        .graph
                        .add_edge(true_node_idx, cond_slot_node, Edge::DirectUsage);
                    self.df
                        .graph
                        .add_edge(false_node_idx, cond_slot_node, Edge::DirectUsage);
                    self.block(
                        &edge.iter().copied().chain([true_node_idx]).collect_vec(),
                        *then_block,
                    );
                    self.block(
                        &edge.iter().copied().chain([false_node_idx]).collect_vec(),
                        *else_block,
                    );
                }
                Instruction::While(_, _, _) => {}
                Instruction::Assertion(_, _) => {}
                Instruction::Call(_, _) => {}
                Instruction::Return => {}
            }
        }
    }
}
impl Dataflow {
    pub fn node(&self, body: &Body, id: SlotId) -> Option<NodeIndex> {
        let node = Node::Slot { id };
        self.nodes.get(&node).copied()
    }
    pub fn graph(&self) -> &Graph<Node, Edge> {
        &self.graph
    }
    //     pub fn dot(&self) -> String {
    //         let dot = petgraph::dot::Dot::with_config(&self.graph, &[Config::GraphContentOnly]);

    //         format!(
    //             "digraph {{
    //     margin=0.75
    //     bgcolor=\"#ffffff00\"
    //     color=white
    //     fontcolor=white
    //     node [color=white, fontcolor=white]
    //     edge [color=white, fontcolor=white]
    // {dot}}}"
    //         )
    //     }
    pub fn flow_from(&self, body: &Body, s: SlotId) -> Option<(NodeIndex, Graph<Node, Edge>)> {
        let mut new_g = self.graph.clone();
        let start_node = self.node(body, s)?;
        let mut back_edges = vec![];
        depth_first_search(&new_g, [start_node], |event| -> Control<()> {
            match event {
                DfsEvent::Discover(_, t) => Control::Continue,
                DfsEvent::TreeEdge(_, _) => Control::Continue,
                DfsEvent::BackEdge(a, b) => {
                    // back_edges.push((a, b));
                    Control::Continue
                }
                DfsEvent::CrossForwardEdge(_, _) => Control::Continue,
                DfsEvent::Finish(_, _) => Control::Continue,
            }
        });
        for (a, b) in back_edges {
            let eid = new_g.find_edge(a, b).unwrap();
            let e = new_g.remove_edge(eid).unwrap();
            match e {
                Edge::DirectUsage => {}
                Edge::Condition(through) => {
                    new_g.add_edge(a, through, Edge::DirectUsage);
                }
            }
        }
        Some((start_node, new_g))
    }
}
pub fn pretty_dot<N, E>(g: &Graph<N, E>) -> String
where
    N: std::fmt::Display,
    E: std::fmt::Display,
{
    petgraph::dot::Dot::with_config(g, &[]).to_string()
}
pub fn pretty_graph(
    db: &dyn crate::Db,
    program: hir::Program,
    cx: &hir::ItemContext,
    body: &Body,
    g: &Graph<Node, Edge>,
) -> Graph<String, String> {
    let fmt_node = |n: &Node| match n {
        Node::Slot { id } => serialize::serialize_slot(db, program, cx, body, *id),
        Node::Branch { id, success } => {
            let s = serialize::serialize_slot(db, program, cx, body, *id);
            if *success {
                format!("? {s}")
            } else {
                format!("! {s}")
            }
        }
        Node::Construct { expr } => expr.serialize(db, program, cx, body),
    };
    g.map(
        |_idx, n| fmt_node(n),
        |_idx, e| match e {
            Edge::DirectUsage => "".to_string(),
            Edge::Condition(e) => fmt_node(g.node_weight(*e).unwrap()),
        },
    )
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
        }
    }
}
