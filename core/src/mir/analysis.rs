use std::collections::HashMap;

use derive_new::new;
use itertools::Itertools;
use petgraph::{stable_graph::NodeIndex, Graph};

pub use petgraph;

use crate::hir;

use super::{serialize, BlockId, Body, MExpr, Operand, Place, SlotId};

pub mod cfg;
mod folding_tree;
pub mod isorecursive;
pub mod liveness;
mod monotone;

pub fn pretty_dot<N, E>(g: &Graph<N, E>) -> String
where
    N: std::fmt::Display,
    E: std::fmt::Display,
{
    petgraph::dot::Dot::with_config(g, &[]).to_string()
}

impl MExpr {
    pub fn all_slot_usages(&self) -> impl IntoIterator<Item = SlotId> + '_ {
        match self {
            MExpr::Struct(_, fields) => fields.iter().filter_map(|f| f.1.slot()).collect(),
            MExpr::Use(s) => s.slot().into_iter().collect(),
            MExpr::BinaryOp(_, l, r) => l.slot().into_iter().chain(r.slot()).collect(),
            MExpr::Ref(_, p) => vec![p.slot],
            MExpr::UnaryOp(_, o) => o.slot().into_iter().collect(),
        }
    }
    pub fn all_operands(&self) -> impl IntoIterator<Item = &Operand> {
        match self {
            MExpr::Struct(_, fields) => fields.iter().map(|f| &f.1).collect(),
            MExpr::Use(s) => vec![s],
            MExpr::BinaryOp(_, l, r) => vec![l, r],
            MExpr::Ref(_, _) => vec![],
            MExpr::UnaryOp(_, o) => vec![o],
        }
    }
    pub fn places(&self) -> impl Iterator<Item = Place> + '_ {
        self.all_operands().into_iter().filter_map(|o| o.place())
    }
}
