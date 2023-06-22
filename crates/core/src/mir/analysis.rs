use std::collections::HashMap;

use derive_new::new;
use itertools::Itertools;
use petgraph::{stable_graph::NodeIndex, Graph};

pub use petgraph;

use super::{serialize, BlockId, Body};

pub mod cfg;
pub mod folding_forrest;
pub mod liveness;
pub mod monotone;

pub fn pretty_dot<N, E>(g: &Graph<N, E>) -> String
where
    N: std::fmt::Display,
    E: std::fmt::Display,
{
    petgraph::dot::Dot::with_config(g, &[]).to_string()
}
