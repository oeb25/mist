#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use petgraph::{visit::Control, Direction};

use crate::mono::exprs::VariableDeclaration;

use super::{
    exprs::{ExprData, ExprPtr, StatementData},
    types::{Type, TypeData},
    Condition, Item, ItemKind, Monomorphized,
};

#[derive(Debug)]
pub struct MonoDep {
    nodes: HashMap<Item, petgraph::graph::NodeIndex>,
    graph: petgraph::Graph<Item, Level>,
}

impl MonoDep {
    pub fn dot(&self, db: &dyn crate::Db) -> String {
        let g = self.graph.map(|_, it| it.name(db), |_, l| l.to_string());
        petgraph::dot::Dot::new(&g).to_string()
    }
    pub fn components(&self) -> Vec<MonoComponent> {
        let g = self.graph.filter_map(
            |_, n| Some(*n),
            |_, e| match e {
                Level::Signature => Some(e),
                Level::Body => None,
            },
        );
        petgraph::algo::kosaraju_scc(&g)
            .into_iter()
            .map(|ns| {
                let items = ns.iter().map(|n| *g.node_weight(*n).unwrap()).collect_vec();
                MonoComponent { items, soft: vec![] }
            })
            .collect()
    }
    pub fn clusters(&self) -> Vec<MonoComponent> {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        struct Key(u32);
        impl ena::unify::UnifyKey for Key {
            type Value = ();

            fn index(&self) -> u32 {
                self.0
            }

            fn from_index(u: u32) -> Self {
                Self(u)
            }

            fn tag() -> &'static str {
                "ClusterKey"
            }
        }

        type Table = ena::unify::InPlaceUnificationTable<Key>;
        let mut clusters = Table::new();
        let mut keys = HashMap::new();
        let mut back = HashMap::new();
        let mut key = |clusters: &mut Table, n: petgraph::graph::NodeIndex| {
            let item = *self.graph.node_weight(n).unwrap();
            let id = *keys.entry(item).or_insert_with(|| clusters.new_key(()));
            back.insert(id, item);
            id
        };

        petgraph::visit::depth_first_search(
            &self.graph,
            self.graph.node_indices(),
            |event| -> Control<()> {
                match event {
                    petgraph::visit::DfsEvent::Discover(n, _) => {
                        key(&mut clusters, n);
                        Control::Continue
                    }
                    petgraph::visit::DfsEvent::Finish(_, _) => Control::Continue,
                    petgraph::visit::DfsEvent::TreeEdge(a, b)
                    | petgraph::visit::DfsEvent::BackEdge(a, b)
                    | petgraph::visit::DfsEvent::CrossForwardEdge(a, b) => {
                        let e = self.graph.edges_connecting(a, b).next().unwrap();
                        match e.weight() {
                            Level::Signature => {
                                let a = key(&mut clusters, a);
                                let b = key(&mut clusters, b);
                                clusters.unify_var_var(a, b).unwrap();
                                Control::Continue
                            }
                            Level::Body => Control::Prune,
                        }
                    }
                }
            },
        );

        let mut result: HashMap<_, Vec<_>> = HashMap::new();
        for (&item, &id) in keys.iter() {
            let g_id = clusters.find(id);
            result.entry(back[&g_id]).or_default().push(item);
        }
        result
            .values()
            .cloned()
            .map(|items| {
                let soft = items
                    .iter()
                    .flat_map(|item| {
                        self.graph
                            .neighbors_directed(self.nodes[item], Direction::Outgoing)
                            .filter_map(|n| {
                                let inner_item = *self.graph.node_weight(n).unwrap();
                                if items.contains(&inner_item) {
                                    None
                                } else {
                                    let id = keys[&inner_item];
                                    let g_id = clusters.find(id);
                                    Some(result[&back[&g_id]].clone())
                                }
                            })
                            .flatten()
                            .collect_vec()
                    })
                    .sorted()
                    .dedup()
                    .collect();
                MonoComponent { items, soft }
            })
            .collect()
    }
}

pub struct MonoComponent {
    pub items: Vec<Item>,
    pub soft: Vec<Item>,
}

impl Monomorphized {
    pub fn dep(self, db: &dyn crate::Db) -> MonoDep {
        let queue: Vec<Queue> = self.items(db).into_iter().map(Queue::Item).collect_vec();
        let computed: HashSet<Queue> = queue.iter().copied().collect();
        let mut gb =
            GraphBuilder { nodes: Default::default(), g: Default::default(), queue, computed };
        gb.work(db);
        gb.finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, derive_more::Display)]
pub enum Level {
    #[display(fmt = "sig")]
    Signature,
    #[display(fmt = "bod")]
    Body,
}

struct GraphBuilder {
    nodes: HashMap<Item, petgraph::graph::NodeIndex>,
    g: petgraph::Graph<Item, Level>,

    queue: Vec<Queue>,
    computed: HashSet<Queue>,
}
impl GraphBuilder {
    /// Adds a dependency to `b` from `a`
    fn dep(&mut self, a: Item, b: Item, level: Level) {
        let a = self.add_node(a);
        let b = self.add_node(b);
        self.g.add_edge(a, b, level);
    }

    fn add_node(&mut self, a: Item) -> petgraph::graph::NodeIndex {
        *self.nodes.entry(a).or_insert_with(|| self.g.add_node(a))
    }

    fn queue(&mut self, qi: Queue) {
        if self.computed.insert(qi) {
            self.queue.push(qi);
        } else {
            // Nothing...
        }
    }

    fn work(&mut self, db: &dyn crate::Db) {
        while let Some(it) = self.queue.pop() {
            match it {
                Queue::Item(it) => {
                    self.add_node(it);
                    match it.kind(db) {
                        ItemKind::Adt(adt) => {
                            for ty in adt.generic_args(db) {
                                self.queue(Queue::Type(it, true, Level::Signature, *ty));
                            }
                        }
                        ItemKind::Function(f) => {
                            for param in f.params(db) {
                                self.queue(Queue::Type(it, false, Level::Signature, param.ty));
                            }
                            self.queue(Queue::Type(it, false, Level::Signature, f.return_ty(db)));
                            for cond in f.conditions(db) {
                                match cond {
                                    Condition::Ensures(exprs) | Condition::Requires(exprs) => {
                                        for expr in exprs {
                                            self.queue(Queue::Expr(it, Level::Signature, expr));
                                        }
                                    }
                                }
                            }
                            if let Some(body) = f.body(db) {
                                let level = if f.attrs(db).is_pure() {
                                    Level::Signature
                                } else {
                                    Level::Body
                                };
                                self.queue(Queue::Expr(it, level, body));
                            }
                        }
                    }
                }
                Queue::Type(it, direct, level, ty) => match ty.kind(db) {
                    TypeData::Error
                    | TypeData::Void
                    | TypeData::Primitive(_)
                    | TypeData::Null
                    | TypeData::Generic(_) => {}

                    TypeData::Ref { is_mut: _, inner } | TypeData::Optional(inner) => {
                        self.queue(Queue::Type(it, false, level, inner))
                    }
                    TypeData::Adt(adt) => {
                        let nit = Item::new(db, ItemKind::Adt(adt));
                        if !direct || it != nit {
                            self.dep(it, nit, level);
                        }
                        self.queue(Queue::Type(nit, true, level, adt.ty(db)));

                        for field in adt.fields(db) {
                            self.queue(Queue::Type(nit, false, level, field.ty(db)));
                        }
                    }
                    TypeData::Builtin(b) => {
                        for ty in b.generic_args(db) {
                            self.queue(Queue::Type(it, false, level, *ty));
                        }
                    }
                    TypeData::Function(_) => {}
                },
                Queue::Expr(it, level, expr) => expr.visit(db, &mut |expr| match expr {
                    itertools::Either::Left(expr) => match expr.data(db) {
                        ExprData::Adt { adt, .. } => {
                            let nit = Item::new(db, ItemKind::Adt(adt));
                            self.dep(it, nit, level);
                            self.queue(Queue::Item(nit));
                        }
                        ExprData::Ident(var) => {
                            if let Some(decl) = var.decl {
                                match decl {
                                    VariableDeclaration::Function(f) => {
                                        let nit = Item::new(db, ItemKind::Function(f));
                                        self.dep(it, nit, level);
                                        self.queue(Queue::Item(nit));
                                    }
                                    VariableDeclaration::Let { .. }
                                    | VariableDeclaration::Parameter => {}
                                }
                            }
                        }

                        ExprData::Literal(_) => {}
                        ExprData::Self_ => {}
                        ExprData::Field { .. } => {}
                        ExprData::Missing => {}
                        ExprData::Block(_) => {}
                        ExprData::If(_) => {}
                        ExprData::While(_) => {}
                        ExprData::For(_) => {}
                        ExprData::Call { .. } => {}
                        ExprData::Unary { .. } => {}
                        ExprData::Bin { .. } => {}
                        ExprData::Ref { .. } => {}
                        ExprData::Index { .. } => {}
                        ExprData::List { .. } => {}
                        ExprData::Quantifier { .. } => {}
                        ExprData::Result => {}
                        ExprData::Range { .. } => {}
                        ExprData::Return(_) => {}
                        ExprData::NotNull(_) => {}
                        ExprData::Builtin(_) => {}
                    },
                    itertools::Either::Right(stmt) => match stmt.data(db) {
                        StatementData::Let(_) => {}
                        StatementData::Expr(_) | StatementData::Assertion { .. } => {}
                    },
                }),
            };
        }
    }

    fn finish(self) -> MonoDep {
        MonoDep { nodes: self.nodes, graph: self.g }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Queue {
    Item(Item),
    Type(Item, bool, Level, Type),
    Expr(Item, Level, ExprPtr),
}
