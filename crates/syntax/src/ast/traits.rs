use crate::support::{self, AstNode};

use super::{Attr, AttrFlags, Attrs, Expr, Name};

pub trait HasAttrs: AstNode {
    fn attrs(&self) -> Option<Attrs> {
        support::child(self.syntax())
    }
    fn attr_flags(&self) -> AttrFlags {
        let Some(attrs) = self.attrs() else { return Default::default() };
        support::children(&attrs.syntax)
            .flat_map(|a: Attr| {
                [a.ghost_token().map(|_| AttrFlags::GHOST), a.pure_token().map(|_| AttrFlags::PURE)]
            })
            .flatten()
            .reduce(|acc, flag| acc | flag)
            .unwrap_or_default()
    }
    fn is_ghost(&self) -> bool {
        self.attr_flags().is_ghost()
    }
    fn is_pure(&self) -> bool {
        self.attr_flags().is_pure()
    }
}

pub trait HasName: AstNode {
    fn name(&self) -> Option<Name> {
        support::child(self.syntax())
    }
}
pub trait HasExpr: AstNode {
    fn expr(&self) -> Option<Expr> {
        support::child(self.syntax())
    }
}
