pub mod exprs;
pub mod lower;
pub mod types;

use mist_syntax::ast::AttrFlags;

use crate::{def::Name, file::SourceFile, hir::Param, mono::lower::MonoLower};

use self::{
    exprs::{ExprPtr, VariablePtr},
    types::{Adt, Type},
};

/// A monomorphized item
#[salsa::interned]
pub struct Item {
    pub kind: ItemKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Adt(Adt),
    Function(Function),
}

#[salsa::tracked]
pub fn monomorphized_items(db: &dyn crate::Db, file: SourceFile) -> Monomorphized {
    let mut ml = MonoLower::new(db);

    for def in file.definitions(db) {
        ml.lower_def(def);
    }

    ml.finish()
}

#[salsa::tracked]
pub struct Monomorphized {
    pub items: Vec<Item>,
}

#[salsa::interned]
pub struct Function {
    pub attrs: AttrFlags,
    pub name: Name,
    pub params: Vec<Param<VariablePtr, Type>>,
    pub return_ty: Type,
    pub conditions: Vec<Condition>,
    pub body: Option<ExprPtr>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Vec<ExprPtr>),
    Ensures(Vec<ExprPtr>),
}

impl Item {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self.kind(db) {
            ItemKind::Adt(adt) => adt.kind(db).name(db),
            ItemKind::Function(fun) => fun.name(db),
        }
    }
}
