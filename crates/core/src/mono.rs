pub mod dep;
pub mod exprs;
pub mod lower;
pub mod types;

use mist_syntax::ast::AttrFlags;

use crate::{
    def::{Def, Name},
    file::SourceFile,
    hir::Param,
    mono::lower::MonoLower,
};

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
    def: Def,
    pub attrs: AttrFlags,
    pub name: Name,
    pub params: Vec<Param<VariablePtr, Type>>,
    pub return_ty: Type,
    pub conditions: Vec<Condition>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Vec<ExprPtr>),
    Ensures(Vec<ExprPtr>),
}

impl Item {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self.kind(db) {
            ItemKind::Adt(adt) => Name::new(&adt.display(db).to_string()),
            ItemKind::Function(fun) => fun.name(db),
        }
    }
}
