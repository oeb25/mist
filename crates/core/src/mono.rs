pub mod exprs;
pub mod lower;
pub mod types;

use mist_syntax::ast::AttrFlags;

use crate::{
    def::Name,
    hir::{self, ExprIdx, Param, SourceFile, VariableIdx},
    mono::lower::MonoLower,
    util::IdxMap,
};

use self::{
    exprs::ExprPtr,
    types::{Adt, Type},
};

/// A monomorphized item
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    pub source_map: MonoSourceMap,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct MonoSourceMap {}

#[salsa::interned]
pub struct Function {
    attrs: AttrFlags,
    name: Name,
    params: Vec<Param<VariableIdx, Type>>,
    return_ty: Type,
    body: Option<ExprIdx>,
}

impl Item {
    pub fn new(kind: ItemKind) -> Self {
        Self { kind }
    }
}
