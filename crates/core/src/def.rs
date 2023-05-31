use mist_syntax::ast;

use crate::hir::file::AstId;

mod ext;

#[salsa::interned]
pub struct Def {
    pub kind: DefKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, derive_more::From)]
pub enum DefKind {
    Function(Function),
    Struct(Struct),
    StructField(StructField),
    TypeInvariant(TypeInvariant),
}

#[salsa::interned]
pub struct Function {
    id: AstId<ast::Fn>,
}

#[salsa::interned]
pub struct Struct {
    id: AstId<ast::Struct>,
}

#[salsa::interned]
pub struct StructField {
    id: AstId<ast::StructField>,
    pub parent_struct: Struct,
}

#[salsa::interned]
pub struct TypeInvariant {
    id: AstId<ast::TypeInvariant>,
}
