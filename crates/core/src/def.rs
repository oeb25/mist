use mist_syntax::ast;

use crate::hir::file::AstId;

mod ext;
mod name;

pub use name::Name;

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

impl DefKind {
    pub fn to_function(self) -> Option<Function> {
        if let Self::Function(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn to_struct(self) -> Option<Struct> {
        if let Self::Struct(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn to_struct_field(self) -> Option<StructField> {
        if let Self::StructField(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn to_type_invariant(self) -> Option<TypeInvariant> {
        if let Self::TypeInvariant(v) = self {
            Some(v)
        } else {
            None
        }
    }
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
