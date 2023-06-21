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
    pub fn new(db: &dyn crate::Db, id: AstId<ast::Item>) -> Option<DefKind> {
        let root = id.file.root(db);
        let ast_map = id.file.ast_map(db);

        Some(match ast_map.get(id.value).to_node(root.syntax()) {
            ast::Item::Fn(node) => DefKind::from(Function::new(db, ast_map.ast_id(id.file, &node))),
            ast::Item::Struct(node) => {
                DefKind::from(Struct::new(db, ast_map.ast_id(id.file, &node)))
            }
            ast::Item::TypeInvariant(node) => {
                DefKind::from(TypeInvariant::new(db, ast_map.ast_id(id.file, &node)))
            }
            ast::Item::Const(_) | ast::Item::Macro(_) => return None,
        })
    }

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

// TODO: This is just a stub at the moment of writing
#[salsa::interned]
pub struct Enum {
    // id: AstId<ast::Enum>,
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
