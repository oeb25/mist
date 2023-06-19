use itertools::Itertools;
use mist_syntax::ast::AttrFlags;

use crate::{
    def::{Def, DefKind, Name},
    types::{AdtKind, Generic, Primitive},
};

use super::{exprs::ExprPtr, lower::MonoDefLower};

#[salsa::interned]
pub struct Type {
    pub is_ghost: bool,
    pub kind: TypeData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeData {
    Error,
    Void,
    Ref { is_mut: bool, inner: Type },
    List(Type),
    Optional(Type),
    Primitive(Primitive),
    Adt(Adt),
    Null,
    Generic(Generic),
    Function(FunctionType),
    Range(Type),
}

#[salsa::interned]
pub struct FunctionType {
    pub attrs: AttrFlags,
    #[return_ref]
    pub params: Vec<Type>,
    pub return_ty: Type,
}

#[salsa::interned]
pub struct Adt {
    pub kind: AdtKind,
    #[return_ref]
    pub fields: Vec<AdtField>,
}

#[salsa::interned]
pub struct AdtField {
    pub name: Name,
    pub ty: Type,
}

impl Adt {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.kind(db).name(db)
    }
    pub fn invariants(&self, db: &dyn crate::Db) -> Vec<ExprPtr> {
        match self.kind(db) {
            AdtKind::Struct(s) => {
                let file = Def::new(db, crate::def::DefKind::Struct(s)).file(db);
                file.definitions(db)
                    .iter()
                    .filter_map(|def| match def.kind(db) {
                        DefKind::TypeInvariant(_) => {
                            let hir = def.hir(db)?;
                            let cx = hir.cx(db);
                            let mut inner_mdl = MonoDefLower::new(db, cx);
                            inner_mdl.lower_ty(cx.self_ty(db)?);
                            Some(inner_mdl.lower_expr(cx.body_expr()?))
                        }
                        _ => None,
                    })
                    .collect()
            }
        }
    }
}

impl Type {
    pub fn error(db: &dyn crate::Db) -> Type {
        Type::new(db, false, TypeData::Error)
    }
    pub fn bool(db: &dyn crate::Db) -> Type {
        Type::new(db, false, TypeData::Primitive(Primitive::Bool))
    }
    pub fn int(db: &dyn crate::Db) -> Type {
        Type::new(db, false, TypeData::Primitive(Primitive::Int))
    }

    pub fn is_error(&self, db: &dyn crate::Db) -> bool {
        matches!(self.kind(db), TypeData::Error)
    }
    pub fn is_void(&self, db: &dyn crate::Db) -> bool {
        matches!(self.kind(db), TypeData::Void)
    }

    pub fn ty_adt(&self, db: &dyn crate::Db) -> Option<Adt> {
        if let TypeData::Adt(adt) = self.kind(db) {
            Some(adt)
        } else {
            None
        }
    }

    pub fn display(&self, db: &dyn crate::Db) -> impl std::fmt::Display {
        use TypeData::*;

        match self.kind(db) {
            Error => "error".to_string(),
            Void => "void".to_string(),
            Ref { is_mut, inner } => {
                if is_mut {
                    format!("&mut {}", inner.display(db))
                } else {
                    format!("&{}", inner.display(db))
                }
            }
            List(inner) => format!("[{}]", inner.display(db)),
            Optional(inner) => format!("?{}", inner.display(db)),
            Primitive(p) => format!("{p:?}").to_lowercase(),
            Adt(adt) => format!("{}", adt.name(db)),
            Null => "null".to_string(),
            Generic(_) => "<generic>".to_string(),
            Function(f) => {
                let attrs = f.attrs(db);

                let mut attrs = attrs.to_string();
                if !attrs.is_empty() {
                    attrs.push(' ');
                }
                // TODO: do we want a way to track names?
                // let name = f.name(db).as_ref().map(|name| format!(" {name}")).unwrap_or_default();
                let name = "";
                let params = f.params(db).iter().map(|param| param.display(db)).format(", ");
                let ret = if let TypeData::Void = f.return_ty(db).kind(db) {
                    String::new()
                } else {
                    format!(" -> {}", f.return_ty(db).display(db))
                };

                format!("{attrs}fn{name}{params}{ret}")
            }
            Range(r) => format!("range {}", r.display(db)),
        }
    }
}
