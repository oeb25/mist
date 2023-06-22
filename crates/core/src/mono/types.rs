use itertools::Itertools;
use mist_syntax::ast::AttrFlags;

use crate::{
    def::{Def, DefKind, Name},
    types::{AdtKind, BuiltinKind, Generic, Primitive},
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
    Optional(Type),
    Primitive(Primitive),
    Adt(Adt),
    Builtin(BuiltinType),
    Null,
    Generic(Generic),
    Function(FunctionType),
}

#[salsa::interned]
pub struct FunctionType {
    pub attrs: AttrFlags,
    #[return_ref]
    pub params: Vec<Type>,
    pub return_ty: Type,
}

#[salsa::interned]
pub struct BuiltinType {
    pub kind: BuiltinKind,
    pub generic_args: Vec<Type>,
}

#[salsa::interned]
pub struct Adt {
    pub kind: AdtKind,
    pub generic_args: Vec<Type>,
    #[return_ref]
    raw_fields: Vec<(crate::types::AdtField, crate::types::TypeId)>,
}

#[salsa::interned]
pub struct AdtField {
    pub name: Name,
    pub ty: Type,
}

impl BuiltinType {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.kind(db).name()
    }
}

impl Adt {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.kind(db).name(db)
    }
    pub fn fields(&self, db: &dyn crate::Db) -> Vec<AdtField> {
        match self.kind(db) {
            AdtKind::Struct(s) => {
                let def = Def::new(db, crate::def::DefKind::Struct(s));
                let hir = def.hir(db).unwrap();
                let cx = hir.cx(db);
                let mut inner_mdl = MonoDefLower::new(db, cx);

                self.raw_fields(db)
                    .iter()
                    .map(|(af, ty)| {
                        let ty = inner_mdl.lower_ty(*ty);
                        AdtField::new(db, af.name(db), ty)
                    })
                    .collect()
            }
            AdtKind::Enum => todo!(),
        }
    }
    pub fn ty(&self, db: &dyn crate::Db) -> Type {
        Type::new(db, false, TypeData::Adt(*self))
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
                            let inv_ty = inner_mdl.lower_ty(cx.invariant_ty(db)?);

                            if inv_ty != self.ty(db) {
                                return None;
                            }

                            Some(inner_mdl.lower_expr(cx.body_expr()?))
                        }
                        _ => None,
                    })
                    .collect()
            }
            AdtKind::Enum => vec![],
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

    pub fn is_list(&self, db: &dyn crate::Db) -> bool {
        matches!(self.builtin(db), Some(b) if b.kind(db) == BuiltinKind::List)
    }
    pub fn is_ref(&self, db: &dyn crate::Db) -> bool {
        matches!(self.kind(db), TypeData::Ref { .. })
    }

    pub fn builtin(&self, db: &dyn crate::Db) -> Option<BuiltinType> {
        match self.kind(db) {
            TypeData::Builtin(b) => Some(b),
            _ => None,
        }
    }

    pub fn is_adt(&self, db: &dyn crate::Db) -> bool {
        matches!(self.kind(db), TypeData::Adt(_))
    }
    pub fn ty_adt(&self, db: &dyn crate::Db) -> Option<Adt> {
        match self.kind(db) {
            TypeData::Adt(adt) => Some(adt),
            TypeData::Optional(inner) | TypeData::Ref { inner, .. } => inner.ty_adt(db),
            _ => None,
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
            Optional(inner) => format!("?{}", inner.display(db)),
            Primitive(p) => format!("{p:?}").to_lowercase(),
            Adt(adt) => format!("{}", adt.name(db)),
            Builtin(b) => format!(
                "{}[{}]",
                b.name(db),
                b.generic_args(db).iter().map(|arg| arg.display(db)).format(", ")
            ),
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
        }
    }
}
