use itertools::Itertools;
use mist_syntax::ast::AttrFlags;

use crate::{
    def::{DefKind, Generic, Name},
    types::{AdtKind, BuiltinKind, Primitive, TypeProvider, TDK},
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
    #[return_ref]
    pub generic_args: Vec<Type>,
}

#[salsa::interned]
pub struct Adt {
    pub kind: AdtKind,
    #[return_ref]
    pub generic_args: Vec<Type>,
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

impl AdtKind {
    pub fn generic_params(self, db: &dyn crate::Db) -> Vec<Type> {
        self.def()
            .generics(db)
            .iter()
            .map(|g| Type::new(db, false, TypeData::Generic(*g)))
            .collect()
    }
}

impl Adt {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.kind(db).name(db)
    }
    pub fn fields(&self, db: &dyn crate::Db) -> Vec<AdtField> {
        match self.kind(db) {
            AdtKind::Struct(def, _) => super::lower::adt_kind_prototype_fields(db, def)
                .iter()
                .map(|(name, ty)| {
                    let new_ty = ty.substitude(db, &mut |ty| {
                        self.kind(db)
                            .generic_params(db)
                            .iter()
                            .position(|gp| ty == *gp)
                            .and_then(|idx| self.generic_args(db).get(idx).copied())
                            .unwrap_or(ty)
                    });
                    AdtField::new(db, name.clone(), new_ty)
                })
                .collect(),
            AdtKind::Enum => todo!(),
        }
    }
    pub fn ty(&self, db: &dyn crate::Db) -> Type {
        Type::new(db, false, TypeData::Adt(*self))
    }
    pub fn is_monomophic(self, db: &dyn crate::Db) -> bool {
        self.fields(db).iter().all(|f| f.ty(db).is_monomophic(db))
    }
}
#[salsa::tracked]
impl Adt {
    #[salsa::tracked]
    pub fn invariants(self, db: &dyn crate::Db) -> Vec<ExprPtr> {
        self.kind(db)
            .def()
            .file(db)
            .definitions(db)
            .iter()
            .filter_map(|def| {
                match def.kind(db) {
                    DefKind::TypeInvariant(_) => {}
                    _ => return None,
                }

                let cx = def.hir(db)?.cx(db);
                let mut mdl = MonoDefLower::new(db, cx);

                // NOTE: Try to perform unification of generic arguments.

                // NOTE: ATM we only do so shallowly, but we should in the
                // future do proper unification.
                let inv_adt = cx.ty_data(cx.invariant_ty(db)?).adt()?;
                if inv_adt.kind() != self.kind(db) {
                    return None;
                }
                for (inv_ty, &self_ty) in inv_adt.generic_args(db).zip(self.generic_args(db)) {
                    match cx.ty_data(inv_ty).kind {
                        TDK::Generic(_) => {
                            // Need to substitude
                            mdl.add_substitution(inv_ty, self_ty);
                        }
                        _ if mdl.lower_ty(inv_ty) == self_ty => {
                            // They lowered to the same type, so we should be
                            // fine
                        }
                        // NOTE: recursive unification should perhaps be done
                        // here.
                        _ => return None,
                    }
                }

                let inv_ty = mdl.lower_ty(cx.invariant_ty(db)?);

                if inv_ty != self.ty(db) {
                    return None;
                }

                Some(mdl.lower_expr(cx.body_expr()?))
            })
            .collect()
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
    /// A type is monomophic if it does not contains any generics
    pub fn is_monomophic(self, db: &dyn crate::Db) -> bool {
        match self.kind(db) {
            TypeData::Generic(_) => false,
            TypeData::Error
            | TypeData::Void
            | TypeData::Primitive(_)
            | TypeData::Null
            | TypeData::Function(_) => true,
            TypeData::Ref { inner, .. } | TypeData::Optional(inner) => inner.is_monomophic(db),
            TypeData::Adt(adt) => adt.is_monomophic(db),
            TypeData::Builtin(b) => b.generic_args(db).iter().all(|ty| ty.is_monomophic(db)),
        }
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

    pub fn substitude(self, db: &dyn crate::Db, map: &mut impl FnMut(Type) -> Type) -> Type {
        let new = map(self);
        let new_data = match new.kind(db) {
            TypeData::Error
            | TypeData::Void
            | TypeData::Null
            | TypeData::Primitive(_)
            | TypeData::Generic(_) => return new,
            TypeData::Ref { is_mut, inner } => {
                TypeData::Ref { is_mut, inner: inner.substitude(db, map) }
            }
            TypeData::Optional(inner) => TypeData::Optional(inner.substitude(db, map)),
            TypeData::Adt(adt) => TypeData::Adt(Adt::new(
                db,
                adt.kind(db),
                adt.generic_args(db).iter().map(|arg| arg.substitude(db, map)).collect(),
            )),
            TypeData::Builtin(b) => TypeData::Builtin(BuiltinType::new(
                db,
                b.kind(db),
                b.generic_args(db).iter().map(|arg| arg.substitude(db, map)).collect(),
            )),
            TypeData::Function(ft) => TypeData::Function(FunctionType::new(
                db,
                ft.attrs(db),
                ft.params(db).iter().map(|arg| arg.substitude(db, map)).collect(),
                ft.return_ty(db).substitude(db, map),
            )),
        };
        Type::new(db, self.is_ghost(db), new_data)
    }
}
