use mist_syntax::ast::{self, HasName, Spanned};

use crate::{
    hir::{typecheck::TypeCheckErrorKind, Name, SpanOrAstPtr, TypeSrc, TypeSrcId},
    types::{
        builtin::{bool, error, int},
        Primitive, TypeData, TypeId, TypeProvider, TDK,
    },
    TypeCheckError,
};

use super::Typed;

pub(crate) trait TypingMut: TypeProvider {
    fn push_error(&self, err: TypeCheckError);

    fn ty_src(&self, ty_src_id: TypeSrcId) -> &TypeSrc;
    fn lookup_named_ty(&self, name: Name) -> Option<TypeId>;
    fn new_free(&mut self) -> TypeId;

    fn alloc_ty_data(&mut self, data: TypeData) -> TypeId;
    fn alloc_ty_src(&mut self, ts: TypeSrc, ty_src: Option<SpanOrAstPtr<ast::Type>>) -> TypeSrcId;
}

impl<T: TypingMut> TypingMutExt for T {}

pub(crate) trait TypingMutExt: TypingMut + Sized {
    fn unsourced_ty(&mut self, ty: impl Typed) -> TypeSrcId {
        let ty_src = TypeSrc::new(None, ty.ty(self));
        self.alloc_ty_src(ty_src, None)
    }

    fn ty_error(
        &self,
        span: impl Spanned,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> TypeId {
        let span = span.span();
        let err = TypeCheckError { span, label, help, kind };
        self.push_error(err);
        error()
    }

    fn find_named_type(&self, span: impl Spanned, name: Name) -> TypeId {
        self.lookup_named_ty(name.clone()).unwrap_or_else(|| {
            self.ty_error(span, None, None, TypeCheckErrorKind::UndefinedType(name.to_string()))
        })
    }

    fn find_type_src(&mut self, ast_ty: &ast::Type) -> TypeSrcId {
        let (td, ty) = match ast_ty {
            mist_syntax::ast::Type::NamedType(ast_name) => {
                let name = ast_name.name().unwrap();
                let ty = self.find_named_type(ast_name, name.into());
                let td = match self.ty_kind(ty) {
                    TDK::Struct(s) => TDK::Struct(s),
                    TDK::Error => TDK::Error,
                    _ => todo!(),
                };
                (td.into(), ty)
            }
            mist_syntax::ast::Type::Primitive(it) => match () {
                _ if it.int_token().is_some() => (TDK::Primitive(Primitive::Int).into(), int()),
                _ if it.bool_token().is_some() => (TDK::Primitive(Primitive::Bool).into(), bool()),
                _ => {
                    todo!();
                }
            },
            mist_syntax::ast::Type::Optional(it) => {
                let inner = if let Some(ty) = it.ty() {
                    self.find_type_src(&ty)
                } else {
                    let ty = self.new_free();
                    self.unsourced_ty(ty)
                };
                let td = TDK::Optional(inner);
                let ty = td.canonical(self);
                let ty = self.alloc_ty_data(ty);
                (td.into(), ty)
            }
            mist_syntax::ast::Type::RefType(r) => {
                let is_mut = r.mut_token().is_some();

                let inner = if let Some(ty) = r.ty() { self.find_type_src(&ty) } else { todo!() };
                let td = TDK::Ref { is_mut, inner };
                let ty = td.canonical(self);
                let ty = self.alloc_ty_data(ty);
                (td.into(), ty)
            }
            mist_syntax::ast::Type::ListType(t) => {
                let inner = if let Some(ty) = t.ty() {
                    self.find_type_src(&ty)
                } else {
                    let ty = self.new_free();
                    self.unsourced_ty(ty)
                };
                let td = TDK::List(inner);
                let ty = td.canonical(self);
                let ty = self.alloc_ty_data(ty);
                (td.into(), ty)
            }
            mist_syntax::ast::Type::GhostType(t) => {
                let inner = if let Some(ty) = t.ty() { self.find_type_src(&ty) } else { todo!() };
                let td = TypeData {
                    kind: self.ty_src(inner).data.clone().unwrap().kind,
                    is_ghost: true,
                };
                let ty = td.canonical(self);
                let ty = self.alloc_ty_data(ty);
                (td, ty)
            }
        };

        let ts = TypeSrc { data: Some(td), ty };
        self.alloc_ty_src(ts, Some(ast_ty.into()))
    }

    fn expect_find_type(&mut self, ty: &Option<ast::Type>) -> TypeId {
        match ty {
            Some(ty) => {
                let ts = self.find_type_src(ty);
                self.ty_src(ts).ty
            }
            None => error(),
        }
    }
    fn expect_find_type_src(&mut self, ty: &Option<ast::Type>) -> TypeSrcId {
        match ty {
            Some(ty) => self.find_type_src(ty),
            None => self.unsourced_ty(error()),
        }
    }
}

impl TypeData<TypeSrcId> {
    pub(crate) fn canonical(&self, t: &impl TypingMut) -> TypeData {
        self.map(|&id| t.ty_src(id).ty)
    }
}

impl TDK<TypeSrcId> {
    pub(crate) fn canonical(&self, t: &impl TypingMut) -> TypeData {
        TypeData::from(self.clone()).canonical(t)
    }
}
