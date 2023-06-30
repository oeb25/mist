use mist_syntax::ast::{self, HasName, Spanned};

use crate::{
    def::{Def, Generic, Name},
    hir::{typecheck::TypeCheckErrorKind, Path, SpanOrAstPtr, TypeRef, TypeRefKind, TypeSrc},
    types::{
        primitive::{bool, error, int},
        Adt, AdtKind, AdtPrototype, BuiltinKind, Field, GenericArgs, Primitive, TypeData, TypeId,
        TypeProvider, TDK,
    },
    TypeCheckError,
};

use super::Typed;

pub enum NamedType {
    TypeId(TypeId),
    AdtKind(AdtKind),
    Builtin(BuiltinKind),
}

pub(crate) trait TypingMut: TypeProvider {
    fn push_error(&self, err: TypeCheckError);
    fn db(&self) -> &dyn crate::Db;

    fn lookup_named_ty(&self, name: Name) -> Option<NamedType>;
    fn new_free(&mut self) -> TypeId;
    fn new_generic(&mut self, generic: Generic) -> TypeId;

    fn create_adt_prototype(&mut self, kind: AdtKind, prototype: AdtPrototype);
    fn instantiate_adt(&mut self, kind: AdtKind, generic_args: GenericArgs) -> Adt;
    fn adt_ty(&mut self, adt: Adt) -> TypeId;

    fn alloc_ty_data(&mut self, data: TypeData) -> TypeId;
    fn alloc_ty_src(&mut self, ts: TypeSrc, ty_src: Option<SpanOrAstPtr<ast::Type>>) -> TypeSrc;
}

impl<T: TypingMut> TypingMutExt for T {}

pub(crate) trait TypingMutExt: TypingMut + Sized {
    fn unsourced_ty(&mut self, ty: impl Typed) -> TypeSrc {
        let ty_src = TypeSrc::unsourced(self.db(), ty.ty(self));
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

    fn find_named_type(&self, span: impl Spanned, name: Name) -> Result<NamedType, TypeId> {
        self.lookup_named_ty(name.clone()).ok_or_else(|| {
            self.ty_error(span, None, None, TypeCheckErrorKind::UndefinedType(name.to_string()))
        })
    }

    fn lower_type(&mut self, ast_ty: &ast::Type) -> TypeSrc {
        let (_, _, ts) = lower_type_inner(self, ast_ty);
        ts
    }

    fn field_ty(&mut self, f: Field) -> TypeId {
        match f {
            Field::AdtField(af) => af.ty(),
            Field::Builtin(bf) => bf.ty(self),
            Field::Undefined => error(),
        }
    }

    fn expect_find_type(&mut self, ty: &Option<ast::Type>) -> TypeId {
        match ty {
            Some(ty) => self.lower_type(ty).ty(self.db()),
            None => error(),
        }
    }
    fn expect_find_type_src(&mut self, ty: &Option<ast::Type>) -> TypeSrc {
        match ty {
            Some(ty) => self.lower_type(ty),
            None => self.unsourced_ty(error()),
        }
    }

    fn register_generics(&mut self, def: Def) -> Vec<TypeId> {
        def.generics(self.db()).iter().map(|&generic| self.new_generic(generic)).collect()
    }
}

fn lower_type_inner_opt(
    tc: &mut impl TypingMut,
    ast_ty: Option<ast::Type>,
) -> (TypeRefKind, TypeId) {
    if let Some(ty) = ast_ty {
        let (td, ty, _) = lower_type_inner(tc, &ty);
        (td, ty)
    } else {
        (TypeRefKind::Error, tc.new_free())
    }
}
fn lower_type_inner(tc: &mut impl TypingMut, ast_ty: &ast::Type) -> (TypeRefKind, TypeId, TypeSrc) {
    let (td, ty) = match ast_ty {
        ast::Type::NamedType(ast_name) => {
            let name = ast_name.name().unwrap();
            match tc.find_named_type(ast_name, name.clone().into()) {
                Ok(named) => {
                    let (path, arity) = match named {
                        NamedType::AdtKind(adt_kind) => {
                            (Path::Adt(adt_kind), adt_kind.arity(tc.db()))
                        }
                        NamedType::Builtin(builtin) => {
                            (Path::Name(builtin.name()), builtin.arity())
                        }
                        NamedType::TypeId(_) => (Path::Name(name.into()), 0),
                    };
                    let type_args = if let Some(args) = ast_name.generic_arg_list() {
                        // TODO: put `type_ref_args` on the type ref
                        let (_type_ref_args, type_args): (Vec<_>, Vec<_>) = args
                            .generic_args()
                            .map(|arg| lower_type_inner_opt(tc, arg.ty()))
                            .unzip();

                        GenericArgs::new(tc.db(), type_args)
                    } else {
                        GenericArgs::none(tc.db())
                    };

                    if arity != type_args.len(tc.db()) {
                        let span = Spanned::span((ast_name.generic_arg_list().as_ref(), ast_name));
                        tc.ty_error(
                            span,
                            None,
                            None,
                            TypeCheckErrorKind::GenericArityMismatch {
                                expected: arity,
                                given: type_args.len(tc.db()),
                            },
                        );
                    }

                    let ty = match named {
                        NamedType::TypeId(ty) => ty,
                        NamedType::AdtKind(adt_kind) => {
                            let adt = tc.instantiate_adt(adt_kind, type_args);
                            tc.adt_ty(adt)
                        }
                        NamedType::Builtin(builtin) => {
                            tc.alloc_ty_data(TDK::Builtin(builtin, type_args).into())
                        }
                    };

                    (TypeRefKind::Path(path), ty)
                }
                Err(err_ty) => (TypeRefKind::Error, err_ty),
            }
        }
        ast::Type::Primitive(it) => match () {
            _ if it.int_token().is_some() => (TypeRefKind::Primitive(Primitive::Int), int()),
            _ if it.bool_token().is_some() => (TypeRefKind::Primitive(Primitive::Bool), bool()),
            _ => {
                todo!();
            }
        },
        ast::Type::Optional(it) => {
            let (inner, inner_ty) = lower_type_inner_opt(tc, it.ty());
            (
                TypeRefKind::Optional(Box::new(inner)),
                tc.alloc_ty_data(TDK::Optional(inner_ty).into()),
            )
        }
        ast::Type::ListType(it) => {
            let (inner, inner_ty) = lower_type_inner_opt(tc, it.ty());
            (
                TypeRefKind::List(Box::new(inner)),
                tc.alloc_ty_data(TypeData::list(tc.db(), inner_ty)),
            )
        }
        ast::Type::GhostType(it) => {
            let (inner, inner_ty) = lower_type_inner_opt(tc, it.ty());
            (TypeRefKind::Ghost(Box::new(inner)), inner_ty.ghosted(tc))
        }
        ast::Type::RefType(it) => {
            let is_mut = it.mut_token().is_some();
            let (inner, inner_ty) = lower_type_inner_opt(tc, it.ty());
            (
                TypeRefKind::Ref { is_mut, inner: Box::new(inner) },
                tc.alloc_ty_data(TDK::Ref { is_mut, inner: inner_ty }.into()),
            )
        }
    };

    let ts = TypeSrc::sourced(tc.db(), TypeRef::new(tc.db(), td.clone()), ty);
    tc.alloc_ty_src(ts, Some(ast_ty.into()));
    (td, ty, ts)
}
