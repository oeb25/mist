use std::collections::HashMap;

use itertools::Itertools;
use mist_syntax::ast::{self, HasName, Spanned};

use crate::{
    def::{Function, Name},
    hir::{
        self,
        typecheck::{TypeCheckErrorKind, Typed, TypingMutExt},
        ItemSourceMap, Param, SpanOrAstPtr, TypeSrc,
    },
    types::{
        builtin::void, Adt, AdtField, AdtKind, AdtPrototype, Generic, StructPrototype, TypeData,
        TypeId, TypeProvider, Typer, TDK,
    },
    TypeCheckError, TypeCheckErrors,
};

use super::typecheck::TypingMut;

#[salsa::tracked]
pub(crate) fn initialize_file_context(
    db: &dyn crate::Db,
    file: hir::SourceFile,
) -> (FileContext, ItemSourceMap) {
    initialize_file_context_inner(db, file)
}
fn initialize_file_context_inner(
    db: &dyn crate::Db,
    file: hir::SourceFile,
) -> (FileContext, ItemSourceMap) {
    let mut b = FileContextBuilder {
        db,
        typer: Typer::new(),
        fc: FileContext::default(),
        source_map: Default::default(),
    };

    for def in hir::file_definitions(db, file) {
        if let hir::DefKind::Struct(s) = def.kind(db) {
            let s_ast = s.ast_node(db);

            if let Some(_old) = b.fc.adts.insert(s.name(db), AdtKind::Struct(s)) {
                b.ty_error(
                    s_ast.span(),
                    None,
                    None,
                    TypeCheckErrorKind::NotYetImplemented(
                        "a struct with this name already declared".to_string(),
                    ),
                );
            }
            // if let Some(name) = s_ast.name() {
            //     let ts = b.alloc_ty_src(
            //         TypeSrc::sourced(
            //             db,
            //             TypeRef::new(db, TypeRefKind::Path(hir::Path::Struct(s))),
            //             s_ty,
            //         ),
            //         Some(name.span().into()),
            //     );
            //     b.fc.struct_types.insert(s, ts);
            // }
        }
    }
    for def in hir::file_definitions(db, file) {
        match def.kind(db) {
            hir::DefKind::Function(f) => {
                let is_ghost = f.attrs(db).is_ghost();
                let f_ast = f.ast_node(db);

                let params = f
                    .param_list(db)
                    .map(|param| Param {
                        is_ghost: param.is_ghost,
                        name: param.name.into(),
                        ty: b.expect_find_type_src(&param.ty).with_ghost(&mut b, is_ghost),
                    })
                    .collect();
                let return_ty_src =
                    f_ast.ret().map(|ty| b.lower_type(&ty).with_ghost(&mut b, is_ghost));
                let return_ty = return_ty_src
                    .map(|ts| ts.ty(db))
                    .unwrap_or_else(void)
                    .with_ghost(&mut b, is_ghost);

                if let Some(name) = f_ast.name() {
                    let ty = b.alloc_ty_data(
                        TDK::Function {
                            attrs: f.attrs(db),
                            name: Some(f.name(db).clone()),
                            params,
                            return_ty,
                        }
                        .into(),
                    );
                    if let Some(old) = b.fc.function_types.insert(f.name(db), (f, ty)) {
                        b.ty_error(
                            name.span(),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "redeclared function: '{}'",
                                old.0.name(db)
                            )),
                        );
                    }
                }
            }
            hir::DefKind::Struct(s) => {
                // TODO: register the generic names so they can be referenced in
                // the struct fields

                let generics = s
                    .ast_node(db)
                    .generic_param_list()
                    .into_iter()
                    .flat_map(|generic_params| generic_params.generic_params())
                    .map(|_arg| b.new_generic(Generic::default()))
                    .collect();

                let fields = s
                    .fields(db)
                    .map(|f| (f, b.expect_find_type_src(&f.ast_node(db).ty()).ty(db)))
                    .collect();
                b.create_adt_prototype(
                    AdtKind::Struct(s),
                    AdtPrototype::StructPrototype(StructPrototype { parent: s, generics, fields }),
                );
            }
            _ => {}
        };
    }

    (b.fc, b.source_map)
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FileContext {
    pub(super) function_types: HashMap<Name, (Function, TypeId)>,
    pub(super) adts: HashMap<Name, AdtKind>,
    events: Vec<FileContextBuilderEvent>,
}

impl FileContext {
    pub fn typer(&self, db: &dyn crate::Db) -> Typer {
        let mut typer = Typer::new();
        for event in &self.events {
            match event {
                FileContextBuilderEvent::AllocTy(td) => {
                    typer.ty_id(td.clone());
                }
                FileContextBuilderEvent::NewFree => {
                    typer.new_free();
                }
                FileContextBuilderEvent::NewGeneric(generic) => {
                    typer.new_generic(*generic);
                }
                FileContextBuilderEvent::CreateAdtPrototype(kind, prototype) => {
                    typer.create_adt_prototype(*kind, prototype.clone());
                }
                FileContextBuilderEvent::InstantiateAdt(kind, generic_args) => {
                    typer.instantiate_adt(db, *kind, generic_args.clone());
                }
            }
        }
        typer
    }
}

struct FileContextBuilder<'a> {
    db: &'a dyn crate::Db,
    typer: Typer,
    fc: FileContext,
    source_map: ItemSourceMap,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum FileContextBuilderEvent {
    AllocTy(TypeData),
    NewFree,
    NewGeneric(Generic),
    InstantiateAdt(AdtKind, Vec<TypeId>),
    CreateAdtPrototype(AdtKind, AdtPrototype),
}

impl<'a> TypeProvider for FileContextBuilder<'a> {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
    }
    fn fields_of(&self, adt: Adt) -> Vec<AdtField> {
        self.typer.adt_fields(adt).to_vec()
    }
}

impl<'a> TypingMut for FileContextBuilder<'a> {
    fn db(&self) -> &dyn crate::Db {
        self.db
    }

    fn push_error(&self, err: TypeCheckError) {
        TypeCheckErrors::push(self.db, err);
    }

    fn lookup_adt_kind(&self, name: Name) -> Option<AdtKind> {
        self.fc.adts.get(&name).copied()
    }

    fn new_free(&mut self) -> TypeId {
        self.fc.events.push(FileContextBuilderEvent::NewFree);
        self.typer.new_free()
    }

    fn new_generic(&mut self, generic: Generic) -> TypeId {
        self.fc.events.push(FileContextBuilderEvent::NewGeneric(generic));
        self.typer.new_generic(generic)
    }

    fn create_adt_prototype(&mut self, kind: AdtKind, prototype: AdtPrototype) {
        self.fc.events.push(FileContextBuilderEvent::CreateAdtPrototype(kind, prototype.clone()));
        self.typer.create_adt_prototype(kind, prototype)
    }
    fn instantiate_adt(
        &mut self,
        kind: AdtKind,
        generic_args: impl IntoIterator<Item = TypeId>,
    ) -> Adt {
        let generic_args = generic_args.into_iter().collect_vec();
        self.fc.events.push(FileContextBuilderEvent::InstantiateAdt(kind, generic_args.clone()));
        self.typer.instantiate_adt(self.db, kind, generic_args)
    }
    fn adt_ty(&self, adt: Adt) -> TypeId {
        self.typer.adt_ty(adt)
    }

    fn alloc_ty_data(&mut self, data: TypeData) -> TypeId {
        self.fc.events.push(FileContextBuilderEvent::AllocTy(data.clone()));
        self.typer.ty_id(data)
    }

    fn alloc_ty_src(&mut self, ts: TypeSrc, ty_src: Option<SpanOrAstPtr<ast::Type>>) -> TypeSrc {
        if let Some(src) = ty_src {
            self.source_map.register_ty_src(ts, src).unwrap();
        }
        ts
    }
}
