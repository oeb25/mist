use std::collections::HashMap;

use mist_syntax::ast::{self, HasName, Spanned};

use crate::{
    def::{Function, Struct, StructField},
    hir::{
        self,
        typecheck::{TypeCheckErrorKind, Typed, TypingMutExt},
        ItemSourceMap, Name, Param, SpanOrAstPtr, TypeSrc, TypeSrcId,
    },
    types::{builtin::void, TypeData, TypeId, TypeProvider, Typer, TDK},
    util::IdxArena,
    TypeCheckError, TypeCheckErrors,
};

use super::typecheck::TypingMut;

#[salsa::tracked]
pub(crate) fn initialize_file_context(
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
        let f = match def.kind(db) {
            hir::DefKind::Function(f) => f,
            hir::DefKind::Struct(s) => {
                let s_ast = s.ast_node(db);

                let s_ty = b.alloc_ty_data(TDK::Struct(s).into());
                if let Some(old) = b.fc.named_types.insert(s.name(db), s_ty) {
                    b.ty_error(
                        s_ast.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(
                            "a struct with this name already declared".to_string(),
                        ),
                    );
                }
                if let Some(name) = s_ast.name() {
                    let ts = b.alloc_ty_src(
                        TypeSrc { data: Some(TDK::Struct(s).into()), ty: s_ty },
                        Some(name.span().into()),
                    );
                    b.fc.struct_types.insert(s, ts);
                }

                for f in s.fields(db) {
                    let data = f.ast_node(db).ty();
                    let ty = b.expect_find_type_src(&data);
                    b.fc.struct_field_types.insert(f, ty);
                }

                continue;
            }
            _ => continue,
        };
        let is_ghost = f.attrs(db).is_ghost();
        let f_ast = f.ast_node(db);

        let params = f
            .param_list(db)
            .map(|param| {
                let ty = b.expect_find_type_src(&param.ty);
                Param {
                    is_ghost: param.is_ghost,
                    name: param.name.into(),
                    ty: ty.with_ghost(&mut b, is_ghost),
                }
            })
            .collect();
        let return_ty_src = f_ast.ret().map(|ty| b.find_type_src(&ty).with_ghost(&mut b, is_ghost));
        let return_ty = return_ty_src
            .map(|ts| b.ty_src(ts).ty)
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

    (b.fc, b.source_map)
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FileContext {
    pub(super) ty_src_arena: IdxArena<TypeSrcId>,
    pub(super) function_types: HashMap<Name, (Function, TypeId)>,
    pub(super) named_types: HashMap<Name, TypeId>,
    pub(super) struct_types: HashMap<Struct, TypeSrcId>,
    pub(super) struct_field_types: HashMap<StructField, TypeSrcId>,

    events: Vec<FileContextBuilderEvent>,
}

impl FileContext {
    pub fn typer(&self) -> Typer {
        let mut typer = Typer::new();
        for event in &self.events {
            match event {
                FileContextBuilderEvent::AllocTy(td) => {
                    typer.ty_id(td.clone());
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
}

impl<'a> TypeProvider for FileContextBuilder<'a> {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
    }

    fn struct_field_ty(&self, sf: StructField) -> TypeId {
        self.fc.struct_field_types[&sf].ty(self)
    }
}

impl<'a> TypingMut for FileContextBuilder<'a> {
    fn push_error(&self, err: TypeCheckError) {
        TypeCheckErrors::push(self.db, err);
    }

    fn ty_src(&self, ty_src_id: TypeSrcId) -> &TypeSrc {
        &self.fc.ty_src_arena[ty_src_id]
    }

    fn lookup_named_ty(&self, name: Name) -> Option<TypeId> {
        self.fc.named_types.get(&name).copied()
    }

    fn new_free(&mut self) -> TypeId {
        self.typer.new_free()
    }

    fn alloc_ty_data(&mut self, data: TypeData) -> TypeId {
        self.fc.events.push(FileContextBuilderEvent::AllocTy(data.clone()));
        self.typer.ty_id(data)
    }

    fn alloc_ty_src(&mut self, ts: TypeSrc, ty_src: Option<SpanOrAstPtr<ast::Type>>) -> TypeSrcId {
        let id = self.fc.ty_src_arena.alloc(ts);
        if let Some(src) = ty_src {
            self.source_map.ty_src_map.insert(id, src.clone());
            self.source_map.ty_src_map_back.insert(src, id);
        }
        id
    }
}
