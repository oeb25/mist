use std::ops::ControlFlow;

use derive_new::new;
use itertools::Either;
use mist_core::{
    hir::{self, SourceFile, TypeRefKind, VariableIdx},
    salsa,
    types::Field,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
    VariableDeclarationKind,
};
use mist_syntax::{
    ast::{self, HasName, Spanned},
    SourceSpan,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationSpans {
    pub original_span: SourceSpan,
    pub target_span: SourceSpan,
}

#[salsa::tracked]
pub fn goto_declaration(
    db: &dyn crate::Db,
    file: SourceFile,
    byte_offset: usize,
) -> Option<DeclarationSpans> {
    let mut visitor = DeclarationFinder::new(db, byte_offset);
    match PostOrderWalk::walk_program(db, file, &mut visitor) {
        ControlFlow::Break(result) => result,
        ControlFlow::Continue(()) => None,
    }
}
#[salsa::tracked]
pub fn find_references(
    db: &dyn crate::Db,
    file: SourceFile,
    byte_offset: usize,
) -> Vec<SourceSpan> {
    let root = hir::file::parse_file(db, file).tree();

    let def_named = file.definitions(db).into_iter().find_map(|def| {
        let hir = def.hir(db)?;
        let source_map = hir.source_map(db);
        source_map.names().find_map(|(ptr, named)| {
            if let ast::NameOrNameRef::Name(name) = ptr.to_node(root.syntax()) {
                if name.contains_pos(byte_offset) {
                    return Some((def, named));
                }
            }
            None
        })
    });

    let Some((named_def, named)) = def_named else { return vec![] };

    file.definitions(db)
        .into_iter()
        .flat_map(|def| Some((def, def.hir(db)?)))
        .flat_map(|(def, hir)| {
            let var = match named {
                hir::Named::Variable(var) => hir.cx(db).decl(*var),
            };
            match var.kind() {
                VariableDeclarationKind::Function => {}
                VariableDeclarationKind::Let | VariableDeclarationKind::Parameter
                    if def == named_def => {}
                _ => return Either::Right([].into_iter()),
            }
            Either::Left(hir.source_map(db).named_references(named).map(|n| n.span()))
        })
        .collect()
}

#[derive(new)]
struct DeclarationFinder<'a> {
    db: &'a dyn crate::Db,
    byte_offset: usize,
}

impl Visitor for DeclarationFinder<'_> {
    type Item = Option<DeclarationSpans>;
    fn visit_field(
        &mut self,
        _: &VisitContext,
        field: Field,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if reference.contains_pos(self.byte_offset) {
            let original_span = reference.span();
            match field {
                Field::StructField(sf) => {
                    let target_span = sf.ast_node(self.db).name().unwrap().span();
                    return ControlFlow::Break(Some(DeclarationSpans {
                        original_span,
                        target_span,
                    }));
                }
                Field::List(_, _) | Field::Undefined => {}
            }
        }
        ControlFlow::Continue(())
    }

    fn visit_ty(
        &mut self,
        vcx: &VisitContext,
        ty: hir::TypeSrc,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        let original_span = vcx.source_map[ty].span();
        if original_span.contains(self.byte_offset) {
            match ty.type_ref(self.db) {
                Some(TypeRefKind::Struct(s)) => {
                    let target_span = s.ast_node(self.db).name().unwrap().span();
                    ControlFlow::Break(Some(DeclarationSpans { original_span, target_span }))
                }
                _ => ControlFlow::Continue(()),
            }
        } else {
            ControlFlow::Continue(())
        }
    }
    fn visit_var(
        &mut self,
        vcx: &VisitContext,
        var: VariableIdx,
        span: SourceSpan,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if span.contains_pos(self.byte_offset) {
            let original_span = span;
            let target_span = vcx.cx.var_span(var);
            ControlFlow::Break(Some(DeclarationSpans { original_span, target_span }))
        } else {
            ControlFlow::Continue(())
        }
    }
}
