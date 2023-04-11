use std::ops::ControlFlow;

use derive_new::new;
use mist_core::{
    hir::{self, Ident, ItemContext, SourceProgram, VariableRef},
    salsa,
    visit::{PostOrder, Visitor, Walker},
};
use mist_syntax::{ast::Spanned, SourceSpan};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationSpans {
    pub original_span: SourceSpan,
    pub target_span: SourceSpan,
}

#[salsa::tracked]
pub fn goto_declaration(
    db: &dyn crate::Db,
    source: SourceProgram,
    byte_offset: usize,
) -> Option<DeclarationSpans> {
    let program = hir::parse_program(db, source);

    match PostOrder::new(db).walk_program(&mut DeclarationFinder::new(db, byte_offset), program) {
        ControlFlow::Break(result) => result,
        ControlFlow::Continue(()) => None,
    }
}

#[derive(new)]
struct DeclarationFinder<'a> {
    db: &'a dyn crate::Db,
    byte_offset: usize,
}

impl Visitor<Option<DeclarationSpans>> for DeclarationFinder<'_> {
    fn visit_field(
        &mut self,
        _cx: &ItemContext,
        field: &hir::Field,
        reference: &Ident,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if reference.contains_pos(self.byte_offset) {
            let original_span = reference.span();
            let target_span = field.name.span();
            ControlFlow::Break(Some(DeclarationSpans {
                original_span,
                target_span,
            }))
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_ty(
        &mut self,
        _cx: &ItemContext,
        ty: hir::Type,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        match ty.span(self.db) {
            Some(span) if span.contains(self.byte_offset) => match ty.data(self.db) {
                hir::TypeData::Struct(s) => {
                    let Some(original_span) = ty.span(self.db) else { return ControlFlow::Continue(()) };
                    let target_span = s.name(self.db).span();
                    ControlFlow::Break(Some(DeclarationSpans {
                        original_span,
                        target_span,
                    }))
                }
                _ => ControlFlow::Continue(()),
            },
            _ => ControlFlow::Continue(()),
        }
    }
    fn visit_var(
        &mut self,
        cx: &ItemContext,
        var: VariableRef,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if var.contains_pos(self.byte_offset) {
            let original_span = var.span();
            let target_span = cx.var_span(var);
            ControlFlow::Break(Some(DeclarationSpans {
                original_span,
                target_span,
            }))
        } else {
            ControlFlow::Continue(())
        }
    }
}
