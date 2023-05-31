use std::ops::ControlFlow;

use derive_new::new;
use mist_core::{
    hir::{self, types::TypeProvider, SourceFile, VariableRef},
    salsa,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
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
        field: hir::Field,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if reference.contains_pos(self.byte_offset) {
            let original_span = reference.span();
            match field {
                hir::Field::StructField(sf) => {
                    let target_span = sf.ast_node(self.db).name().unwrap().span();
                    return ControlFlow::Break(Some(DeclarationSpans {
                        original_span,
                        target_span,
                    }));
                }
                hir::Field::List(_, _) | hir::Field::Undefined => {}
            }
        }
        ControlFlow::Continue(())
    }

    fn visit_ty(
        &mut self,
        vcx: &VisitContext,
        ty: hir::TypeSrcId,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        let original_span = vcx.source_map[ty].span();
        if original_span.contains(self.byte_offset) {
            match vcx.cx.ty_data(vcx.cx[ty].ty) {
                hir::TypeData::Struct(s) => {
                    let target_span = s.ast_node(self.db).name().unwrap().span();
                    ControlFlow::Break(Some(DeclarationSpans {
                        original_span,
                        target_span,
                    }))
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
        var: VariableRef,
    ) -> ControlFlow<Option<DeclarationSpans>> {
        if var.contains_pos(self.byte_offset) {
            let original_span = var.span();
            let target_span = vcx.cx.var_span(var);
            ControlFlow::Break(Some(DeclarationSpans {
                original_span,
                target_span,
            }))
        } else {
            ControlFlow::Continue(())
        }
    }
}
