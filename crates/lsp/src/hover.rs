use std::ops::ControlFlow;

use derive_new::new;
use mist_core::{
    hir::{
        self, pretty, types::TypeProvider, ExprData, ExprIdx, Field, FieldParent, Ident, Param,
        SourceProgram, TypeData, TypeSrcId, VariableIdx, VariableRef,
    },
    salsa,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
    VariableDeclarationKind,
};
use mist_syntax::{ast::Spanned, SourceSpan};

#[salsa::tracked]
pub fn hover(db: &dyn crate::Db, source: SourceProgram, byte_offset: usize) -> Option<HoverResult> {
    let program = hir::parse_program(db, source);
    let root = program.parse(db).tree();

    let mut visitor = HoverFinder::new(db, byte_offset);
    match PostOrderWalk::walk_program(db, program, &root, &mut visitor) {
        ControlFlow::Break(result) => result,
        ControlFlow::Continue(()) => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HoverResult {
    pub contents: Vec<HoverElement>,
    pub range: Option<SourceSpan>,
}

impl HoverResult {
    pub fn new(contents: Vec<HoverElement>, range: Option<SourceSpan>) -> Self {
        Self { contents, range }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HoverElement {
    String(String),
    Code(String),
}

#[derive(new)]
struct HoverFinder<'a> {
    db: &'a dyn crate::Db,
    byte_offset: usize,
}

impl<'a> Visitor for HoverFinder<'a> {
    type Item = Option<HoverResult>;
    fn visit_field(
        &mut self,
        vcx: &VisitContext,
        field: Field,
        reference: &Ident,
    ) -> ControlFlow<Option<HoverResult>> {
        if reference.contains_pos(self.byte_offset) {
            match field.parent(self.db) {
                FieldParent::Struct(s) => {
                    let struct_ty = pretty::ty(&*vcx.cx, self.db, vcx.cx[vcx.cx.struct_ty(s)].ty);
                    let ty = pretty::ty(&*vcx.cx, self.db, vcx.cx.field_ty(field).id());
                    break_code(
                        [
                            format!("struct {struct_ty}"),
                            format!("{}: {ty}", field.name(self.db)),
                        ],
                        Some(reference.span()),
                    )
                }
                FieldParent::List(list_ty) => {
                    let list_ty = pretty::ty(&*vcx.cx, self.db, list_ty);
                    let ty = pretty::ty(&*vcx.cx, self.db, vcx.cx.field_ty(field).id());
                    break_code(
                        [format!("[{list_ty}]"), format!("len: {ty}")],
                        Some(reference.span()),
                    )
                }
            }
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_var(
        &mut self,
        vcx: &VisitContext,
        var: VariableRef,
    ) -> ControlFlow<Option<HoverResult>> {
        if var.contains_pos(self.byte_offset) {
            let name = vcx.cx.var_ident(var);
            let ty = pretty::ty(&*vcx.cx, self.db, vcx.cx.var_ty(var).id());

            break_code(
                [match vcx.cx.decl(var).kind() {
                    VariableDeclarationKind::Let => format!("let {name}: {ty}"),
                    VariableDeclarationKind::Parameter => format!("{name}: {ty}"),
                    VariableDeclarationKind::Function => ty,
                    VariableDeclarationKind::Undefined => name.to_string(),
                }],
                None,
            )
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_param(
        &mut self,
        vcx: &VisitContext,
        param: &Param<VariableIdx>,
    ) -> ControlFlow<Option<HoverResult>> {
        let name = vcx.cx.var_ident(param.name);
        if name.contains_pos(self.byte_offset) {
            let ty = pretty::ty(&*vcx.cx, self.db, vcx.cx[param.ty].ty);
            break_code([format!("{name}: {ty}")], None)
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_expr(
        &mut self,
        vcx: &VisitContext,
        expr: ExprIdx,
    ) -> ControlFlow<Option<HoverResult>> {
        let span = vcx.source_map.expr_span(expr);
        if span.contains_pos(self.byte_offset) {
            let expr = vcx.cx.expr(expr);
            let ty = pretty::ty(&*vcx.cx, self.db, expr.ty);
            if let ExprData::Result = &expr.data {
                return break_code([format!("result: {ty}")], None);
            } else {
                return break_code([ty], Some(span));
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, vcx: &VisitContext, ty: TypeSrcId) -> ControlFlow<Option<HoverResult>> {
        let span = match &vcx.source_map[ty] {
            src if src.span().contains(self.byte_offset) => src.span(),
            _ => return ControlFlow::Continue(()),
        };

        let pretty_ty = pretty::ty(&*vcx.cx, self.db, vcx.cx[ty].ty);

        let s = match &vcx.cx[ty].data {
            Some(TypeData::Struct(_)) => format!("struct {pretty_ty}"),
            _ => pretty_ty,
        };

        break_code([s], Some(span))
    }
}

fn break_code<const N: usize>(
    code: [String; N],
    span: Option<SourceSpan>,
) -> ControlFlow<Option<HoverResult>> {
    ControlFlow::Break(Some(HoverResult::new(
        code.map(HoverElement::Code).to_vec(),
        span,
    )))
}
