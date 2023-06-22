use std::ops::ControlFlow;

use derive_new::new;
use mist_core::{
    def::{Def, DefKind, Name, StructField},
    hir::{pretty, ExprData, ExprIdx, SourceFile, TypeRefKind, TypeSrc, VariableIdx},
    salsa,
    types::{AdtKind, BuiltinField, Field, TypeProvider},
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
    VariableDeclarationKind,
};
use mist_syntax::{
    ast::{self, Spanned},
    AstNode, SourceSpan,
};

#[salsa::tracked]
pub fn hover(db: &dyn crate::Db, file: SourceFile, byte_offset: usize) -> Option<HoverResult> {
    let mut visitor = HoverFinder::new(db, byte_offset);

    let root = file.root(db);
    let token = root.syntax().token_at_offset(byte_offset.try_into().unwrap()).left_biased()?;
    let item = token.parent_ancestors().find_map(ast::Item::cast)?;
    let ast_map = file.ast_map(db);
    let ast_id = ast_map.ast_id(file, &item);
    let def = Def::new(db, DefKind::new(db, ast_id)?);

    match PostOrderWalk::walk_def(db, file, &mut visitor, def) {
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
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Option<HoverResult>> {
        if reference.contains_pos(self.byte_offset) {
            match field {
                Field::AdtField(af) => {
                    let ty = pretty::ty(&*vcx.cx, self.db, false, vcx.cx.field_ty(field));
                    let kind = match af.adt().kind() {
                        AdtKind::Struct(_) => Name::new("struct"),
                        AdtKind::Enum => todo!(),
                    };
                    break_code(
                        [
                            format!("{} {}", kind, af.adt().name(self.db)),
                            format!("{}: {ty}", field.name(self.db)),
                        ],
                        Some(reference.span()),
                    )
                }
                Field::Builtin(bf) => match bf {
                    BuiltinField::List(list_ty, _)
                    | BuiltinField::Set(list_ty, _)
                    | BuiltinField::MultiSet(list_ty, _) => {
                        let list_ty = pretty::ty(&*vcx.cx, self.db, false, list_ty);
                        let ty = pretty::ty(&*vcx.cx, self.db, false, vcx.cx.field_ty(field));
                        break_code(
                            [format!("{list_ty}"), format!("{}: {ty}", bf.name())],
                            Some(reference.span()),
                        )
                    }
                },
                Field::Undefined => break_code(["?undefined".to_string()], Some(reference.span())),
            }
        } else {
            ControlFlow::Continue(())
        }
    }
    fn visit_struct_field(
        &mut self,
        _vcx: &VisitContext,
        field: StructField,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Option<HoverResult>> {
        if reference.contains_pos(self.byte_offset) {
            let ast = field.ast_node(self.db);
            let ty = if let Some(ty) = ast.ty() {
                ty.syntax().text().to_string()
            } else {
                String::new()
            };
            break_code(
                [
                    format!("struct {}", field.parent_struct(self.db).name(self.db)),
                    format!("{}: {ty}", field.name(self.db)),
                ],
                Some(reference.span()),
            )
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_var(
        &mut self,
        vcx: &VisitContext,
        var: VariableIdx,
        span: SourceSpan,
    ) -> ControlFlow<Option<HoverResult>> {
        if span.contains_pos(self.byte_offset) {
            let name = vcx.cx.var_name(var);
            let ty = pretty::ty(&*vcx.cx, self.db, false, vcx.cx.var_ty(self.db, var));

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

    fn visit_expr(
        &mut self,
        vcx: &VisitContext,
        expr: ExprIdx,
    ) -> ControlFlow<Option<HoverResult>> {
        let span = vcx.source_map.expr_span(&vcx.cx, expr);
        if span.contains_pos(self.byte_offset) {
            let expr = vcx.cx.original_expr(expr);
            let ty = pretty::ty(&*vcx.cx, self.db, false, expr.ty);
            if let ExprData::Result = &expr.data {
                return break_code([format!("result: {ty}")], None);
            } else if let ExprData::Self_ = &expr.data {
                return break_code([format!("self: {ty}")], None);
            } else {
                return break_code([ty], Some(span));
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, vcx: &VisitContext, ty: TypeSrc) -> ControlFlow<Option<HoverResult>> {
        let span = match &vcx.source_map[ty] {
            src if src.span().contains(self.byte_offset) => src.span(),
            _ => return ControlFlow::Continue(()),
        };

        let pretty_ty = pretty::ty(&*vcx.cx, self.db, false, ty.ty(self.db));

        let s = match ty.type_ref(self.db) {
            Some(TypeRefKind::Path(_)) => format!("struct {pretty_ty}"),
            _ => pretty_ty,
        };

        break_code([s], Some(span))
    }
}

fn break_code<const N: usize>(
    code: [String; N],
    span: Option<SourceSpan>,
) -> ControlFlow<Option<HoverResult>> {
    ControlFlow::Break(Some(HoverResult::new(code.map(HoverElement::Code).to_vec(), span)))
}
