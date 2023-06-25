#[cfg(test)]
mod tests;

use std::ops::ControlFlow;

use derive_new::new;
use mist_core::{
    def::{Def, DefKind, StructField},
    file::SourceFile,
    hir::{pretty, ExprData, ExprIdx, Path, TypeRefKind, TypeSrc, VariableIdx},
    mono::types::{Type, TypeData},
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
            let field_ty = vcx.lower_ty(self.db, vcx.cx.field_ty(field));
            match field {
                Field::AdtField(af) => {
                    let parent_ty = vcx.lower_ty(self.db, vcx.cx.adt_ty(af.adt()).unwrap());
                    let kind = match parent_ty.kind(self.db) {
                        TypeData::Adt(adt) => match adt.kind(self.db) {
                            AdtKind::Struct(_, _) => "struct".to_string(),
                            AdtKind::Enum => "enum".to_string(),
                        },
                        _ => "<kind>".to_string(),
                    };
                    break_code(
                        [
                            format!("{} {}", kind, parent_ty.display(self.db)),
                            format!("{}: {}", field.name(self.db), field_ty.display(self.db)),
                        ],
                        Some(reference.span()),
                    )
                }
                Field::Builtin(bf) => match bf {
                    BuiltinField::List(list_ty, _)
                    | BuiltinField::Set(list_ty, _)
                    | BuiltinField::MultiSet(list_ty, _) => {
                        let list_ty = vcx.lower_ty(self.db, list_ty);
                        break_code(
                            [
                                list_ty.display(self.db).to_string(),
                                format!("{}: {}", bf.name(), field_ty.display(self.db)),
                            ],
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

    fn visit_ty(
        &mut self,
        vcx: &VisitContext,
        ts: TypeSrc,
        ty: Type,
    ) -> ControlFlow<Option<HoverResult>> {
        let span = match &vcx.source_map[ts] {
            src if src.span().contains(self.byte_offset) => src.span(),
            _ => return ControlFlow::Continue(()),
        };

        let pretty_ty = ty.display(self.db);
        let s = match ts.type_ref(self.db) {
            Some(TypeRefKind::Path(Path::Adt(_))) => format!("struct {pretty_ty}"),
            _ => pretty_ty.to_string(),
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
