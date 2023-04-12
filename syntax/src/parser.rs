use std::ops::ControlFlow;

use itertools::Itertools;
use miette::Diagnostic;
use rowan::{Checkpoint, GreenNodeBuilder};
use thiserror::Error;

use crate::{
    ast::{AttrFlags, SourceFile},
    support::{AstNode, SourceSpan},
    SyntaxKind::{self, *},
    SyntaxNode, T,
};

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
#[error("{kind}")]
pub struct ParseError {
    #[source_code]
    pub input: String,
    #[label("{}", label.as_deref().unwrap_or("here"))]
    pub span: SourceSpan,
    pub label: Option<String>,
    #[help]
    pub help: Option<String>,
    pub kind: ParseErrorKind,
}

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
pub enum ParseErrorKind {
    #[error("expected '{0}'")]
    Context(String),
}

pub struct Parser<'src> {
    src: &'src str,
    tokens: Vec<(SyntaxKind, &'src str, SourceSpan)>,
    builder: GreenNodeBuilder<'static>,
    errors: Vec<ParseError>,
    has_bumped_after_ws_skip: bool,
    pre_whitespace_span: SourceSpan,
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Self {
        let mut tokens = logos::Lexer::new(src)
            .spanned()
            .map(|(kind, span)| {
                (
                    kind,
                    &src[span.clone()],
                    SourceSpan::new_start_end(span.start, span.end),
                )
            })
            .collect_vec();
        if let Some((WHITESPACE, _, _)) = tokens.last() {
        } else {
            tokens.push((
                WHITESPACE,
                "",
                SourceSpan::new_start_end(src.len().max(1) - 1, src.len()),
            ));
        }
        tokens.reverse();

        let mut parser = Self {
            src,
            tokens,
            builder: Default::default(),
            errors: Default::default(),
            pre_whitespace_span: SourceSpan::new_start_end(0, 0),
            has_bumped_after_ws_skip: false,
        };

        for (kind, _, span) in parser.tokens.clone() {
            if kind == ERROR {
                parser.push_error(
                    Some(span),
                    Some("invalid token"),
                    None,
                    ParseErrorKind::Context("valid token".to_string()),
                );
            }
        }

        parser
    }

    pub fn parse(mut self) -> (SourceFile, Vec<ParseError>) {
        self.builder.start_node(SOURCE_FILE.into());
        loop {
            if !self.maybe_item() {
                match self.current() {
                    None => {
                        self.builder.finish_node();

                        let node = SyntaxNode::new_root(self.builder.finish());

                        return (SourceFile::cast(node).unwrap(), self.errors);
                    }
                    _ => {
                        self.push_error(
                            None,
                            Some("unknown start to item"),
                            None,
                            ParseErrorKind::Context("start of item".to_string()),
                        );
                        self.bump();
                    }
                }
            }
        }
    }

    fn attrs(&mut self) -> Checkpoint {
        let attr_checkpoint = self.builder.checkpoint();
        let mut attr_seen = AttrFlags::empty();
        self.builder.start_node(ATTRS.into());
        loop {
            self.skip_ws();
            match self.current() {
                Some(T![pure]) => {
                    if attr_seen.is_pure() {
                        self.push_error(
                            None,
                            Some("repeated pure attr"),
                            Some("consider removing one of them"),
                            ParseErrorKind::Context("attr".to_string()),
                        );
                    }
                    attr_seen.insert(AttrFlags::PURE);
                    self.builder.start_node(ATTR.into());
                    self.bump();
                    self.builder.finish_node();
                }
                Some(T![ghost]) => {
                    if attr_seen.is_ghost() {
                        self.push_error(
                            None,
                            Some("repeated ghost attr"),
                            Some("consider removing one of them"),
                            ParseErrorKind::Context("attr".to_string()),
                        );
                    }
                    attr_seen.insert(AttrFlags::GHOST);
                    self.builder.start_node(ATTR.into());
                    self.bump();
                    self.builder.finish_node();
                }
                _ => break,
            }
        }
        self.builder.finish_node();
        attr_checkpoint
    }

    fn maybe_item(&mut self) -> bool {
        let attrs_checkpoint = self.attrs();

        match self.current() {
            Some(T![fn]) => self.fn_def(attrs_checkpoint),
            Some(T![const]) => self.const_def(attrs_checkpoint),
            Some(T![struct]) => self.struct_def(attrs_checkpoint),
            Some(T![invariant]) => self.type_invariant(attrs_checkpoint),
            Some(T![macro]) => self.macro_def(attrs_checkpoint),
            Some(T![let]) => {
                self.push_error(
                    None,
                    Some("let found as top-level"),
                    Some("consider using a 'const' instead"),
                    ParseErrorKind::Context("top-level item".to_string()),
                );
                self.let_stmt()
            }
            _ => return false,
        }
        true
    }

    fn fn_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![fn]));
        self.builder.start_node_at(attr_checkpoint, FN.into());
        self.bump();

        self.name();
        self.param_list();

        self.skip_ws();

        if let Some(T![->]) = self.current() {
            self.bump();
            self.ty();
        }

        let mut seen_decreases = false;

        loop {
            self.skip_ws();
            match self.current() {
                Some(T![requires] | T![req]) => {
                    self.builder.start_node(REQUIRES.into());
                    self.bump();
                    self.comma_expr(Location::NO_STRUCT);
                    self.builder.finish_node();
                }
                Some(T![ensures] | T![ens]) => {
                    self.builder.start_node(ENSURES.into());
                    self.bump();
                    self.comma_expr(Location::NO_STRUCT);
                    self.builder.finish_node();
                }
                Some(T![decreases] | T![dec]) => {
                    if seen_decreases {
                        // TODO: Report repeated decreases
                    }
                    seen_decreases = true;

                    self.builder.start_node(DECREASES.into());
                    self.bump();
                    self.skip_ws();
                    match self.current() {
                        Some(T![_]) => self.bump(),
                        _ => self.expr(Location::NO_STRUCT),
                    }
                    self.builder.finish_node();
                }
                _ => break,
            }
        }

        match self.current() {
            Some(T![;]) => self.bump(),
            Some(T!['{']) => self.block(),
            _ => self.push_error(
                Some(self.pre_whitespace_span.set_len(1)),
                Some("expected a block"),
                None,
                ParseErrorKind::Context("{".to_string()),
            ),
        }

        self.builder.finish_node();
    }

    fn const_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![const]));
        self.builder.start_node_at(attr_checkpoint, CONST.into());
        self.bump();

        self.name();

        let post_span = self.current_span();
        self.skip_ws();
        match self.current() {
            Some(T![=]) => {
                self.bump();
                self.expr(Location::NONE);
                self.semicolon();
            }
            Some(T![;]) => {
                self.semicolon();
            }
            _ => self.push_error(
                Some(post_span),
                Some("expected a value with '=', or ';'"),
                None,
                ParseErrorKind::Context("constant value".to_string()),
            ),
        }

        self.builder.finish_node();
    }

    fn struct_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![struct]));
        self.builder.start_node_at(attr_checkpoint, STRUCT.into());
        self.bump();

        self.name();

        self.expect_control(T!['{']);

        self.comma_sep(
            |t| t == T!['}'],
            |this| match this.current() {
                Some(T![ident]) => {
                    this.builder.start_node(STRUCT_FIELD.into());
                    this.name();
                    this.skip_ws();
                    this.expect_control(T![:]);
                    this.ty();
                    this.builder.finish_node();
                    ControlFlow::Continue(())
                }

                Some(T![ghost]) => {
                    this.builder.start_node(STRUCT_FIELD.into());
                    this.attrs();
                    this.name();
                    this.skip_ws();
                    this.expect_control(T![:]);
                    this.ty();
                    this.builder.finish_node();
                    ControlFlow::Continue(())
                }
                Some(T!['}']) => ControlFlow::Break(()),
                _ => {
                    this.push_error(
                        None,
                        Some("unexpected token"),
                        None,
                        ParseErrorKind::Context("parsing struct field".to_string()),
                    );
                    ControlFlow::Break(())
                }
            },
        );

        self.expect_control(T!['}']);

        self.builder.finish_node();
    }

    fn type_invariant(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![invariant]));
        self.builder
            .start_node_at(attr_checkpoint, TYPE_INVARIANT.into());
        self.bump();

        self.name();

        self.block();

        self.builder.finish_node();
    }

    fn macro_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![macro]));
        self.builder.start_node_at(attr_checkpoint, MACRO.into());
        self.bump();

        self.name();

        self.skip_ws();
        self.param_list();

        self.block();

        self.builder.finish_node();
    }

    fn name(&mut self) {
        self.skip_ws();

        self.builder.start_node(NAME.into());

        match self.current() {
            Some(IDENT) => self.bump(),
            None => self.unexpected_eof(),
            _ => self.push_error(
                None,
                Some("expected a name"),
                None,
                ParseErrorKind::Context("name".to_string()),
            ),
        }

        self.builder.finish_node();
    }

    fn param_list(&mut self) {
        self.builder.start_node(PARAM_LIST.into());

        if let Some(L_PAREN) = self.current() {
            self.bump();
        } else {
            self.push_error(
                None,
                Some("consider adding parameters here"),
                None,
                ParseErrorKind::Context("function parameters".to_string()),
            );
        }

        self.comma_sep(
            |t| t == T![')'],
            |this| {
                let attrs_checkpoint = this.attrs();
                if let Some(T![ident]) = this.current() {
                    this.builder.start_node_at(attrs_checkpoint, PARAM.into());
                    this.name();
                    this.skip_ws();
                    if let Some(T![:]) = this.current() {
                        this.bump();
                        this.ty();
                    }
                    this.builder.finish_node();
                }

                ControlFlow::Continue(())
            },
        );

        self.expect_control(T![')']);

        // #[derive(Debug, PartialEq)]
        // enum LastThing {
        //     Comma,
        //     Param,
        //     Nothing,
        // }
        // let mut last = LastThing::Nothing;

        // loop {
        //     self.skip_ws();

        //     match self.current() {
        //         Some(T![')']) => {
        //             self.bump();
        //             break;
        //         }
        //         Some(IDENT) => {
        //             self.builder.start_node(PARAM.into());
        //             self.name();
        //             self.skip_ws();
        //             self.expect_control(COLON);
        //             self.ty();
        //             self.builder.finish_node();

        //             last = LastThing::Param;
        //         }
        //         Some(T![,]) => {
        //             match last {
        //                 LastThing::Comma => {
        //                     self.push_error(
        //                         None,
        //                         Some("repeated comma"),
        //                         Some("delete one of them"),
        //                         ParseErrorKind::Context("a parameter".to_string()),
        //                     );
        //                     self.bump();
        //                 }
        //                 LastThing::Param => {
        //                     self.bump();
        //                 }
        //                 LastThing::Nothing => {
        //                     self.push_error(
        //                         None,
        //                         Some("comma before first parameter"),
        //                         Some("add a parameter before"),
        //                         ParseErrorKind::Context("a parameter".to_string()),
        //                     );
        //                     self.bump();
        //                 }
        //             }
        //             self.bump();
        //             last = LastThing::Comma;
        //         }
        //         None => {
        //             self.unexpected_eof();
        //             break;
        //         }
        //         _ => {
        //             self.push_error(
        //                 None,
        //                 Some("consider adding a parameter here"),
        //                 None,
        //                 ParseErrorKind::Context("function parameters".to_string()),
        //             );
        //             self.bump();
        //         }
        //     }
        // }

        self.builder.finish_node();
    }

    fn ty(&mut self) {
        self.skip_ws();
        let is_ref = if let Some(T![&]) = self.current() {
            self.builder.start_node(REF_TYPE.into());
            self.bump();
            true
        } else {
            false
        };

        self.skip_ws();
        if let Some(T![mut]) = self.current() {
            if !is_ref {
                self.push_error(
                    None,
                    Some("'mut' is only allowed on references. add '&' here"),
                    None,
                    ParseErrorKind::Context("type".to_string()),
                );
            }
            self.bump();
        };

        if is_ref {
            self.ty();
            self.builder.finish_node();
            return;
        }

        self.skip_ws();
        if let Some(T![ghost]) = self.current() {
            self.builder.start_node(GHOST_TYPE.into());
            self.bump();
            self.ty();
            self.builder.finish_node();
            return;
        }

        self.skip_ws();
        if let Some(T!['[']) = self.current() {
            self.builder.start_node(LIST_TYPE.into());
            self.bump();
            self.ty();
            self.expect_control(T![']']);
            self.builder.finish_node();
            return;
        }

        let checkpoint = self.builder.checkpoint();
        self.skip_ws();
        match self.current() {
            Some(IDENT) => {
                self.builder.start_node(NAMED_TYPE.into());
                self.name();
                self.builder.finish_node();
            }
            Some(T![int] | T![bool]) => {
                self.builder.start_node(PRIMITIVE.into());
                self.bump();
                self.builder.finish_node();
            }
            _ => self.push_error(
                None,
                Some("specify the type here"),
                None,
                ParseErrorKind::Context("a type".to_string()),
            ),
        }

        self.skip_ws();
        if let Some(T![?]) = self.current() {
            self.builder.start_node_at(checkpoint, OPTIONAL.into());
            self.bump();
            self.builder.finish_node();
        }
    }

    fn block(&mut self) {
        self.skip_ws();
        self.builder.start_node(BLOCK_EXPR.into());
        self.expect_control(T!['{']);

        let mut trailing = None;

        loop {
            self.skip_ws();
            match self.current() {
                Some(R_CURLY) => {
                    self.bump();
                    break;
                }
                Some(T![;]) => {
                    if let Some(checkpoint) = trailing.take() {
                        self.builder.start_node_at(checkpoint, EXPR_STMT.into());
                        self.bump();
                        self.builder.finish_node();
                    }
                }
                None => {
                    self.unexpected_eof();
                    break;
                }
                _ => {
                    if let Some(checkpoint) = trailing.take() {
                        self.push_error(
                            Some(self.pre_whitespace_span.set_len(0)),
                            Some("expected ';'"),
                            Some("consider adding a ';' to mark the end of the expression"),
                            ParseErrorKind::Context(";".to_string()),
                        );
                        self.builder.start_node_at(checkpoint, EXPR_STMT.into());
                        self.builder.finish_node();
                    }
                    match self.stmt() {
                        StatementParsed::Expression(e) => trailing = Some(e),
                        StatementParsed::Statement => {}
                    }
                }
            }
        }

        self.builder.finish_node();
    }

    fn stmt(&mut self) -> StatementParsed {
        self.skip_ws();

        match self.current() {
            Some(T![let]) => self.let_stmt(),
            Some(T![assume]) => self.assume_stmt(),
            Some(T![assert]) => self.assert_stmt(),
            Some(T![return]) => self.return_stmt(),
            Some(T![while]) => {
                self.while_stmt();
            }
            Some(T![if]) => {
                let checkpoint = self.builder.checkpoint();
                // self.builder.start_node(EXPR_STMT.into());
                self.if_expr();
                // self.builder.finish_node();
                return StatementParsed::Expression(checkpoint);
            }
            Some(t) if is_start_of_expr(t) => {
                let expr_checkpoint = self.builder.checkpoint();
                self.expr(Location::NONE);

                // self.skip_ws();
                // if let Some(T![;]) = self.current() {
                //     self.builder
                //         .start_node_at(expr_checkpoint, EXPR_STMT.into());
                //     self.bump();
                //     self.builder.finish_node();
                // } else {
                //     // tail expr
                return StatementParsed::Expression(expr_checkpoint);
                // }
            }
            None => self.unexpected_eof(),
            _ => {
                if !self.maybe_item() {
                    self.push_error(
                        None,
                        Some("expected a statement here"),
                        None,
                        ParseErrorKind::Context("statement".to_string()),
                    );
                    self.bump();
                }
            }
        }

        StatementParsed::Statement
    }

    fn let_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![let]));

        self.builder.start_node(LET_STMT.into());
        self.bump();

        self.name();

        self.skip_ws();
        if let Some(T![:]) = self.current() {
            self.bump();
            self.ty();
        }

        self.skip_ws();
        if let Some(T![=]) = self.current() {
            self.bump();
            self.expr(Location::NONE);
        }

        self.semicolon();

        self.builder.finish_node();
    }

    fn assume_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![assume]));

        self.builder.start_node(ASSUME_STMT.into());
        self.bump();

        self.comma_expr(Location::NONE);
        self.semicolon();

        self.builder.finish_node();
    }

    fn assert_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![assert]));

        self.builder.start_node(ASSERT_STMT.into());
        self.bump();

        self.comma_expr(Location::NONE);
        self.semicolon();

        self.builder.finish_node();
    }

    fn return_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![return]));

        self.builder.start_node(RETURN_STMT.into());
        self.bump();

        self.expr(Location::NONE);
        self.semicolon();

        self.builder.finish_node();
    }

    fn while_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![while]));

        self.builder.start_node(WHILE_STMT.into());
        self.bump();

        self.expr(Location::NO_STRUCT);

        let mut seen_decreases = false;

        loop {
            self.skip_ws();
            match self.current() {
                Some(T![invariant] | T![inv]) => {
                    self.builder.start_node(INVARIANT.into());

                    self.bump();
                    self.comma_expr(Location::NO_STRUCT);

                    self.builder.finish_node();
                }
                Some(T![decreases] | T![dec]) => {
                    if seen_decreases {
                        // TODO: Report repeated decreases
                    }
                    seen_decreases = true;

                    self.builder.start_node(DECREASES.into());
                    self.bump();
                    self.skip_ws();
                    match self.current() {
                        Some(T![_]) => self.bump(),
                        _ => self.expr(Location::NO_STRUCT),
                    }
                    self.builder.finish_node();
                }
                _ => break,
            }
        }

        self.block();

        self.builder.finish_node();
    }

    fn comma_expr(&mut self, loc: Location) {
        self.builder.start_node(COMMA_EXPR.into());
        self.expr(loc);

        loop {
            self.skip_ws();
            if let Some(T![,]) = self.current() {
                self.bump();
                self.builder.finish_node();
            } else {
                self.builder.finish_node();
                break;
            }
            self.builder.start_node(COMMA_EXPR.into());
            self.expr(loc);
        }
    }

    fn expr(&mut self, loc: Location) {
        self.expr_bp(loc, 0)
    }
    fn expr_bp(&mut self, loc: Location, min_bp: u8) {
        self.skip_ws();

        // eprintln!(
        //     "Start parsing expr with first token being: {:?}",
        //     self.current()
        // );

        let mut lhs = self.builder.checkpoint();
        match self.current() {
            Some(T![false] | T![true]) => {
                self.builder.start_node(LITERAL.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(T![result]) => {
                self.builder.start_node(RESULT_EXPR.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(T![ident]) => {
                let checkpoint = self.builder.checkpoint();
                self.name();

                self.skip_ws();

                match self.current() {
                    Some(T!['{']) if !loc.contains(Location::NO_STRUCT) => {
                        self.builder.start_node_at(checkpoint, STRUCT_EXPR.into());

                        self.expect_control(T!['{']);

                        self.comma_sep(
                            |t| t == T!['}'],
                            |this| match this.current() {
                                Some(T![ident]) => {
                                    this.builder.start_node(STRUCT_EXPR_FIELD.into());
                                    this.name();
                                    this.expect_control(T![:]);
                                    this.expr_bp(Location::NONE, 0);
                                    this.builder.finish_node();
                                    ControlFlow::Continue(())
                                }
                                Some(T!['}']) => ControlFlow::Break(()),
                                _ => {
                                    this.push_error(
                                        None,
                                        Some("unexpected token"),
                                        None,
                                        ParseErrorKind::Context(
                                            "parsing struct expr field".to_string(),
                                        ),
                                    );
                                    ControlFlow::Break(())
                                }
                            },
                        );

                        self.expect_control(T!['}']);

                        self.builder.finish_node();
                    }
                    _ => {
                        self.builder.start_node_at(checkpoint, IDENT_EXPR.into());
                        self.builder.finish_node();
                    }
                }
            }
            Some(T![null]) => {
                self.builder.start_node(NULL_EXPR.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(INT_NUMBER) => {
                self.builder.start_node(LITERAL.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(T!['[']) => {
                self.builder.start_node(LIST_EXPR.into());
                self.bump();
                self.comma_sep(
                    |t| t == T![']'],
                    |this| {
                        this.builder.start_node(COMMA_EXPR.into());
                        this.expr_bp(Location::NONE, 0);
                        this.builder.finish_node();
                        ControlFlow::Continue(())
                    },
                );
                self.expect_control(T![']']);
                self.builder.finish_node();
            }
            Some(T!['(']) => {
                self.builder.start_node(PAREN_EXPR.into());
                self.bump();
                self.expr_bp(Location::NONE, 0);
                self.expect_control(T![')']);
                self.builder.finish_node();
            }
            Some(T![if]) => {
                self.if_expr();
            }
            Some(t) => {
                if let Some((op, (), r_bp)) = prefix_binding_power(Some(t)) {
                    match op {
                        T![&] => {
                            self.builder.start_node(REF_EXPR.into());
                            self.bump();

                            self.skip_ws();
                            if let Some(T![mut]) = self.current() {
                                self.bump();
                            }

                            self.expr_bp(loc, r_bp);
                            self.builder.finish_node();
                        }
                        T![forall] | T![exists] => {
                            self.builder.start_node(QUANTIFIER_EXPR.into());
                            self.builder.start_node(QUANTIFIER.into());
                            self.bump();
                            self.builder.finish_node();
                            self.skip_ws();
                            self.param_list();
                            self.expr_bp(loc, r_bp);
                            self.builder.finish_node();
                        }
                        _ => {
                            self.builder.start_node(PREFIX_EXPR.into());
                            self.bump();

                            self.expr_bp(loc, r_bp);
                            self.builder.finish_node();
                        }
                    }
                } else {
                    eprintln!("unknown start of expr {t:?}");
                    self.push_error(
                        None,
                        Some(&format!("unknown start of expr: '{t}'")),
                        None,
                        ParseErrorKind::Context("start of expr".to_string()),
                    );
                    self.bump();
                    return;
                }
            }
            None => {
                self.unexpected_eof();
                return;
            }
        };

        loop {
            self.skip_ws();
            if let Some((op, l_bp, ())) = postfix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }

                let next = self.builder.checkpoint();
                match op {
                    T!['('] => {
                        self.builder.start_node_at(lhs, CALL_EXPR.into());
                        self.arg_list();
                        self.builder.finish_node();
                    }
                    T!['['] => {
                        self.builder.start_node_at(lhs, INDEX_EXPR.into());
                        self.bump();
                        self.expr(Location::NONE);
                        self.expect_control(T![']']);
                        self.builder.finish_node();
                    }
                    T![.] => {
                        self.builder.start_node_at(lhs, FIELD_EXPR.into());
                        self.bump();
                        self.name();
                        self.builder.finish_node();
                    }
                    _ => todo!(),
                }
                // lhs = next;

                continue;
            }
            if let Some((op, l_bp, r_bp)) = infix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }
                let next = self.builder.checkpoint();

                match op {
                    T![..] => {
                        self.builder.start_node_at(lhs, RANGE_EXPR.into());
                        self.bump();
                        if self.current().map(is_start_of_expr) == Some(true) {
                            self.expr_bp(loc, r_bp);
                        }
                    }
                    op => {
                        self.builder.start_node_at(lhs, BIN_EXPR.into());
                        self.bump();
                        // eprintln!("normal infix op was: '{op}'");
                        self.expr_bp(loc, r_bp);
                    }
                }
                self.builder.finish_node();
                // lhs = next;
                continue;
            };

            break;
        }
    }

    fn if_expr(&mut self) {
        assert_eq!(self.current(), Some(T![if]));
        self.builder.start_node(IF_EXPR.into());
        self.bump();

        self.expr(Location::NO_STRUCT);
        self.block();

        self.skip_ws();
        if let Some(T![else]) = self.current() {
            self.bump();
            self.skip_ws();
            if let Some(T![if]) = self.current() {
                self.if_expr();
            } else {
                self.block();
            }
        }

        self.builder.finish_node();
    }

    fn arg_list(&mut self) {
        self.builder.start_node(ARG_LIST.into());

        self.expect_control(T!['(']);

        self.comma_sep(
            |t| t == T![')'],
            |this| {
                this.builder.start_node(ARG.into());
                this.expr_bp(Location::NONE, 0);
                this.builder.finish_node();
                ControlFlow::Continue(())
            },
        );

        // loop {
        //     self.skip_ws();
        //     match self.current() {
        //         Some(T![')']) => {
        //             self.bump();
        //             break;
        //         }
        //         Some(T![;]) => {
        //             self.push_error(
        //                 None,
        //                 Some("expected an expression here"),
        //                 Some("consider closing the function call with a ')'"),
        //                 ParseErrorKind::Context("start of expression".to_string()),
        //             );
        //             break;
        //         }
        //         None => {
        //             self.unexpected_eof();
        //             break;
        //         }
        //         _ => {
        //             self.builder.start_node(ARG.into());
        //             self.expr_bp(Location::NONE, 0);
        //             match self.current() {
        //                 Some(COMMA) => {
        //                     self.bump();
        //                     self.builder.finish_node();
        //                 }
        //                 _ => self.builder.finish_node(),
        //             }
        //         }
        //     }
        // }

        self.expect_control(T![')']);

        self.builder.finish_node();
    }

    fn comma_sep<S, F>(&mut self, terminator: S, mut f: F)
    where
        S: Fn(SyntaxKind) -> bool,
        F: FnMut(&mut Self) -> ControlFlow<()>,
    {
        #[derive(Debug, PartialEq)]
        enum LastThing {
            Comma,
            Item,
            Nothing,
        }
        let mut last = LastThing::Nothing;

        loop {
            self.skip_ws();

            match self.current() {
                Some(T![,]) => {
                    match last {
                        LastThing::Comma => {
                            self.push_error(
                                None,
                                Some("repeated comma"),
                                Some("delete one of them"),
                                ParseErrorKind::Context("a parameter".to_string()),
                            );
                            self.bump();
                        }
                        LastThing::Item => {
                            self.bump();
                        }
                        LastThing::Nothing => {
                            self.push_error(
                                None,
                                Some("comma before first parameter"),
                                Some("add a parameter before"),
                                ParseErrorKind::Context("a parameter".to_string()),
                            );
                            self.bump();
                        }
                    }
                    last = LastThing::Comma;
                }
                Some(t) if terminator(t) => {
                    break;
                }
                None => {
                    self.unexpected_eof();
                    break;
                }
                _ => {
                    self.skip_ws();
                    let before = self.current();
                    if last == LastThing::Item {
                        self.push_error(
                            Some(self.pre_whitespace_span.set_len(1)),
                            Some("missing ','"),
                            None,
                            ParseErrorKind::Context("',' separated".to_string()),
                        )
                    }
                    match f(self) {
                        ControlFlow::Continue(_) => {}
                        ControlFlow::Break(_) => break,
                    }
                    last = LastThing::Item;
                    if before == self.current() {
                        self.bump();
                    }
                }
            }
        }
    }

    fn semicolon(&mut self) {
        self.expect_control(T![;])
    }

    fn expect_control(&mut self, token: SyntaxKind) {
        let span = self.pre_whitespace_span;
        self.skip_ws();
        match self.current() {
            Some(t) if t == token => self.bump(),
            _ => self.push_error(
                Some(span.set_len(1)),
                Some(&format!("help: add '{token}' here")),
                None,
                ParseErrorKind::Context(token.to_string()),
            ),
        }
    }

    fn push_error(
        &mut self,
        span: Option<SourceSpan>,
        label: Option<&str>,
        help: Option<&str>,
        kind: ParseErrorKind,
    ) {
        let err = ParseError {
            input: self.src.to_string(),
            span: span.unwrap_or_else(|| self.current_span()),
            label: label.map(|s| s.to_string()),
            help: help.map(|s| s.to_string()),
            kind,
        };
        #[cfg(debug_assertions)]
        eprintln!("{:?}", miette::Error::new(err.clone()));
        self.errors.push(err)
    }
    fn bump(&mut self) {
        let (kind, text, _) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text);
        self.has_bumped_after_ws_skip = true;
    }
    fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|(kind, _, _)| *kind)
    }
    fn current_span(&self) -> SourceSpan {
        self.tokens
            .last()
            .map(|(_, _, span)| *span)
            .unwrap_or(self.pre_whitespace_span)
    }
    fn skip_ws(&mut self) {
        if self.has_bumped_after_ws_skip {
            self.pre_whitespace_span = self.current_span();
        }
        self.has_bumped_after_ws_skip = false;
        while matches!(self.current(), Some(WHITESPACE | COMMENT)) {
            let (kind, text, _) = self.tokens.pop().unwrap();
            self.builder.token(kind.into(), text);
        }
    }

    fn unexpected_eof(&mut self) {
        self.push_error(
            None,
            Some("ended here"),
            None,
            ParseErrorKind::Context("rest of program".to_string()),
        )
    }
}

fn is_start_of_expr(token: SyntaxKind) -> bool {
    matches!(
        token,
        T![ident]
            | T![true]
            | T![false]
            | T![result]
            | T![&]
            | T![!]
            | T!['(']
            | T!['[']
            | INT_NUMBER,
    )
}

#[derive(Debug, Clone, Copy)]
enum StatementParsed {
    Expression(Checkpoint),
    Statement,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Location: u32 {
        const NONE = 0b000;
        const NO_STRUCT = 0b001;
    }
}

// TODO: https://github.com/rust-lang/rust-analyzer/blob/20b0ae4afe3f9e4c5ee5fc90586e55f2515f403b/crates/syntax/src/ast/prec.rs

fn prefix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, (), u8)> {
    let op = op?;
    match op {
        T![&] | T![!] => Some((op, (), 8)),
        // T![+] |
        T![-] => Some((op, (), 9)),
        T![forall] | T![exists] => Some((op, (), 10)),
        _ => None,
    }
}

fn postfix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, u8, ())> {
    let op = op?;
    let (l, r) = match op {
        // T![!] => (11, ()),
        T!['['] => (11, ()),
        T!['('] => (11, ()),
        T![.] => (14, ()),
        _ => return None,
    };

    Some((op, l, r))
}

fn infix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, u8, u8)> {
    let op = op?;
    let (l, r) = match op {
        T![=] => (2, 1),
        T![&&] => (2, 1),
        T![||] => (2, 1),
        T![==] | T![!=] => (4, 3),
        T![>] | T![<] => (4, 3),
        T![>=] | T![<=] => (4, 3),
        T![..] => (4, 3),
        T![+] | T![-] => (5, 6),
        T![*] | T![/] => (7, 8),
        _ => return None,
    };

    Some((op, l, r))
}
