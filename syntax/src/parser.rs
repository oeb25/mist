use std::ops::ControlFlow;

use itertools::Itertools;
use miette::Diagnostic;
use rowan::{Checkpoint, GreenNodeBuilder};
use thiserror::Error;
use tracing::error;

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
        let attr_checkpoint = self.checkpoint();
        let mut attr_seen = AttrFlags::empty();
        self.start_node(ATTRS, |this| loop {
            match this.current() {
                Some(T![pure]) => {
                    if attr_seen.is_pure() {
                        this.push_error(
                            None,
                            Some("repeated pure attr"),
                            Some("consider removing one of them"),
                            ParseErrorKind::Context("attr".to_string()),
                        );
                    }
                    attr_seen.insert(AttrFlags::PURE);
                    this.start_node(ATTR, |this| this.bump());
                }
                Some(T![ghost]) => {
                    if attr_seen.is_ghost() {
                        this.push_error(
                            None,
                            Some("repeated ghost attr"),
                            Some("consider removing one of them"),
                            ParseErrorKind::Context("attr".to_string()),
                        );
                    }
                    attr_seen.insert(AttrFlags::GHOST);
                    this.start_node(ATTR, |this| this.bump());
                }
                _ => break,
            }
        });
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
        self.start_node_at(attr_checkpoint, FN, |this| {
            this.bump();

            this.current();
            this.name();
            this.current();
            this.param_list();

            if let Some(T![->]) = this.current() {
                this.bump();
                this.ty();
            }

            let mut seen_decreases = false;

            loop {
                match this.current() {
                    Some(T![requires] | T![req]) => {
                        this.start_node(REQUIRES, |this| {
                            this.bump();
                            this.comma_expr(Location::NO_STRUCT);
                        });
                    }
                    Some(T![ensures] | T![ens]) => {
                        this.start_node(ENSURES, |this| {
                            this.bump();
                            this.comma_expr(Location::NO_STRUCT);
                        });
                    }
                    Some(T![decreases] | T![dec]) => {
                        if seen_decreases {
                            // TODO: Report repeated decreases
                        }
                        seen_decreases = true;

                        this.start_node(DECREASES, |this| {
                            this.bump();
                            match this.current() {
                                Some(T![_]) => this.bump(),
                                _ => this.expr(Location::NO_STRUCT),
                            }
                        });
                    }
                    _ => break,
                }
            }

            match this.current() {
                Some(T![;]) => this.bump(),
                Some(T!['{']) => this.block(),
                _ => this.push_error(
                    Some(this.pre_whitespace_span.set_len(1)),
                    Some("expected a block"),
                    None,
                    ParseErrorKind::Context("{".to_string()),
                ),
            }
        });
    }

    fn const_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![const]));
        self.start_node_at(attr_checkpoint, CONST, |this| {
            this.bump();

            this.name();

            let post_span = this.current_span();
            match this.current() {
                Some(T![=]) => {
                    this.bump();
                    this.expr(Location::NONE);
                    this.semicolon();
                }
                Some(T![;]) => this.semicolon(),
                _ => this.push_error(
                    Some(post_span),
                    Some("expected a value with '=', or ';'"),
                    None,
                    ParseErrorKind::Context("constant value".to_string()),
                ),
            }
        });
    }

    fn struct_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![struct]));
        self.start_node_at(attr_checkpoint, STRUCT, |this| {
            this.bump();

            this.name();
            this.maybe_generic_arg_list();

            this.expect_control(T!['{']);

            this.comma_sep(
                |t| t == T!['}'],
                |this| match this.current() {
                    Some(T![ident]) => {
                        this.start_node(STRUCT_FIELD, |this| {
                            this.name();
                            this.expect_control(T![:]);
                            this.ty();
                        });
                        ControlFlow::Continue(())
                    }

                    Some(T![ghost]) => {
                        this.start_node(STRUCT_FIELD, |this| {
                            this.attrs();
                            this.name();
                            this.expect_control(T![:]);
                            this.ty();
                        });
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

            this.expect_control(T!['}']);
        });
    }

    fn type_invariant(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![invariant]));
        self.start_node_at(attr_checkpoint, TYPE_INVARIANT, |this| {
            this.bump();

            this.name_ref();
            this.maybe_generic_arg_list();

            this.block();
        });
    }

    fn macro_def(&mut self, attr_checkpoint: Checkpoint) {
        assert_eq!(self.current(), Some(T![macro]));
        self.start_node_at(attr_checkpoint, MACRO, |this| {
            this.bump();

            this.name();

            this.param_list();

            this.block();
        });
    }

    fn name(&mut self) {
        self.start_node(NAME, |this| match this.current() {
            Some(T![ident] | T![self]) => this.bump(),
            None => this.unexpected_eof(),
            _ => this.push_error(
                None,
                Some("expected a name"),
                None,
                ParseErrorKind::Context("name".to_string()),
            ),
        });
    }
    fn name_ref(&mut self) {
        self.start_node(NAME_REF, |this| match this.current() {
            Some(T![ident] | T![self]) => this.bump(),
            None => this.unexpected_eof(),
            _ => this.push_error(
                None,
                Some("expected a name"),
                None,
                ParseErrorKind::Context("name".to_string()),
            ),
        });
    }

    fn param_list(&mut self) {
        self.start_node(PARAM_LIST, |this| {
            if let Some(L_PAREN) = this.current() {
                this.bump();
            } else {
                this.push_error(
                    None,
                    Some("consider adding parameters here"),
                    None,
                    ParseErrorKind::Context("function parameters".to_string()),
                );
            }

            this.comma_sep(
                |t| t == T![')'],
                |this| {
                    let attrs_checkpoint = this.attrs();
                    if let Some(T![ident]) = this.current() {
                        this.start_node_at(attrs_checkpoint, PARAM, |this| {
                            this.name();
                            if let Some(T![:]) = this.current() {
                                this.bump();
                                this.ty();
                            }
                        });
                    }

                    ControlFlow::Continue(())
                },
            );

            this.expect_control(T![')']);
        });
    }

    fn ty(&mut self) {
        if let Some(T![&]) = self.current() {
            self.start_node(REF_TYPE, |this| {
                this.bump();

                if let Some(T![mut]) = this.current() {
                    this.bump();
                }
                this.ty();
            });
            return;
        } else if let Some(T![mut]) = self.current() {
            self.start_node(REF_TYPE, |this| {
                this.push_error(
                    None,
                    Some("'mut' is only allowed on references. add '&' here"),
                    None,
                    ParseErrorKind::Context("type".to_string()),
                );
                this.bump();
                this.ty();
            });
            return;
        }

        if let Some(T![ghost]) = self.current() {
            self.start_node(GHOST_TYPE, |this| {
                this.bump();
                this.ty();
            });
            return;
        }

        if let Some(T!['[']) = self.current() {
            self.start_node(LIST_TYPE, |this| {
                this.bump();
                this.ty();
                this.expect_control(T![']']);
            });
            return;
        }

        if let Some(T![?]) = self.current() {
            self.start_node(OPTIONAL, |this| {
                this.bump();
                this.ty();
            });
            return;
        }

        match self.current() {
            Some(IDENT) => {
                self.start_node(NAMED_TYPE, |this| {
                    this.name();
                    this.maybe_generic_arg_list();
                });
            }
            Some(T![int] | T![bool]) => self.start_node(PRIMITIVE, |this| this.bump()),
            _ => self.push_error(
                None,
                Some("specify the type here"),
                None,
                ParseErrorKind::Context("a type".to_string()),
            ),
        }
    }

    fn maybe_generic_arg_list(&mut self) {
        if let Some(T![<]) = self.current() {
            self.start_node(GENERIC_ARG_LIST, |this| {
                this.bump();
                this.comma_sep(
                    |t| t == T![>],
                    |this| match this.current() {
                        Some(T![>]) => ControlFlow::Break(()),
                        _ => {
                            this.start_node(GENERIC_ARG, |this| this.ty());
                            ControlFlow::Continue(())
                        }
                    },
                );
                this.expect_control(T![>]);
            });
        }
    }

    fn block(&mut self) {
        self.start_node(BLOCK_EXPR, |this| {
            this.expect_control(T!['{']);

            let mut trailing = None;
            let mut last_span = None;

            loop {
                if last_span == Some(this.current_span()) {
                    error!("parser did not progress. breaking block body");
                    break;
                }
                last_span = Some(this.current_span());

                match this.current() {
                    Some(T!['}']) => {
                        this.bump();
                        break;
                    }
                    Some(T![;]) => {
                        if let Some(checkpoint) = trailing.take() {
                            this.start_node_at(checkpoint, EXPR_STMT, |this| this.bump());
                        }
                    }
                    None => {
                        this.unexpected_eof();
                        break;
                    }
                    _ => {
                        if let Some(checkpoint) = trailing.take() {
                            this.push_error(
                                Some(this.pre_whitespace_span.set_len(0)),
                                Some("expected ';'"),
                                Some("consider adding a ';' to mark the end of the expression"),
                                ParseErrorKind::Context(";".to_string()),
                            );
                            this.wrap_checkpoint_in(checkpoint, EXPR_STMT);
                        }
                        match this.stmt() {
                            StatementParsed::Expression(e) => trailing = Some(e),
                            StatementParsed::Statement => {}
                        }
                    }
                }
            }
        });
    }

    fn stmt(&mut self) -> StatementParsed {
        match self.current() {
            Some(T![let]) => self.let_stmt(),
            Some(T![assume]) => self.assume_stmt(),
            Some(T![assert]) => self.assert_stmt(),
            Some(T![while]) => self.while_stmt(),
            Some(T![if]) => {
                let checkpoint = self.checkpoint();
                // self.start_node(EXPR_STMT, |this| {});
                self.if_expr();
                // self.builder.finish_node();
                return StatementParsed::Expression(checkpoint);
            }
            Some(t) if is_start_of_expr(t) => {
                let expr_checkpoint = self.checkpoint();
                self.expr(Location::NONE);

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

        self.start_node(LET_STMT, |this| {
            this.bump();

            this.name();

            if let Some(T![:]) = this.current() {
                this.bump();
                this.ty();
            }

            if let Some(T![=]) = this.current() {
                this.bump();
                this.expr(Location::NONE);
            }

            this.semicolon();
        });
    }

    fn assume_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![assume]));

        self.start_node(ASSUME_STMT, |this| {
            this.bump();

            this.comma_expr(Location::NONE);
            this.semicolon();
        });
    }

    fn assert_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![assert]));

        self.start_node(ASSERT_STMT, |this| {
            this.bump();

            this.comma_expr(Location::NONE);
            this.semicolon();
        });
    }

    fn while_stmt(&mut self) {
        assert_eq!(self.current(), Some(T![while]));

        self.start_node(WHILE_STMT, |this| {
            this.bump();

            this.expr(Location::NO_STRUCT);

            let mut seen_decreases = false;

            loop {
                match this.current() {
                    Some(T![invariant] | T![inv]) => {
                        this.start_node(INVARIANT, |this| {
                            this.bump();
                            this.comma_expr(Location::NO_STRUCT);
                        });
                    }
                    Some(T![decreases] | T![dec]) => {
                        if seen_decreases {
                            // TODO: Report repeated decreases
                        }
                        seen_decreases = true;

                        this.start_node(DECREASES, |this| {
                            this.bump();
                            match this.current() {
                                Some(T![_]) => this.bump(),
                                _ => this.expr(Location::NO_STRUCT),
                            }
                        });
                    }
                    _ => break,
                }
            }

            this.block();
        });
    }

    fn comma_expr(&mut self, loc: Location) {
        loop {
            match self.current() {
                Some(t) if is_start_of_expr(t) => {
                    let mut finished = false;
                    self.start_node(COMMA_EXPR, |this| {
                        this.expr(loc);

                        match this.current() {
                            Some(T![,]) => this.bump(),
                            _ => finished = true,
                        }
                    });
                    if finished {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    fn expr(&mut self, loc: Location) {
        self.expr_bp(loc, 0)
    }
    fn expr_bp(&mut self, loc: Location, min_bp: u8) {
        let lhs = self.checkpoint();
        match self.current() {
            Some(T![false] | T![true]) => self.start_node(LITERAL, |this| this.bump()),
            Some(T!['{']) => self.block(),
            Some(T![return]) => {
                self.start_node(RETURN_EXPR, |this| {
                    this.bump();

                    match this.current() {
                        Some(t) if is_start_of_expr(t) => this.expr(Location::NONE),
                        _ => {}
                    }
                });
            }
            Some(T![result]) => self.start_node(RESULT_EXPR, |this| this.bump()),
            Some(T![ident] | T![self]) => {
                let checkpoint = self.checkpoint();
                self.name();

                match self.current() {
                    Some(T!['{']) if !loc.contains(Location::NO_STRUCT) => {
                        self.start_node_at(checkpoint, STRUCT_EXPR, |this| {
                            this.expect_control(T!['{']);

                            this.comma_sep(
                                |t| t == T!['}'],
                                |this| match this.current() {
                                    Some(T![ident]) => {
                                        this.start_node(STRUCT_EXPR_FIELD, |this| {
                                            this.name();
                                            this.expect_control(T![:]);
                                            this.expr_bp(Location::NONE, 0);
                                        });
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

                            this.expect_control(T!['}']);
                        });
                    }
                    _ => self.wrap_checkpoint_in(checkpoint, IDENT_EXPR),
                }
            }
            Some(T![null]) => self.start_node(NULL_EXPR, |this| this.bump()),
            Some(INT_NUMBER) => self.start_node(LITERAL, |this| this.bump()),
            Some(T!['[']) => {
                self.start_node(LIST_EXPR, |this| {
                    this.bump();
                    this.comma_sep(
                        |t| t == T![']'],
                        |this| {
                            this.start_node(COMMA_EXPR, |this| this.expr_bp(Location::NONE, 0));
                            ControlFlow::Continue(())
                        },
                    );
                    this.expect_control(T![']']);
                });
            }
            Some(T!['(']) => {
                self.start_node(PAREN_EXPR, |this| {
                    this.bump();
                    this.expr_bp(Location::NONE, 0);
                    this.expect_control(T![')']);
                });
            }
            Some(T![if]) => self.if_expr(),
            Some(t) => {
                if let Some((op, (), r_bp)) = prefix_binding_power(Some(t)) {
                    match op {
                        T![&] => {
                            self.start_node(REF_EXPR, |this| {
                                this.bump();

                                if let Some(T![mut]) = this.current() {
                                    this.bump();
                                }

                                this.expr_bp(loc, r_bp);
                            });
                        }
                        T![forall] | T![exists] => {
                            self.start_node(QUANTIFIER_EXPR, |this| {
                                this.start_node(QUANTIFIER, |this| this.bump());
                                this.param_list();
                                this.expr_bp(loc, r_bp);
                            });
                        }
                        _ => {
                            self.start_node(PREFIX_EXPR, |this| {
                                this.bump();

                                this.expr_bp(loc, r_bp);
                            });
                        }
                    }
                } else {
                    // eprintln!("unknown start of expr {t:?}");
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
            if let Some((op, l_bp, ())) = postfix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }

                match op {
                    T!['('] => self.start_node_at(lhs, CALL_EXPR, |this| this.arg_list()),
                    T!['['] => {
                        self.start_node_at(lhs, INDEX_EXPR, |this| {
                            this.bump();
                            this.expr(Location::NONE);
                            this.expect_control(T![']']);
                        });
                    }
                    T![.] => {
                        self.start_node_at(lhs, FIELD_EXPR, |this| {
                            this.bump();
                            this.name();
                        });
                    }
                    _ => todo!(),
                }

                continue;
            }
            if let Some((op, l_bp, r_bp)) = infix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }

                match op {
                    T![..] => {
                        self.start_node_at(lhs, RANGE_EXPR, |this| {
                            this.bump();
                            if this.current().map(is_start_of_expr) == Some(true) {
                                this.expr_bp(loc, r_bp);
                            }
                        });
                    }
                    _op => {
                        self.start_node_at(lhs, BIN_EXPR, |this| {
                            this.bump();
                            // eprintln!("normal infix op was: '{op}'");
                            this.expr_bp(loc, r_bp);
                        });
                    }
                }
                continue;
            };

            break;
        }
    }

    fn if_expr(&mut self) {
        assert_eq!(self.current(), Some(T![if]));
        self.start_node(IF_EXPR, |this| {
            this.bump();

            this.expr(Location::NO_STRUCT);
            this.block();

            if let Some(T![else]) = this.current() {
                this.bump();
                if let Some(T![if]) = this.current() {
                    this.if_expr();
                } else {
                    this.block();
                }
            }
        });
    }

    fn arg_list(&mut self) {
        self.start_node(ARG_LIST, |this| {
            this.expect_control(T!['(']);

            this.comma_sep(
                |t| t == T![')'],
                |this| {
                    this.start_node(ARG, |this| this.expr_bp(Location::NONE, 0));
                    ControlFlow::Continue(())
                },
            );

            this.expect_control(T![')']);
        });
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
                        LastThing::Item => self.bump(),
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
                Some(t) if terminator(t) => break,
                None => {
                    self.unexpected_eof();
                    break;
                }
                _ => {
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
    fn checkpoint(&mut self) -> Checkpoint {
        self.real_skip_ws();
        self.builder.checkpoint()
    }
    fn start_node(&mut self, kind: SyntaxKind, f: impl FnOnce(&mut Self)) {
        self.real_skip_ws();
        self.builder.start_node(kind.into());
        f(self);
        self.builder.finish_node();
    }
    fn start_node_at(
        &mut self,
        checkpoint: Checkpoint,
        kind: SyntaxKind,
        f: impl FnOnce(&mut Self),
    ) {
        self.real_skip_ws();
        self.builder.start_node_at(checkpoint, kind.into());
        f(self);
        self.builder.finish_node();
    }
    fn wrap_checkpoint_in(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(checkpoint, kind.into());
        self.builder.finish_node();
    }
    fn bump(&mut self) {
        self.real_skip_ws();
        let (kind, text, _) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text);
        self.has_bumped_after_ws_skip = true;
    }
    fn current_full_token(&self) -> Option<(SyntaxKind, &'src str, SourceSpan)> {
        self.tokens
            .iter()
            .rev()
            .copied()
            .find(|&(kind, _, _)| !is_whitespace(kind))
    }
    fn current(&self) -> Option<SyntaxKind> {
        self.current_full_token().map(|(kind, _, _)| kind)
    }
    fn current_span(&self) -> SourceSpan {
        self.current_full_token()
            .map(|(_, _, span)| span)
            .unwrap_or(self.pre_whitespace_span)
    }
    fn real_skip_ws(&mut self) {
        if self.has_bumped_after_ws_skip {
            self.pre_whitespace_span = self.current_span();
        }
        self.has_bumped_after_ws_skip = false;
        while self.tokens.last().map(|(kind, _, _)| is_whitespace(*kind)) == Some(true) {
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

fn is_whitespace(token: SyntaxKind) -> bool {
    matches!(token, WHITESPACE | COMMENT)
}

fn is_start_of_expr(token: SyntaxKind) -> bool {
    matches!(
        token,
        T![ident]
            | T![self]
            | T![true]
            | T![false]
            | T![result]
            | T![if]
            | T![return]
            | T![forall]
            | T![exists]
            | T![&]
            | T![!]
            | T![-]
            | T!['{']
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
