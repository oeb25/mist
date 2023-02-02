use itertools::Itertools;
use miette::Diagnostic;
use rowan::GreenNodeBuilder;
use thiserror::Error;

use crate::{
    generated::SourceFile,
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

    fn maybe_item(&mut self) -> bool {
        self.skip_ws();
        match self.current() {
            Some(T![fn]) => self.fn_def(),
            Some(T![const]) => self.const_def(),
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

    fn fn_def(&mut self) {
        assert_eq!(self.current(), Some(T![fn]));
        self.builder.start_node(FN.into());
        self.bump();

        self.name();
        self.param_list();

        let span = self.current_span();
        self.skip_ws();

        match self.current() {
            Some(SEMICOLON) => self.bump(),
            Some(L_CURLY) => self.block(),
            _ => self.push_error(
                Some(span.set_len(1)),
                Some("expected a block"),
                None,
                ParseErrorKind::Context("{".to_string()),
            ),
        }

        self.builder.finish_node();
    }

    fn const_def(&mut self) {
        assert_eq!(self.current(), Some(T![const]));
        self.builder.start_node(CONST.into());
        self.bump();

        self.name();

        let post_span = self.current_span();
        self.skip_ws();
        match self.current() {
            Some(T![=]) => {
                self.bump();
                self.expr();
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

        loop {
            self.skip_ws();
            match self.current() {
                Some(R_PAREN) => {
                    self.bump();
                    break;
                }
                Some(IDENT) => {
                    self.builder.start_node(PARAM.into());
                    self.name();
                    self.skip_ws();
                    self.expect_control(COLON);
                    self.ty();
                    self.builder.finish_node()
                }
                None => {
                    self.unexpected_eof();
                    break;
                }
                _ => {
                    self.push_error(
                        None,
                        Some("consider adding a parameter here"),
                        None,
                        ParseErrorKind::Context("function parameters".to_string()),
                    );
                    self.bump();
                }
            }
        }

        self.builder.finish_node();
    }

    fn ty(&mut self) {
        self.skip_ws();
        match self.current() {
            Some(IDENT) => {
                self.builder.start_node(NAME_REF.into());
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
    }

    fn block(&mut self) {
        assert_eq!(self.current(), Some(L_CURLY));

        self.builder.start_node(BLOCK.into());

        self.bump();

        loop {
            self.skip_ws();
            match self.current() {
                Some(R_CURLY) => {
                    self.bump();
                    break;
                }
                None => break,
                _ => self.stmt(),
            }
        }

        self.builder.finish_node();
    }

    fn stmt(&mut self) {
        self.skip_ws();

        match self.current() {
            Some(LET_KW) => self.let_stmt(),
            Some(ASSUME_KW) => self.assume_stmt(),
            Some(ASSERT_KW) => self.assert_stmt(),
            Some(IDENT) => {
                self.expr();
                self.semicolon();
            }
            // Some(CONST_KW) => {
            //     self.push_error(
            //         None,
            //         Some("const declarations are only allowed at top-level"),
            //         None,
            //         ParseErrorKind::Context("const found in body".to_string()),
            //     );
            //     self.const_def();
            // }
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
    }

    fn let_stmt(&mut self) {
        eprintln!("parsing let stmt");

        assert_eq!(self.current(), Some(LET_KW));

        self.builder.start_node(LET_STMT.into());
        self.bump();

        self.name();

        self.skip_ws();
        if let Some(T![=]) = self.current() {
            self.bump();
            self.expr();
        }

        self.semicolon();

        self.builder.finish_node();
    }

    fn assume_stmt(&mut self) {
        eprintln!("parsing assume");

        assert_eq!(self.current(), Some(ASSUME_KW));

        self.builder.start_node(ASSUME_STMT.into());
        self.bump();

        self.expr();
        self.semicolon();

        self.builder.finish_node();
    }

    fn assert_stmt(&mut self) {
        eprintln!("parsing assert");

        assert_eq!(self.current(), Some(ASSERT_KW));

        self.builder.start_node(ASSERT_STMT.into());
        self.bump();

        self.expr();
        self.semicolon();

        self.builder.finish_node();
    }

    fn expr(&mut self) {
        self.expr_bp(0)
    }
    fn expr_bp(&mut self, min_bp: u8) {
        self.skip_ws();

        eprintln!(
            "Start parsing expr with first token being: {:?}",
            self.current()
        );

        let mut lhs = self.builder.checkpoint();
        match self.current() {
            Some(T![false] | T![true]) => {
                self.builder.start_node(LITERAL.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(T![ident]) => {
                self.builder.start_node(IDENT_EXPR.into());
                self.name();
                self.builder.finish_node();
            }
            Some(INT_NUMBER) => {
                self.builder.start_node(LITERAL.into());
                self.bump();
                self.builder.finish_node();
            }
            Some(T!['(']) => {
                self.builder.start_node(PAREN_EXPR.into());
                self.bump();
                self.expr_bp(0);
                self.expect_control(T![')']);
                self.builder.finish_node();
            }
            Some(t) => {
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
            None => self.unexpected_eof(),
        };

        loop {
            self.skip_ws();
            if let Some((_op, l_bp, ())) = postfix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }

                let next = self.builder.checkpoint();
                if self.current() == Some(T!['(']) {
                    self.builder.start_node_at(lhs, CALL_EXPR.into());
                    self.arg_list();
                    self.builder.finish_node();
                } else {
                    todo!()
                }
                lhs = next;

                continue;
            }
            if let Some((op, l_bp, r_bp)) = infix_binding_power(self.current()) {
                if l_bp < min_bp {
                    break;
                }
                let next = self.builder.checkpoint();
                self.builder.start_node_at(lhs, BIN_EXPR.into());
                self.bump();

                match op {
                    op => {
                        eprintln!("normal infix op was: '{op}'");
                        self.expr_bp(r_bp);
                    }
                }
                self.builder.finish_node();
                continue;
            };

            break;
        }
    }

    fn arg_list(&mut self) {
        self.builder.start_node(ARG_LIST.into());

        if let Some(L_PAREN) = self.current() {
            self.bump();
        } else {
            todo!()
        }

        loop {
            self.skip_ws();
            match self.current() {
                Some(R_PAREN) => {
                    self.bump();
                    break;
                }
                Some(SEMICOLON) => {
                    self.push_error(
                        None,
                        Some("expected an expression here"),
                        Some("consider closing the function call with a ')'"),
                        ParseErrorKind::Context("start of expression".to_string()),
                    );
                    break;
                }
                _ => {
                    self.builder.start_node(ARG.into());
                    self.expr_bp(0);
                    match self.current() {
                        Some(COMMA) => {
                            self.bump();
                            self.builder.finish_node();
                        }
                        _ => self.builder.finish_node(),
                    }
                }
            }
        }

        self.builder.finish_node();
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
        eprintln!("{:?}", miette::Error::new(err.clone()));
        self.errors.push(err)
    }
    fn bump(&mut self) {
        let (kind, text, _) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text);
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
        self.pre_whitespace_span = self.current_span();
        while matches!(self.current(), Some(WHITESPACE | COMMENT)) {
            self.bump()
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

fn prefix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, (), u8)> {
    let op = op?;
    match op {
        T![+] | T![-] => Some((op, (), 9)),
        _ => None,
    }
}

fn postfix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, u8, ())> {
    let op = op?;
    let (l, r) = match op {
        T![!] => (11, ()),
        T!['['] => (11, ()),
        T!['('] => (11, ()),
        _ => return None,
    };

    Some((op, l, r))
}

fn infix_binding_power(op: Option<SyntaxKind>) -> Option<(SyntaxKind, u8, u8)> {
    let op = op?;
    let (l, r) = match op {
        T![=] => (2, 1),
        T![?] => (4, 3),
        T![+] | T![-] => (5, 6),
        T![*] | T![/] => (7, 8),
        T![.] => (14, 13),
        _ => return None,
    };

    Some((op, l, r))
}
