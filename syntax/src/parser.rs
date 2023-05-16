mod grammar;

use std::{fmt, ops::ControlFlow};

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

use self::grammar::*;

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
    #[error("parse error: {0}")]
    Adhoc(String),
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
            if !item_opt(&mut self) {
                match self.current() {
                    EOF => {
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

    fn semicolon(&mut self) {
        self.eat(T![;])
    }

    fn eat(&mut self, token: SyntaxKind) {
        let span = self.pre_whitespace_span;
        match self.current() {
            t if t == token => self.bump(),
            _ => self.push_error(
                Some(span.set_len(1)),
                Some(&format!("help: add '{token}' here")),
                None,
                ParseErrorKind::Context(token.to_string()),
            ),
        }
    }

    fn error(&mut self, text: impl fmt::Display) {
        self.push_error(None, None, None, ParseErrorKind::Adhoc(text.to_string()))
    }
    fn error_help(&mut self, text: impl fmt::Display, help: impl fmt::Display) {
        let err = ParseError {
            input: self.src.to_string(),
            span: self.current_span(),
            label: Some(text.to_string()),
            help: Some(help.to_string()),
            kind: ParseErrorKind::Adhoc(text.to_string()),
        };
        #[cfg(debug_assertions)]
        eprintln!("{:?}", miette::Error::new(err.clone()));
        self.errors.push(err)
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
            .find(|&(kind, _, _)| !kind.is_trivia())
    }
    fn current(&self) -> SyntaxKind {
        self.current_full_token()
            .map(|(kind, _, _)| kind)
            .unwrap_or(SyntaxKind::EOF)
    }
    fn current_span(&self) -> SourceSpan {
        self.current_full_token()
            .map(|(_, _, span)| span)
            .unwrap_or(self.pre_whitespace_span)
    }
    fn at(&self, kind: SyntaxKind) -> bool {
        self.current() == kind
    }
    fn real_skip_ws(&mut self) {
        if self.has_bumped_after_ws_skip {
            self.pre_whitespace_span = self.current_span();
        }
        self.has_bumped_after_ws_skip = false;
        while self.tokens.last().map(|(kind, _, _)| kind.is_trivia()) == Some(true) {
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

#[derive(Debug, Clone, Copy)]
pub enum StatementParsed {
    Expression(Checkpoint),
    Statement,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Location: u32 {
        const NONE = 0b000;
        const NO_STRUCT = 0b001;
    }
}
