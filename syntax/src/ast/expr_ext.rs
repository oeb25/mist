use std::cmp::Ordering;

use crate::{
    ast,
    support::{self, AstNode, AstToken},
    SourceSpan, SyntaxToken, T,
};

use super::operators::{ArithOp, BinaryOp, CmpOp, LogicOp, UnaryOp};

impl ast::PrefixExpr {
    pub fn op_details(&self) -> Option<(SyntaxToken, UnaryOp)> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find_map(|c| {
                let bin_op = match c.kind() {
                    T![!] => UnaryOp::Not,
                    T![-] => UnaryOp::Neg,
                    _ => return None,
                };
                Some((c, bin_op))
            })
    }
}

impl ast::BinExpr {
    pub fn lhs(&self) -> Option<ast::Expr> {
        support::children(self.syntax()).next()
    }

    pub fn rhs(&self) -> Option<ast::Expr> {
        support::children(self.syntax()).nth(1)
    }

    pub fn op_details(&self) -> Option<(SyntaxToken, BinaryOp)> {
        self.syntax().children_with_tokens().filter_map(|it| it.into_token()).find_map(|c| {
            #[rustfmt::skip]
            let bin_op = match c.kind() {
                T![||] => BinaryOp::LogicOp(LogicOp::Or),
                T![&&] => BinaryOp::LogicOp(LogicOp::And),

                T![==] => BinaryOp::CmpOp(CmpOp::Eq { negated: false }),
                T![!=] => BinaryOp::CmpOp(CmpOp::Eq { negated: true }),
                T![<=] => BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Less,    strict: false }),
                T![>=] => BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Greater, strict: false }),
                T![<]  => BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Less,    strict: true }),
                T![>]  => BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Greater, strict: true }),

                T![+]  => BinaryOp::ArithOp(ArithOp::Add),
                T![*]  => BinaryOp::ArithOp(ArithOp::Mul),
                T![-]  => BinaryOp::ArithOp(ArithOp::Sub),
                T![/]  => BinaryOp::ArithOp(ArithOp::Div),
                T![%]  => BinaryOp::ArithOp(ArithOp::Rem),
                T![<<] => BinaryOp::ArithOp(ArithOp::Shl),
                T![>>] => BinaryOp::ArithOp(ArithOp::Shr),
                T![^]  => BinaryOp::ArithOp(ArithOp::BitXor),
                T![|]  => BinaryOp::ArithOp(ArithOp::BitOr),
                T![&]  => BinaryOp::ArithOp(ArithOp::BitAnd),

                T![=]   => BinaryOp::Assignment,
                // T![=]   => BinaryOp::Assignment { op: None },
                // T![+=]  => BinaryOp::Assignment { op: Some(ArithOp::Add) },
                // T![*=]  => BinaryOp::Assignment { op: Some(ArithOp::Mul) },
                // T![-=]  => BinaryOp::Assignment { op: Some(ArithOp::Sub) },
                // T![/=]  => BinaryOp::Assignment { op: Some(ArithOp::Div) },
                // T![%=]  => BinaryOp::Assignment { op: Some(ArithOp::Rem) },
                // T![<<=] => BinaryOp::Assignment { op: Some(ArithOp::Shl) },
                // T![>>=] => BinaryOp::Assignment { op: Some(ArithOp::Shr) },
                // T![^=]  => BinaryOp::Assignment { op: Some(ArithOp::BitXor) },
                // T![|=]  => BinaryOp::Assignment { op: Some(ArithOp::BitOr) },
                // T![&=]  => BinaryOp::Assignment { op: Some(ArithOp::BitAnd) },

                _ => return None,
            };
            Some((c, bin_op))
        })
    }
}

impl ast::RangeExpr {
    pub fn lhs(&self) -> Option<ast::Expr> {
        let idx = self
            .syntax()
            .children_with_tokens()
            .position(|it| matches!(it.kind(), T![..]))?;
        self.syntax().children().take(idx).find_map(ast::Expr::cast)
    }

    pub fn rhs(&self) -> Option<ast::Expr> {
        let idx = self
            .syntax()
            .children_with_tokens()
            .position(|it| matches!(it.kind(), T![..]))?;
        self.syntax().children().skip(idx).find_map(ast::Expr::cast)
    }
}

impl ast::IndexExpr {
    pub fn base(&self) -> Option<ast::Expr> {
        support::children(self.syntax()).next()
    }
    pub fn index(&self) -> Option<ast::Expr> {
        support::children(self.syntax()).nth(1)
    }
}

impl ast::IfExpr {
    pub fn condition(&self) -> Option<ast::Expr> {
        support::children(self.syntax()).next()
    }
    pub fn then_branch(&self) -> Option<ast::BlockExpr> {
        support::children(self.syntax()).next()
    }
    pub fn else_branch(&self) -> Option<ast::IfExprElse> {
        support::children(self.syntax()).nth(1)
    }
}

pub enum LiteralKind {
    IntNumber(ast::IntNumber),
    Bool(bool),
}

impl ast::Literal {
    pub fn token(&self) -> SyntaxToken {
        self.syntax()
            .children_with_tokens()
            .find(|e| !e.kind().is_trivia())
            .and_then(|e| e.into_token())
            .unwrap()
    }
    pub fn kind(&self) -> LiteralKind {
        let token = self.token();

        if let Some(t) = ast::IntNumber::cast(token.clone()) {
            return LiteralKind::IntNumber(t);
        }
        match token.kind() {
            T![true] => LiteralKind::Bool(true),
            T![false] => LiteralKind::Bool(false),
            _ => todo!(),
        }
    }
}
