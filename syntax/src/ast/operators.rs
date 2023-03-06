use std::cmp::Ordering;

use derive_more::Display;

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryOp {
    LogicOp(LogicOp),
    CmpOp(CmpOp),
    ArithOp(ArithOp),
    Assignment,
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LogicOp {
    #[display(fmt = "||")]
    Or,
    #[display(fmt = "&&")]
    And,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CmpOp {
    Eq { negated: bool },
    Ord { ordering: Ordering, strict: bool },
}

impl std::fmt::Display for CmpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CmpOp::Eq { negated: true } => "!=",
            CmpOp::Eq { negated: false } => "==",
            CmpOp::Ord { ordering, strict } => match (ordering, strict) {
                (Ordering::Less, true) => "<",
                (Ordering::Less, false) => "<=",
                (Ordering::Equal, _) => "==",
                (Ordering::Greater, true) => ">",
                (Ordering::Greater, false) => ">=",
            },
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArithOp {
    #[display(fmt = "+")]
    Add,
    #[display(fmt = "*")]
    Mul,
    #[display(fmt = "-")]
    Sub,
    #[display(fmt = "/")]
    Div,
    #[display(fmt = "%")]
    Rem,
    #[display(fmt = "<<")]
    Shl,
    #[display(fmt = ">>")]
    Shr,
    #[display(fmt = "^")]
    BitXor,
    #[display(fmt = "|")]
    BitOr,
    #[display(fmt = "&")]
    BitAnd,
}
