use std::fmt;

use crate::AstNode;

use super::{Name, NameRef, SyntaxKind::*};

#[derive(Debug, Clone, PartialEq)]
pub enum NameOrNameRef {
    Name(Name),
    NameRef(NameRef),
}
impl fmt::Display for NameOrNameRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameOrNameRef::Name(it) => fmt::Display::fmt(it, f),
            NameOrNameRef::NameRef(it) => fmt::Display::fmt(it, f),
        }
    }
}
impl From<Name> for NameOrNameRef {
    fn from(name: Name) -> NameOrNameRef {
        NameOrNameRef::Name(name)
    }
}
impl From<NameRef> for NameOrNameRef {
    fn from(name: NameRef) -> NameOrNameRef {
        NameOrNameRef::NameRef(name)
    }
}

impl AstNode for NameOrNameRef {
    fn can_cast(kind: super::SyntaxKind) -> bool
    where
        Self: Sized,
    {
        Name::can_cast(kind) || NameRef::can_cast(kind)
    }

    fn cast(syntax: crate::SyntaxNode) -> Option<Self>
    where
        Self: Sized,
    {
        match syntax.kind() {
            NAME => Name::cast(syntax).map(NameOrNameRef::Name),
            NAME_REF => NameRef::cast(syntax).map(NameOrNameRef::NameRef),
            _ => None,
        }
    }

    fn syntax(&self) -> &crate::SyntaxNode {
        match self {
            NameOrNameRef::Name(it) => it.syntax(),
            NameOrNameRef::NameRef(it) => it.syntax(),
        }
    }
}
