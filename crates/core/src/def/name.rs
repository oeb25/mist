use std::fmt;

use mist_syntax::ast;
use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(SmolStr);

impl Name {
    pub fn new(text: &str) -> Name {
        Name(text.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<ast::Name> for Name {
    fn from(value: ast::Name) -> Self {
        Name::new(&value.to_string())
    }
}
impl From<&'_ ast::Name> for Name {
    fn from(value: &'_ ast::Name) -> Self {
        Name::new(&value.to_string())
    }
}

impl From<ast::NameRef> for Name {
    fn from(value: ast::NameRef) -> Self {
        Name::new(&value.to_string())
    }
}
impl From<&'_ ast::NameRef> for Name {
    fn from(value: &'_ ast::NameRef) -> Self {
        Name::new(&value.to_string())
    }
}

impl From<ast::NameOrNameRef> for Name {
    fn from(value: ast::NameOrNameRef) -> Self {
        Name::new(&value.to_string())
    }
}
impl From<&'_ ast::NameOrNameRef> for Name {
    fn from(value: &'_ ast::NameOrNameRef) -> Self {
        Name::new(&value.to_string())
    }
}
