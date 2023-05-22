use super::{Name, NameRef};

#[derive(Debug, Clone, PartialEq)]
pub enum NameOrNameRef {
    Name(Name),
    NameOrNameRef(NameRef),
}
