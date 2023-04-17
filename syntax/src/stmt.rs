use crate::{
    ast::{
        AssertStmt, AssumeStmt, ExprStmt, Item, LetStmt, SourceFile, Stmt,
        SyntaxKind::{self, *},
        WhileStmt,
    },
    support::AstNode,
    SyntaxNode,
};

// Stmt is the only nested enum, so it's easier to just hand-write it
impl AstNode for Stmt {
    fn can_cast(kind: SyntaxKind) -> bool {
        match kind {
            LET_STMT | EXPR_STMT | ASSERT_STMT | ASSUME_STMT | WHILE_STMT => true,
            _ => Item::can_cast(kind),
        }
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            LET_STMT => Stmt::LetStmt(LetStmt { syntax }),
            EXPR_STMT => Stmt::ExprStmt(ExprStmt { syntax }),
            ASSERT_STMT => Stmt::AssertStmt(AssertStmt { syntax }),
            ASSUME_STMT => Stmt::AssumeStmt(AssumeStmt { syntax }),
            WHILE_STMT => Stmt::WhileStmt(WhileStmt { syntax }),
            _ => {
                let item = Item::cast(syntax)?;
                Stmt::Item(item)
            }
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Stmt::LetStmt(it) => &it.syntax,
            Stmt::ExprStmt(it) => &it.syntax,
            Stmt::Item(it) => it.syntax(),
            Stmt::AssertStmt(it) => &it.syntax,
            Stmt::AssumeStmt(it) => &it.syntax,
            Stmt::WhileStmt(it) => &it.syntax,
        }
    }
}

impl SourceFile {
    pub fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
