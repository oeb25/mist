use std::{collections::HashMap, fmt};

use mist_syntax::{ast, AstNode, SourceSpan, SyntaxToken};

use crate::{
    def::{Def, DefKind},
    file::SourceFile,
    mono::{
        lower::MonoDefLower,
        types::{Adt, Type},
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixture {
    file: SourceFile,
    markers: HashMap<usize, Marker>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Marker {
    byte_offset: usize,
    end_offset: Option<usize>,
}

impl Fixture {
    pub fn new(db: &dyn crate::Db, src: impl fmt::Display) -> Fixture {
        let mut src = src.to_string();
        let mut markers = HashMap::<usize, Marker>::new();

        while let Some((pre, post)) = src.split_once('$') {
            let n = post[0..1].parse().unwrap();
            if let Some(m) = markers.get_mut(&n) {
                m.end_offset = Some(pre.len());
            } else {
                markers.insert(n, Marker { byte_offset: pre.len(), end_offset: None });
            }
            src = format!("{pre}{}", &post[1..])
        }

        let file = SourceFile::new(db, src);

        Fixture { file, markers }
    }

    pub fn file(&self) -> SourceFile {
        self.file
    }

    pub fn marker(&self, idx: usize) -> Marker {
        self.markers[&idx]
    }
    pub fn span(&self, idx: usize) -> SourceSpan {
        let m = self.marker(idx);
        SourceSpan::new_start_end(m.byte_offset, m.end_offset.unwrap())
    }

    pub fn token_at(&self, db: &dyn crate::Db, m: Marker) -> SyntaxToken {
        self.file
            .root(db)
            .syntax()
            .token_at_offset(m.byte_offset.try_into().unwrap())
            .left_biased()
            .unwrap()
    }

    pub fn def_at(&self, db: &dyn crate::Db, m: Marker) -> Def {
        let token = self.token_at(db, m);
        let item = token.parent_ancestors().find_map(ast::Item::cast).unwrap();
        let ast_map = self.file.ast_map(db);
        let ast_id = ast_map.ast_id(self.file, &item);
        Def::new(db, DefKind::new(db, ast_id).unwrap())
    }

    pub fn type_at(&self, db: &dyn crate::Db, m: Marker) -> Type {
        let def = self.def_at(db, m);
        let hir = def.hir(db).unwrap();
        let cx = hir.cx(db);
        let mut mdl = MonoDefLower::new(db, cx);

        let token = self.token_at(db, m);

        if let Some(ty_ast) = token.parent_ancestors().find_map(ast::Type::cast) {
            let ty_src = hir.source_map(db).ty_ast((&ty_ast).into()).unwrap();
            mdl.lower_ty(ty_src.ty(db))
        } else if let Some(expr_ast) = token.parent_ancestors().find_map(ast::Expr::cast) {
            let expr = hir.source_map(db).expr_ast((&expr_ast).into()).unwrap();
            let ty_id = cx.expr_ty(expr);
            mdl.lower_ty(ty_id)
        } else {
            todo!()
        }
    }
    pub fn adt_at(&self, db: &dyn crate::Db, m: Marker) -> Adt {
        self.type_at(db, m).ty_adt(db).unwrap()
    }
}

impl Marker {
    pub fn byte_offset(self) -> usize {
        self.byte_offset
    }
}

#[macro_export]
macro_rules! expect_ {
    ($($t:tt)*) => {
        |res| ::insta::assert_display_snapshot!(res, $($t)*)
    };
}

pub use expect_ as expect;
