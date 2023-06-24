use std::fmt;

use mist_syntax::{ast, AstNode, SyntaxToken};

use crate::{
    def::{Def, DefKind},
    file::SourceFile,
    mono::{
        lower::MonoDefLower,
        types::{Adt, Type},
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fixture {
    file: SourceFile,
    markers: Vec<Marker>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Marker {
    byte_offset: usize,
}

impl Fixture {
    pub fn new(db: &dyn crate::Db, src: impl fmt::Display) -> Fixture {
        let mut src = src.to_string();
        let mut markers = Vec::new();

        while let Some((pre, post)) = src.rsplit_once("$0") {
            markers.push(Marker { byte_offset: pre.len() });
            src = format!("{pre}{post}")
        }

        let file = SourceFile::new(db, src);

        Fixture { file, markers }
    }

    pub fn marker(&self, idx: usize) -> Marker {
        self.markers[idx]
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

fn fixture(src: impl fmt::Display) -> (crate::db::Database, Fixture) {
    let db = crate::db::Database::default();
    let fixture = Fixture::new(&db, src);
    (db, fixture)
}

fn check_type_at(src: impl fmt::Display) -> String {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    fixture.type_at(&db, m).display(&db).to_string()
}

fn check_pure_type(src: impl fmt::Display) -> Option<bool> {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    fixture.type_at(&db, m).is_pure(&db)
}

fn check_pure_adt(src: impl fmt::Display) -> bool {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    fixture.adt_at(&db, m).is_pure(&db)
}

#[test]
fn test_type_at() {
    insta::assert_display_snapshot!(check_type_at(
        r#"
pure struct Pos { x: int }
invariant Pos$0 { true }
"#,
    ), @r#"Pos"#);
    insta::assert_display_snapshot!(check_type_at(
        r#"
pure struct Pos { x: int }
invariant Pos { self$0.x == 4 }
"#,
    ), @r#"ghost Pos"#);
}

#[test]
fn test_pure() {
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos { x: int }
invariant Pos$0 { true }
"#,
        ),
        Some(true)
    );
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos { x: int }
invariant Pos { self$0.x == 4 }
"#,
        ),
        Some(true)
    );
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos[T] { x: T }
fn f() {
    let a = Pos$0 { x: 1 };
}
"#,
        ),
        Some(true)
    );
    assert!(check_pure_adt(
        r#"
pure struct Pos[T] { x: T }
fn f() {
    let a = Pos$0 { x: 1 };
}
"#,
    ));
    assert!(check_pure_adt(
        r#"
pure struct Tuple[T, S] {
    fst: T,
    snd: S,
}
fn client() {
    let a = Tuple$0 { fst: 4, snd: 4 };
    let c = Tuple { fst: a, snd: a };
    assert sum(c) == 16;
}
"#,
    ));
}
