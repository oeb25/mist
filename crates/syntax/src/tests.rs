use crate::{
    ast::{HasName, Item, Stmt},
    parser::Parser,
};

mod ast_src;
mod sourcegen_ast;

#[test]
fn parse_hello() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let src = include_str!("../../examples/list.mist");

    let (file, _errors) = Parser::new(src).parse();

    dbg!(&file);

    for item in file.items() {
        match item {
            Item::Const(_) => todo!(),
            Item::Fn(my_fn) => {
                for stmt in my_fn.body().unwrap().statements() {
                    match stmt {
                        Stmt::LetStmt(l) => {
                            dbg!(l.name());
                            dbg!(l.initializer());
                        }
                        Stmt::AssertStmt(a) => {
                            dbg!(a.assert_token());
                            dbg!(a.comma_exprs());
                        }
                        Stmt::AssumeStmt(a) => {
                            dbg!(a.assume_token());
                            dbg!(a.comma_exprs());
                        }
                        Stmt::ExprStmt(e) => {
                            dbg!(e.expr());
                        }
                        Stmt::Item(i) => {
                            dbg!(i);
                        }
                        Stmt::WhileStmt(i) => {
                            dbg!(i);
                        }
                    }
                }
            }
            Item::Struct(s) => {
                dbg!(s);
            }
            Item::TypeInvariant(_) => todo!(),
            Item::Macro(_) => todo!(),
        }
    }

    Ok(())
}
