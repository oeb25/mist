use crate::parser::Parser;

mod ast_src;
mod sourcegen_ast;

#[test]
fn parse_hello() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let src = include_str!("../examples/list.mist");

    let (file, _errors) = Parser::new(src).parse();

    dbg!(&file);

    for item in file.items() {
        match item {
            crate::generated::Item::Const(_) => todo!(),
            crate::generated::Item::Fn(my_fn) => {
                for stmt in my_fn.body().unwrap().statements() {
                    match stmt {
                        crate::generated::Stmt::LetStmt(l) => {
                            dbg!(l.name());
                            dbg!(l.initializer());
                        }
                        crate::generated::Stmt::AssertStmt(a) => {
                            dbg!(a.assert_token());
                            dbg!(a.comma_expr());
                        }
                        crate::generated::Stmt::AssumeStmt(a) => {
                            dbg!(a.assume_token());
                            dbg!(a.comma_expr());
                        }
                        crate::generated::Stmt::ExprStmt(e) => {
                            dbg!(e.expr());
                        }
                        crate::generated::Stmt::Item(i) => {
                            dbg!(i);
                        }
                        crate::generated::Stmt::ReturnStmt(i) => {
                            dbg!(i);
                        }
                        crate::generated::Stmt::WhileStmt(i) => {
                            dbg!(i);
                        }
                    }
                }
            }
            crate::generated::Item::Struct(s) => {
                dbg!(s);
            }
            crate::generated::Item::Macro(_) => todo!(),
        }
    }

    Ok(())
}
