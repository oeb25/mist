use salsa::DebugWithDb;
use tracing_test::traced_test;

use crate::hir::function_body;

// #[test]
// fn basic() {
//     let db = crate::db::Database::default();

//     let source =
//         crate::hir::SourceProgram::new(&db, include_str!("../../examples/list.mist").to_string());
//     let program = crate::hir::parse_program(&db, source);
//     let functions = crate::hir::functions(&db, program);
//     for function in &functions {
//         let param_list = function.param_list(&db);
//         for param in &param_list.params {
//             eprintln!("{:?}: {:?}", param.name, param.ty.debug_all(&db));
//         }
//         if let Some(body) = function_body(&db, program, *function) {
//             eprintln!("{:?}", body)
//         }
//     }
//     functions[0].name(&db);
//     eprintln!("Functions = {:?}", functions.debug_all(&db));
// }

// #[test]
// #[traced_test]
// fn call_with_index_argument() {
//     let db = crate::db::Database::default();

//     let src = "fn a(x: int) { a(x[0]); }";
//     let source = crate::hir::SourceProgram::new(&db, src.to_string());
//     let program = crate::hir::parse_program(&db, source);
//     let functions = crate::hir::functions(&db, program);
//     eprintln!("Functions = {:?}", functions.debug_all(&db));
// }

// #[test]
// #[traced_test]
// fn two_calls_missing_semi() {
//     let db = crate::db::Database::default();

//     let src = "fn f() { f() f() }";
//     let source = crate::hir::SourceProgram::new(&db, src.to_string());
//     let program = crate::hir::parse_program(&db, source);
//     let functions = crate::hir::functions(&db, program);
//     eprintln!("Functions = {:#?}", functions.debug_all(&db));
//     assert_eq!(program.errors(&db).len(), 1);
// }
