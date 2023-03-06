use salsa::DebugWithDb;

use crate::ir::function_body;

#[test]
fn basic() {
    let db = crate::db::Database::default();

    let source =
        crate::ir::SourceProgram::new(&db, include_str!("../../examples/list.mist").to_string());
    let program = crate::ir::parse_program(&db, source);
    let functions = crate::ir::functions(&db, program);
    for function in &functions {
        let param_list = function.param_list(&db);
        for param in &param_list.params {
            eprintln!("{:?}: {:?}", param.name, param.ty.debug_all(&db));
        }
        if let Some(body) = function_body(&db, program, *function) {
            eprintln!("{:?}", body)
        }
    }
    functions[0].name(&db);
    eprintln!("Functions = {:?}", functions.debug_all(&db));
}
