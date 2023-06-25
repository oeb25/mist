use miette::{Context, IntoDiagnostic, Result};
use wasmer::{imports, Instance, Module, Store, Value};

fn main() -> Result<()> {
    let module_wat = r#"
        (module
        (type $t0 (func (param i32 i32) (result i32 i32)))

        (memory $mem 1)

        (func $add_one (export "add_one") (type $t0) (param $p0 i32) (param $p1 i32) (result i32) (result i32) (local $temp i32)
            (i32.store (i32.const 0) (i32.add (get_local $p0) (get_local $p1)))
            (local.set 0 (i32.sub (get_local $p0) (get_local $p1)))
            (i32.load (i32.const 0))
            (get_local $p0)))
    "#;

    let mut store = Store::default();
    let module = Module::new(&store, module_wat).into_diagnostic().wrap_err("create module")?;

    let import_object = imports! {};
    let instance = Instance::new(&mut store, &module, &import_object)
        .into_diagnostic()
        .wrap_err("create instance")?;

    let add_one =
        instance.exports.get_function("add_one").into_diagnostic().wrap_err("getting 'add_one'")?;
    let result = add_one
        .call(&mut store, &[Value::I32(42), Value::I32(27)])
        .into_diagnostic()
        .wrap_err("call 'add_one'")?;
    dbg!(result);

    Ok(())
}
