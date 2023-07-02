use std::{
    sync::{Arc, Mutex},
    thread,
    time::Duration,
};

use salsa::ParallelDatabase;

use crate::highlighting;

use super::fixture;

// TODO: This fails spuriously
#[test]
#[ignore]
fn stress_type_in_fun() {
    let full_src = r#"
fn f() {
    let x = 5;

    while true {

    }
}
"#;

    let (db, fix) = fixture("");
    let db = Arc::new(Mutex::new(db));
    let file = fix.file();

    let (tx, rx) = crossbeam_channel::unbounded();

    thread::spawn({
        let db = Arc::clone(&db);
        move || {
            while let Ok(()) = rx.recv() {
                let db = db.lock().unwrap().snapshot();
                eprintln!("Received update!");
                let _ = highlighting::highlighting(&*db, file);
                eprintln!("Highlighted!");
            }
        }
    });
    for idx in 0..full_src.len() {
        let src = &full_src[0..idx];

        eprintln!("Setting text...");
        fix.file().set_text(&mut *db.lock().unwrap()).to(src.to_string());
        eprintln!("Sending update...");
        tx.send(()).unwrap();

        thread::sleep(Duration::from_millis(2));
    }
}
