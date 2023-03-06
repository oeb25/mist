use miette::{miette, IntoDiagnostic, Result};

fn main() -> Result<()> {
    miette::set_panic_hook();
    tracing_subscriber::fmt()
        .without_time()
        .with_target(false)
        .init();

    let f = std::env::args()
        .nth(1)
        .ok_or_else(|| miette!("please provide file as first argument"))?;
    let src = std::fs::read_to_string(f).into_diagnostic()?;

    let db = mist_viper_backend::db::Database::default();

    let source = mist_core::ir::SourceProgram::new(&db, src);
    let program = mist_core::ir::parse_program(&db, source);
    let viper_file = mist_viper_backend::gen::viper_file(&db, program);

    println!("{viper_file}");

    Ok(())
}

// pub trait ToViper {
//     type Output: std::fmt::Display;
//     fn to_viper(&self) -> Result<Self::Output>;
// }

// impl ToViper for SourceFile {
//     type Output = silvers::program::Program;

//     fn to_viper(&self) -> Result<Self::Output> {
//         let mut p = Program {
//             domains: vec![],
//             fields: vec![],
//             functions: vec![],
//             predicates: vec![],
//             methods: vec![],
//             extensions: vec![],
//         };

//         for i in self.items() {
//             match i {
//                 Item::Const(c) => {
//                     info!("skipping const with name: {}", c.name().unwrap())
//                 }
//                 Item::Fn(f) => {
//                     info!("skipping fn with name: {}", f.name().unwrap())
//                 }
//                 Item::Struct(s) => p.predicates.push(s.to_viper()?),
//                 Item::Macro(m) => {
//                     info!("skipping macro with name: {}", m.name().unwrap())
//                 }
//             }
//         }

//         Ok(p)
//     }
// }

// impl ToViper for Struct {
//     type Output = Predicate;

//     fn to_viper(&self) -> Result<Self::Output> {
//         Ok(Predicate {
//             name: self
//                 .name()
//                 .ok_or_else(|| miette!("struct did not have a name"))?
//                 .to_string(),
//             formal_args: vec![LocalVarDecl {
//                 name: "this".to_string(),
//                 typ: Type::Atomic(AtomicType::Ref),
//             }],
//             body: None,
//         })
//     }
// }
