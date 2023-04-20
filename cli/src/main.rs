#![feature(trait_upcasting)]

mod db;

use std::{io::Write, path::PathBuf};

use clap::Parser;
use futures_util::StreamExt;
use itertools::Itertools;
use miette::{bail, Context, IntoDiagnostic, Result};
use mist_core::{hir, mir, salsa, util::Position};
use mist_syntax::SourceSpan;
use mist_viper_backend::{gen::ViperOutput, lower::ViperSourceMap};
use tracing::{error, info, warn};
use tracing_subscriber::prelude::*;
use viperserver::verification::Details;

#[tokio::main]
async fn main() -> Result<()> {
    miette::set_panic_hook();
    dotenvy::dotenv().into_diagnostic()?;

    tracing_subscriber::Registry::default()
        // .with(tracing_error::ErrorLayer::default())
        .with(
            tracing_subscriber::EnvFilter::builder()
                .with_default_directive(tracing_subscriber::filter::LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .with(
            tracing_subscriber::fmt::layer()
                .with_target(false)
                .without_time(),
        )
        .with(tracing_subscriber::filter::FilterFn::new(|m| {
            !m.target().contains("salsa")
        }))
        .init();

    cli().await?;

    Ok(())
}

#[derive(Debug, Parser)]
enum Cli {
    /// Generate the MIR for the given file
    Mir { file: PathBuf },
    /// Generate the Viper code for the given file
    MirViper { file: PathBuf },
    /// Verify the provided file using Viper
    Viper {
        #[clap(long, short, env)]
        viperserver_jar: PathBuf,
        file: PathBuf,
    },
}

async fn cli() -> Result<()> {
    match Cli::parse() {
        Cli::Mir { file } => {
            let db = crate::db::Database::default();

            let source = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = hir::SourceProgram::new(&db, source);
            let program = hir::parse_program(&db, source);
            for (_, cx, _, mir, _) in mir::lower_program(&db, program) {
                println!("{}", mir.serialize(mir::serialize::Color::Yes, &db, &cx));
                let cfg = mir::analysis::cfg::Cfg::compute(&mir);

                let dot = cfg.dot(&db, &cx, &mir);
                mir::analysis::cfg::dot_imgcat(dot);
            }
        }
        Cli::MirViper { file } => {
            let db = crate::db::Database::default();

            let source = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = hir::SourceProgram::new(&db, source);
            let program = hir::parse_program(&db, source);
            for (item, cx, _, mir, _) in mir::lower_program(&db, program) {
                info!("{}", item.name(&db));
                println!("{}", mir.serialize(mir::serialize::Color::Yes, &db, &cx));
                let cfg = mir::analysis::cfg::Cfg::compute(&mir);
                let dot = cfg.dot(&db, &cx, &mir);
                mir::analysis::cfg::dot_imgcat(dot);
                match mist_viper_backend::gen::viper_item(&db, cx, item, &mir) {
                    Ok(Some((viper_item, viper_body, _viper_source_map))) => {
                        let output = ViperOutput::generate(&viper_body, &viper_item);
                        println!("{}", output.buf);
                    }
                    Ok(None) => {
                        warn!("no viper code generated")
                    }
                    Err(err) => error!("{}", err),
                }
            }
        }
        Cli::Viper {
            viperserver_jar,
            file,
        } => {
            let db = crate::db::Database::default();

            let src = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = hir::SourceProgram::new(&db, src.clone());
            let program = hir::parse_program(&db, source);

            let parse_errors = program.errors(&db);
            let type_errors =
                mir::lower_program::accumulated::<mist_core::TypeCheckErrors>(&db, program);
            let mir_errors = mir::lower_program::accumulated::<mir::MirErrors>(&db, program);
            let viper_errors =
                if parse_errors.is_empty() && type_errors.is_empty() && mir_errors.is_empty() {
                    mist_viper_backend::gen::viper_file::accumulated::<
                        mist_viper_backend::lower::ViperLowerErrors,
                    >(&db, program)
                } else {
                    vec![]
                };

            let errors = itertools::chain!(
                parse_errors.iter().cloned().map(miette::Error::new),
                type_errors.into_iter().map(miette::Error::new),
                mir_errors.into_iter().map(miette::Error::new),
                viper_errors.into_iter().map(miette::Error::new),
            )
            .collect_vec();

            if !errors.is_empty() {
                let num_errors = errors.len();
                for err in errors {
                    eprintln!(
                        "{:?}",
                        err.with_source_code(miette::NamedSource::new(
                            file.display().to_string(),
                            src.clone()
                        ))
                    );
                }

                bail!("failed due to {} previous errors", num_errors);
            }

            for (item, cx, _, mir, _) in mir::lower_program(&db, program) {
                info!("{}", item.name(&db));
                println!("{}", mir.serialize(mir::serialize::Color::Yes, &db, &cx));
                let cfg = mir::analysis::cfg::Cfg::compute(&mir);
                let dot = cfg.dot(&db, &cx, &mir);
                mir::analysis::cfg::dot_imgcat(dot);
            }

            let (viper_program, viper_body, viper_source_map) =
                mist_viper_backend::gen::viper_file(&db, program)?;
            let viper_output = ViperOutput::generate(&viper_body, &viper_program);
            let viper_src = &viper_output.buf;

            let mut viper_file = tempfile::Builder::new()
                .suffix(".vpr")
                .tempfile_in("./")
                .into_diagnostic()?;
            write!(viper_file, "{viper_src}").into_diagnostic()?;

            viper_file.flush().into_diagnostic()?;

            info!("Starting verification...");

            let server = viperserver::server::ViperServer::builder()
                .spawn_http(viperserver_jar)
                .await
                .into_diagnostic()?;

            let client = viperserver::client::Client::new(server)
                .await
                .into_diagnostic()?;

            let req = viperserver::client::VerificationRequest::silicon()
                .detect_z3()
                .into_diagnostic()?
                .verify_file(&viper_file)
                .into_diagnostic()?;

            let res = client.post(req).await.into_diagnostic()?;

            let mut stream = client.check_on_verification(&res).await.into_diagnostic()?;

            let mut num_errors = 0;

            while let Some(status) = stream.next().await {
                use viperserver::client::VerificationStatus as Vs;

                let status = status.into_diagnostic()?;
                match &status {
                    Vs::CopyrightReport { .. } => {}
                    Vs::WarningsDuringParsing(warnings) => {
                        if !warnings.is_empty() {
                            eprintln!("? {status:?}")
                        }
                    }
                    Vs::WarningsDuringTypechecking(warnings) => {
                        if !warnings.is_empty() {
                            eprintln!("? {status:?}")
                        }
                    }
                    Vs::InvalidArgsReport { .. } => eprintln!("? {status:?}"),
                    Vs::AstConstructionResult { details, .. } => {
                        let viper_file = viper_file.path().canonicalize().into_diagnostic()?;
                        let errors = details_to_miette(
                            &db,
                            &program,
                            &file,
                            viper_file.as_path(),
                            &src,
                            details,
                            &viper_source_map,
                            &viper_output,
                        );
                        for err in errors {
                            eprintln!("{err:?}");
                            num_errors += 1;
                        }
                    }
                    Vs::ProgramOutline { .. } => {}
                    Vs::ProgramDefinitions { .. } => {}
                    Vs::Statistics { .. } => {}
                    Vs::ExceptionReport { .. } => eprintln!("? {status:?}"),
                    Vs::ConfigurationConfirmation { .. } => {}
                    Vs::VerificationResult { details, .. } => {
                        let viper_file = viper_file.path().canonicalize().into_diagnostic()?;
                        let errors = details_to_miette(
                            &db,
                            &program,
                            &file,
                            viper_file.as_path(),
                            &src,
                            details,
                            &viper_source_map,
                            &viper_output,
                        );
                        for err in errors {
                            eprintln!("{err:?}");
                            num_errors += 1;
                        }
                    }
                    Vs::BackendSubProcessReport { .. } => eprintln!("? {status:?}"),
                }
            }

            if num_errors > 0 {
                bail!("failed due to {} previous errors", num_errors);
            }

            tracing::info!("Successfully verified!");

            drop(viper_file);
        }
    }

    Ok(())
}

fn details_to_miette<'a>(
    db: &'a dyn crate::Db,
    program: &'a hir::Program,
    src_path: &'a std::path::Path,
    viper_path: &'a std::path::Path,
    src: &'a str,
    details: &'a Details,
    viper_source_map: &'a ViperSourceMap,
    viper_output: &'a ViperOutput,
) -> impl Iterator<Item = miette::Error> + 'a {
    details.result.iter().flat_map(|result| {
        result.errors.iter().flat_map(|err| {
            let text = err
                .text
                .split_once(viper_path.file_name().unwrap().to_str().unwrap())
                .unwrap()
                .0
                .trim_end_matches(" (");
            if let Some(pos) = err.position.inner() {
                let viper_span = viper_position_to_internal(&viper_output.buf, pos)
                    .unwrap_or_else(|| SourceSpan::new_start_end(0, 0));
                let source_span = if let Some(back) = viper_output
                    .expr_map_back
                    .iter()
                    .sorted_by_key(|(span, _)| *span)
                    .find(|(span, _)| span.overlaps(viper_span))
                {
                    if let Some(&(item_id, back)) = viper_source_map.inst_expr_back.get(*back.1) {
                        let item = hir::item(db, *program, item_id).unwrap();
                        let (cx, source_map) =
                            hir::item_lower(db, *program, item_id, item).unwrap();
                        let (_mir, mir_source_map) = mir::lower_item(db, cx);
                        if let Some(back) = mir_source_map.expr_instr_map_back.get(back) {
                            Some(source_map.expr_span(*back))
                        } else {
                            warn!("no span was registered instruction for {:?}", back);
                            None
                        }
                    } else if let Some(&(item_id, back)) =
                        viper_source_map.block_expr_back.get(*back.1)
                    {
                        let item = hir::item(db, *program, item_id).unwrap();
                        let (cx, source_map) =
                            hir::item_lower(db, *program, item_id, item).unwrap();
                        let (_mir, mir_source_map) = mir::lower_item(db, cx);
                        if let Some(back) = mir_source_map.expr_block_map_back.get(back) {
                            Some(source_map.expr_span(*back))
                        } else {
                            warn!("no span was registered block for {:?}", back);
                            None
                        }
                    } else {
                        warn!("no span was registered for {:?}", back.1);
                        None
                    }
                } else {
                    warn!(
                        "unable to backtrace {}..{}",
                        Position::from_byte_offset(&viper_output.buf, viper_span.offset()),
                        Position::from_byte_offset(&viper_output.buf, viper_span.end())
                    );
                    None
                };

                #[derive(Debug, thiserror::Error, miette::Diagnostic)]
                #[error("{error}")]
                struct AdHoc {
                    error: String,
                    #[label("here")]
                    span: SourceSpan,
                    #[label("and here")]
                    span2: Option<SourceSpan>,
                }

                if let Some(source_span) = source_span {
                    Some(
                        miette::Error::new(AdHoc {
                            error: text.to_string(),
                            span: source_span,
                            span2: None,
                        })
                        .with_source_code(miette::NamedSource::new(
                            src_path.display().to_string(),
                            src.to_string(),
                        )),
                    )
                } else {
                    Some(
                        miette::Error::new(AdHoc {
                            error: text.to_string(),
                            span: viper_span,
                            span2: None,
                        })
                        .with_source_code(miette::NamedSource::new(
                            viper_path.display().to_string(),
                            viper_output.buf.to_string(),
                        )),
                    )
                }
            } else {
                eprintln!("{err:?}");
                None
            }
        })
    })
}

fn viper_position_to_internal(
    src: &str,
    pos: &viperserver::verification::Position,
) -> Option<SourceSpan> {
    fn pos_to_byte_offset(pos: &str) -> Option<Position> {
        let (a, b) = pos.split_once(':')?;
        let a: u32 = a.parse().unwrap();
        let b: u32 = b.parse().unwrap();

        Some(Position::new(a - 1, b - 1))
    }

    Some(SourceSpan::new_start_end(
        pos_to_byte_offset(&pos.start)?.to_byte_offset(src)?,
        pos_to_byte_offset(&pos.end)?.to_byte_offset(src)?,
    ))
}

#[salsa::jar(db=Db)]
pub struct Jar();

pub trait Db: mist_core::Db + mist_viper_backend::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + mist_viper_backend::Db + salsa::DbWithJar<Jar> {}
