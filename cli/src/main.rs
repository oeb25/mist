mod db;

use std::{io::Write, path::PathBuf};

use clap::Parser;
use futures_util::StreamExt;
use itertools::Itertools;
use miette::{bail, Context, IntoDiagnostic, Result};
use mist_core::{salsa, util::Position};
use mist_syntax::SourceSpan;
use tracing::info;
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
    /// Analyze the given file and report errors, but don't generate any files
    Check { file: PathBuf },
    /// Format the given file and print the result to stdout
    Fmt { file: PathBuf },
    /// Verify the provided file using Viper
    Viper {
        #[clap(long, short, env)]
        viperserver_jar: PathBuf,
        file: PathBuf,
    },
}

async fn cli() -> Result<()> {
    match Cli::parse() {
        Cli::Check { file } => {
            let db = crate::db::Database::default();

            let source = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = mist_core::ir::SourceProgram::new(&db, source);
            let program = mist_core::ir::parse_program(&db, source);
        }
        Cli::Fmt { file } => {
            let db = crate::db::Database::default();

            let source = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = mist_core::ir::SourceProgram::new(&db, source);
            let program = mist_core::ir::parse_program(&db, source);
        }
        Cli::Viper {
            viperserver_jar,
            file,
        } => {
            let db = crate::db::Database::default();

            let src = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = mist_core::ir::SourceProgram::new(&db, src.clone());
            let program = mist_core::ir::parse_program(&db, source);
            let viper_src = mist_viper_backend::gen::viper_file(&db, program);

            let parse_errors = program.errors(&db);
            let type_errors = mist_viper_backend::gen::viper_file::accumulated::<
                mist_core::TypeCheckErrors,
            >(&db, program);

            let errors = itertools::chain!(
                parse_errors.iter().cloned().map(miette::Error::new),
                type_errors.into_iter().map(miette::Error::new),
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

            let mut viper_file = tempfile::Builder::new()
                .suffix(".vpr")
                .tempfile_in("./")
                .into_diagnostic()?;
            write!(viper_file, "{viper_src}").into_diagnostic()?;

            dbg!(&viper_file);
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
                    Vs::InvalidArgsReport { .. } => eprintln!("? {status:?}"),
                    Vs::AstConstructionResult { details, status } => {
                        let src = viper_src.to_string();
                        let viper_file = viper_file.path().canonicalize().into_diagnostic()?;
                        let errors = details_to_miette(viper_file.as_path(), &src, details);
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
                        let src = viper_src.to_string();
                        let viper_file = viper_file.path().canonicalize().into_diagnostic()?;
                        let errors = details_to_miette(viper_file.as_path(), &src, details);
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

            drop(viper_file);
        }
    }

    Ok(())
}

fn details_to_miette<'a>(
    path: &'a std::path::Path,
    src: &'a str,
    details: &'a Details,
) -> impl Iterator<Item = miette::Error> + 'a {
    details.result.iter().flat_map(|result| {
        result.errors.iter().flat_map(|err| {
            let text = err
                .text
                .split_once(path.file_name().unwrap().to_str().unwrap())
                .unwrap()
                .0
                .trim_end_matches(" (");
            if let Some(pos) = err.position.inner() {
                #[derive(Debug, thiserror::Error, miette::Diagnostic)]
                #[error("{error}")]
                struct AdHoc {
                    error: String,
                    #[label("here")]
                    span: SourceSpan,
                }

                Some(
                    miette::Error::new(AdHoc {
                        error: text.to_string(),
                        span: viper_position_to_internal(src, pos).unwrap(),
                    })
                    .with_source_code(miette::NamedSource::new(
                        path.display().to_string(),
                        src.to_string(),
                    )),
                )
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
