use std::{io::Write, path::PathBuf};

use clap::Parser;
use futures_util::StreamExt;
use itertools::Itertools;
use miette::{bail, Context, IntoDiagnostic, Result};
use mist_codegen_viper::gen::ViperOutput;
use mist_core::{hir, mir};
use tracing::{error, info, warn, Level};
use tracing_subscriber::prelude::*;

use mist_cli::{accumulated_errors, db::Database, Db, VerificationContext};

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
    /// Dump the program at different stages of transformation
    Dump {
        #[clap(short, long)]
        mir: bool,
        #[clap(short, long)]
        cfg: bool,
        #[clap(short, long)]
        liveness: bool,
        #[clap(short, long)]
        isorecursive: bool,
        #[clap(short, long)]
        viper: bool,
        file: PathBuf,
    },
    /// Verify the provided file using Viper
    Viper {
        #[clap(long, short, env)]
        viperserver_jar: PathBuf,
        file: PathBuf,
    },
}

async fn cli() -> Result<()> {
    match Cli::parse() {
        Cli::Dump {
            mir: dump_mir,
            cfg: dump_cfg,
            liveness: dump_liveness,
            isorecursive: dump_isorecursive,
            viper: dump_viper,
            file,
        } => {
            let db = Database::default();

            let source = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = hir::SourceProgram::new(&db, source);
            let program = hir::parse_program(&db, source);
            for (item, cx, _, mut mir, _) in mir::lower_program(&db, program) {
                info!("{}", item.name(&db));
                let span = tracing::span!(Level::DEBUG, "dump", item = item.name(&db).to_string());
                let _enter = span.enter();
                if dump_mir {
                    println!(
                        "{}",
                        mir.serialize(&db, Some(&cx), mir::serialize::Color::Yes)
                    );
                }
                if dump_isorecursive {
                    mir::analysis::isorecursive::IsorecursivePass::new(&cx, &mut mir).run();
                    if dump_mir {
                        println!(
                            "{}",
                            mir.serialize(&db, Some(&cx), mir::serialize::Color::Yes)
                        );
                    }
                }
                if dump_cfg {
                    let cfg = mir::analysis::cfg::Cfg::compute(&mir);
                    let dot = cfg.dot(&db, &cx, &mir);
                    mir::analysis::cfg::dot_imgcat(&dot);

                    if dump_liveness {
                        mir::analysis::cfg::dot_imgcat(&cfg.analysis_dot(
                            &mir::analysis::liveness::FoldingAnalysisResults::compute(&cx, &mir),
                            |x| {
                                format!(
                                    "{:?}",
                                    x.leafs()
                                        .map(|p| {
                                            mir::serialize::serialize_place(
                                                mir::serialize::Color::No,
                                                Some(&cx),
                                                &mir,
                                                &p,
                                            )
                                        })
                                        .collect::<std::collections::HashSet<_>>()
                                )
                            },
                        ));
                    }
                }
                if dump_viper {
                    match mist_codegen_viper::gen::viper_item(&db, cx, item, &mir) {
                        Ok((viper_items, viper_body, _viper_source_map)) => {
                            if viper_items.is_empty() {
                                warn!("no viper code generated")
                            }
                            for viper_item in viper_items {
                                let output = ViperOutput::generate(&viper_body, &viper_item);
                                println!("{}", output.buf);
                            }
                        }
                        Err(err) => error!("{:?}", err),
                    }
                }
            }
        }
        Cli::Viper {
            viperserver_jar,
            file,
        } => {
            let db = Database::default();

            let src = std::fs::read_to_string(&file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", file.display()))?;
            let source = hir::SourceProgram::new(&db, src.clone());
            let program = hir::parse_program(&db, source);

            dump_errors(&db, &file, &src, program)?;

            let (viper_program, viper_body, viper_source_map) =
                mist_codegen_viper::gen::viper_file(&db, program)?;
            let viper_output = ViperOutput::generate(&viper_body, &viper_program);
            let viper_src = &viper_output.buf;

            let temp_mist_dir = tempfile::Builder::new()
                .prefix(".mist.")
                .tempdir_in("./")
                .into_diagnostic()?;
            let mut viper_file = tempfile::Builder::new()
                .suffix(".vpr")
                .tempfile_in(temp_mist_dir.path())
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

            let ctx = VerificationContext {
                program,
                mist_src_path: &file,
                mist_src: &src,
                viper_path: viper_file.path(),
                viper_source_map: &viper_source_map,
                viper_output: &viper_output,
            };

            let mut stream = client.check_on_verification(&res).await.into_diagnostic()?;

            let mut errors = vec![];

            while let Some(status) = stream.next().await {
                let status = status.into_diagnostic()?;
                errors.append(&mut ctx.handle_status(&db, status));
            }

            if !errors.is_empty() {
                bail!("failed due to {} previous errors", errors.len());
            }

            info!("Successfully verified!");

            drop(viper_file);
        }
    }

    Ok(())
}

fn dump_errors(
    db: &dyn crate::Db,
    path: &std::path::Path,
    src: &str,
    program: hir::Program,
) -> Result<()> {
    let errors = accumulated_errors(db, program).collect_vec();

    if !errors.is_empty() {
        let num_errors = errors.len();
        for err in errors {
            let err = err
                .inner_diagnostic()
                .map(|err| {
                    err.with_source_code(miette::NamedSource::new(
                        path.display().to_string(),
                        src.to_string(),
                    ))
                })
                .unwrap_or_else(|| miette::Error::new(err));
            eprintln!("{err:?}");
        }

        bail!("failed due to {} previous errors", num_errors);
    }

    Ok(())
}
