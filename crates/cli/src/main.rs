use std::{fmt, io::Write, path::PathBuf, time::Instant};

use clap::Parser;
use futures_util::StreamExt;
use itertools::Itertools;
use miette::{bail, Context, IntoDiagnostic, Result};
use mist_cg_vpr::gen::ViperOutput;
use mist_core::{
    file::SourceFile,
    mir::{self, pass::Pass},
    mono,
    util::dot::graph_easy,
};
use tracing::{error, info, warn, Level};
use tracing_subscriber::prelude::*;

use mist_cli::{accumulated_errors, db::Database, Db, VerificationContext};

#[tokio::main]
async fn main() -> Result<()> {
    miette::set_panic_hook();
    color_backtrace::install();
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
                .without_time()
                .with_writer(std::io::stderr),
        )
        .with(tracing_subscriber::filter::FilterFn::new(|m| !m.target().contains("salsa")))
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
        #[clap(long, short, default_value_t=ViperBackend::default())]
        backend: ViperBackend,
        file: PathBuf,
    },
}

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
enum ViperBackend {
    #[default]
    Silicon,
    Carbon,
}

impl fmt::Display for ViperBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ViperBackend::Silicon => write!(f, "silicon"),
            ViperBackend::Carbon => write!(f, "carbon"),
        }
    }
}

async fn cli() -> Result<()> {
    let program_start = Instant::now();

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
            let file = SourceFile::new(&db, source);
            for item in mono::monomorphized_items(&db, file).items(&db) {
                info!("{}", item.name(&db));
                let span = tracing::span!(Level::DEBUG, "dump", def = item.name(&db).to_string());
                let _enter = span.enter();

                let Some(mir) = mir::lower_item(&db, item) else { continue };
                let mut ib = mir.ib(&db).clone();

                mir::pass::MentionPass::run(&db, &mut ib);

                if dump_mir {
                    let a = mir::analysis::liveness::FoldingAnalysisResults::compute(&db, &ib);
                    // println!("{}", ib.serialize(&db, mir::serialize::Color::Yes));
                    println!(
                        "{}",
                        ib.serialize_with_annotation(&db, mir::serialize::Color::Yes, |act| {
                            Some(a.try_entry(act.loc())?.debug_str(&db, &ib))
                        })
                    );
                }
                if dump_isorecursive {
                    mir::pass::IsorecursivePass::run(&db, &mut ib);
                    let a = mir::analysis::liveness::FoldingAnalysisResults::compute(&db, &ib);
                    if dump_mir {
                        println!(
                            "{}",
                            ib.serialize_with_annotation(&db, mir::serialize::Color::Yes, |act| {
                                Some(a.try_entry(act.loc())?.debug_str(&db, &ib))
                            })
                        );
                    }
                }
                if dump_cfg {
                    let cfg = mir::analysis::cfg::Cfg::compute(&db, &ib);
                    let dot = cfg.dot(&db, &ib);
                    if let Ok(g) = graph_easy(&dot) {
                        println!("{g}");
                    }

                    if dump_liveness {
                        let dot = cfg.analysis_dot(
                            &ib,
                            &mir::analysis::liveness::FoldingAnalysisResults::compute(&db, &ib),
                            |x| x.debug_str(&db, &ib),
                        );
                        if let Ok(g) = graph_easy(&dot) {
                            println!("{g}");
                        }
                    }
                }
                if dump_viper {
                    match mist_cg_vpr::gen::viper_item(&db, item) {
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
        Cli::Viper { viperserver_jar, backend, file: src_file } => {
            let db = Database::default();

            let src = std::fs::read_to_string(&src_file)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read `{}`", src_file.display()))?;
            let file = SourceFile::new(&db, src.clone());

            dump_errors(&db, &src_file, &src, file)?;

            let (viper_program, viper_body, viper_source_map) =
                mist_cg_vpr::gen::viper_file(&db, file)?;
            let viper_output = ViperOutput::generate(&viper_body, &viper_program);
            let viper_src = &viper_output.buf;

            let temp_mist_dir =
                tempfile::Builder::new().prefix(".mist.").tempdir_in("./").into_diagnostic()?;
            let mut viper_file = tempfile::Builder::new()
                .suffix(".vpr")
                .tempfile_in(temp_mist_dir.path())
                .into_diagnostic()?;
            write!(viper_file, "{viper_src}").into_diagnostic()?;

            viper_file.flush().into_diagnostic()?;

            info!("Starting verification...");

            let ts_spawn_viperserver = Instant::now();
            eprintln!("Spawning viperserver: {:?}", program_start.elapsed());

            let server = viperserver::server::ViperServer::builder()
                .spawn_http(viperserver_jar)
                .await
                .into_diagnostic()?;

            let client = viperserver::client::Client::new(server).await.into_diagnostic()?;

            let ts_start_verification = Instant::now();
            eprintln!("Starting verification: {:?}", program_start.elapsed());

            let req = match backend {
                ViperBackend::Silicon => viperserver::client::VerificationRequest::silicon()
                    .detect_z3()
                    .into_diagnostic()?
                    .verify_file(&viper_file),
                ViperBackend::Carbon => viperserver::client::VerificationRequest::carbon()
                    .detect_z3()
                    .into_diagnostic()?
                    .verify_file(&viper_file),
            }
            .into_diagnostic()?;

            let res = client.post(req).await.into_diagnostic()?;

            let ctx = VerificationContext {
                file,
                mist_src_path: &src_file,
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

            const PRINT_TIMINGS: bool = false;

            let ts_finished = Instant::now();

            if PRINT_TIMINGS {
                eprintln!("Finished: {:?}", program_start.elapsed());

                for (name, (a, b)) in ["prepare", "viperserver", "verification"].into_iter().zip(
                    [program_start, ts_spawn_viperserver, ts_start_verification, ts_finished]
                        .into_iter()
                        .tuple_windows(),
                ) {
                    let d = b.duration_since(a);
                    let ms = (d.as_nanos() as f64) / 1000000.0;
                    eprintln!("{name:>20}: {:>20}ms", ms);
                    print!("{ms},");
                }
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
    file: SourceFile,
) -> Result<()> {
    let errors = accumulated_errors(db, file).collect_vec();

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
