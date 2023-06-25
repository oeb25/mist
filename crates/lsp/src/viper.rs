use std::{
    path::{Path, PathBuf},
    sync::Arc,
    time::Duration,
};

use crossbeam_channel::{RecvTimeoutError, SendError};
use futures_util::StreamExt;
use miette::{Context, IntoDiagnostic};
use mist_cli::VerificationContext;
use mist_codegen_viper::gen::ViperOutput;
use mist_core::file::SourceFile;
use tracing::info;
use viperserver::{verification::DetailsError, ViperServerError};

pub struct VerifyFile<'a> {
    pub file: SourceFile,
    pub viperserver_jar: &'a Path,
    pub viperserver: &'a viperserver::ViperServer,
    pub working_dir: &'a Path,
    pub mist_src_path: PathBuf,
    pub mist_src: &'a str,
}

impl VerifyFile<'_> {
    pub(crate) fn run(&self, db: &dyn crate::Db) -> miette::Result<Vec<miette::Report>> {
        let (viper_program, viper_body, viper_source_map) =
            mist_codegen_viper::gen::viper_file(db, self.file)?;
        let viper_output = ViperOutput::generate(&viper_body, &viper_program);
        let viper_src = &viper_output.buf;

        std::fs::create_dir_all(self.working_dir)
            .into_diagnostic()
            .with_context(|| format!("creating working dir: {}", self.working_dir.display()))?;
        let viper_file =
            self.working_dir.join(self.mist_src_path.file_name().unwrap()).with_extension("vpr");

        let ctx = VerificationContext {
            file: self.file,
            mist_src_path: &self.mist_src_path,
            mist_src: self.mist_src,
            viper_path: &viper_file,
            viper_source_map: &viper_source_map,
            viper_output: &viper_output,
        };

        let input = VerificationInput::new(
            db,
            viper_file.clone(),
            viper_src.into(),
            self.viperserver_jar.into(),
        );
        let errors = verify_viper_src(db, input);
        let other_errors = verify_viper_src::accumulated::<VerificationErrors>(db, input);
        Ok(errors
            .into_iter()
            .flat_map(|status| ctx.details_err_to_miette(db, &status))
            .chain(other_errors.into_iter().map(|err| miette::miette!("{}", err)))
            .collect())
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum VerificationError {
    #[error("viper server error: {0}")]
    ViperServerError(#[from] ViperServerError),
    #[error("channel error: {0}")]
    ChannelError(#[from] SendError<DetailsError>),
}

#[salsa::accumulator]
pub struct VerificationErrors(Arc<VerificationError>);

#[salsa::interned]
pub struct VerificationInput {
    viper_file: PathBuf,
    viper_src: String,
    viperserver_jar: PathBuf,
}

#[salsa::tracked]
pub fn verify_viper_src(db: &dyn crate::Db, input: VerificationInput) -> Vec<DetailsError> {
    let handle = tokio::runtime::Handle::current();

    let viper_file = input.viper_file(db);
    let viper_src = input.viper_src(db);
    let viperserver_jar = input.viperserver_jar(db);

    std::fs::write(&viper_file, viper_src).unwrap();

    let (tx, rx) = crossbeam_channel::unbounded();

    info!("Starting verification...");
    let res: Result<_, VerificationError> = std::thread::spawn(move || {
        handle.block_on(async move {
            let server =
                viperserver::server::ViperServer::builder().spawn_http(viperserver_jar).await?;

            let client = viperserver::client::Client::new(server).await?;

            let req = viperserver::client::VerificationRequest::silicon()
                .detect_z3()?
                .verify_file(&viper_file)?;

            let res = client.post(req).await?;

            let mut stream = client.check_on_verification(&res).await?;

            while let Some(status) = stream.next().await {
                for err in status?.detail_errors().cloned() {
                    tx.send(err)?;
                }
            }
            Ok(())
        })
    })
    .join()
    .expect("thread paniced");

    let mut errors = Vec::new();

    loop {
        viper_unwind_if_cancelled(db, input);
        match rx.recv_timeout(Duration::from_millis(500)) {
            Ok(err) => errors.push(err),
            Err(RecvTimeoutError::Disconnected) => break,
            Err(RecvTimeoutError::Timeout) => {}
        }
    }

    if let Err(err) = res {
        VerificationErrors::push(db, Arc::new(err));
    }
    errors
}

/// HACK: This is used to simulate `Runtime::unwind_if_cancelled` which does not
/// currently exist in this version of salsa
#[salsa::tracked]
pub fn viper_unwind_if_cancelled(_db: &dyn crate::Db, _input: VerificationInput) {}
