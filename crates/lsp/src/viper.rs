use std::{
    path::{Path, PathBuf},
    sync::Mutex,
};

use futures_util::StreamExt;
use miette::{Context, IntoDiagnostic};
use mist_cli::VerificationContext;
use mist_codegen_viper::gen::ViperOutput;
use mist_core::hir;
use tracing::info;

pub struct VerifyFile<'a> {
    pub file: hir::SourceFile,
    pub viperserver_jar: &'a Path,
    pub viperserver: &'a viperserver::ViperServer,
    pub working_dir: &'a Path,
    pub mist_src_path: PathBuf,
    pub mist_src: &'a str,
}

impl VerifyFile<'_> {
    pub(crate) async fn run(
        &self,
        db: &Mutex<crate::db::Database>,
    ) -> miette::Result<Vec<miette::Report>> {
        let (viper_program, viper_body, viper_source_map) =
            mist_codegen_viper::gen::viper_file(&*db.lock().unwrap(), self.file)?;
        let viper_output = ViperOutput::generate(&viper_body, &viper_program);
        let viper_src = &viper_output.buf;

        std::fs::create_dir_all(self.working_dir)
            .into_diagnostic()
            .with_context(|| format!("creating working dir: {}", self.working_dir.display()))?;
        let viper_file = self
            .working_dir
            .join(self.mist_src_path.file_name().unwrap())
            .with_extension("vpr");
        tokio::fs::write(&viper_file, viper_src)
            .await
            .into_diagnostic()?;

        info!("Starting verification...");

        let server = viperserver::server::ViperServer::builder()
            .spawn_http(self.viperserver_jar)
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
            file: self.file,
            mist_src_path: &self.mist_src_path,
            mist_src: self.mist_src,
            viper_path: &viper_file,
            viper_source_map: &viper_source_map,
            viper_output: &viper_output,
        };

        let mut stream = client.check_on_verification(&res).await.into_diagnostic()?;

        let mut errors = vec![];

        while let Some(status) = stream.next().await {
            let status = status.into_diagnostic()?;
            errors.append(&mut ctx.handle_status(&*db.lock().unwrap(), status));
        }

        // if errors.is_empty() {
        //     bail!("failed due to {} previous errors", num_errors);
        // }

        drop(viper_file);

        info!("Finished verification!");

        Ok(errors)
    }
}
