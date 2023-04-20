use std::{io::Write, path::Path};

use futures_util::StreamExt;
use miette::IntoDiagnostic;
use mist_cli::VerificationContext;
use mist_core::hir;
use mist_viper_backend::gen::ViperOutput;
use tracing::info;

pub async fn verify_file(
    db: &dyn crate::Db,
    program: hir::Program,
    viperserver_jar: &Path,
    mist_src_path: impl AsRef<Path>,
    mist_src: &str,
) -> miette::Result<Vec<miette::Report>> {
    let mist_src_path = mist_src_path.as_ref();
    let (viper_program, viper_body, viper_source_map) =
        mist_viper_backend::gen::viper_file(db, program)?;
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
        mist_src_path,
        mist_src,
        viper_path: viper_file.path(),
        viper_source_map: &viper_source_map,
        viper_output: &viper_output,
    };

    let mut stream = client.check_on_verification(&res).await.into_diagnostic()?;

    let mut errors = vec![];

    while let Some(status) = stream.next().await {
        let status = status.into_diagnostic()?;
        errors.append(&mut ctx.handle_status(db, status));
    }

    // if errors.is_empty() {
    //     bail!("failed due to {} previous errors", num_errors);
    // }

    drop(viper_file);

    Ok(errors)
}
