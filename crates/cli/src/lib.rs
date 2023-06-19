#![feature(trait_upcasting)]

pub mod db;

use itertools::Itertools;
use miette::Diagnostic;
use mist_codegen_viper::{
    gen::ViperOutput,
    lower::{ViperLowerError, ViperSourceMap},
};
use mist_core::{hir, mir, mono, salsa, util::Position, TypeCheckError};
use mist_syntax::{ast::Spanned, ParseError, SourceSpan};
use tracing::warn;
use viperserver::{verification::Details, VerificationStatus};

#[derive(Debug, Clone, thiserror::Error, Diagnostic)]
#[error("Mist error")]
pub enum MistError {
    Parse(
        #[from]
        #[diagnostic_source]
        ParseError,
    ),
    TypeCheck(
        #[from]
        #[diagnostic_source]
        TypeCheckError,
    ),
    Mir(
        #[from]
        #[diagnostic_source]
        mir::MirError,
    ),
    ViperLower(
        #[from]
        #[diagnostic_source]
        ViperLowerError,
    ),
}

impl MistError {
    pub fn inner_diagnostic(&self) -> Option<miette::Error> {
        match self {
            MistError::Parse(x) => Some(miette::Error::new(x.clone())),
            MistError::TypeCheck(x) => Some(miette::Error::new(x.clone())),
            MistError::Mir(x) => Some(miette::Error::new(x.clone())),
            MistError::ViperLower(x) => Some(miette::Error::new(x.clone())),
        }
    }
}

#[allow(unused)]
#[salsa::tracked]
fn lower_file_for_errors(db: &dyn crate::Db, file: hir::SourceFile) {
    for _ in mono::monomorphized_items(db, file).items(db) {}
}

pub fn accumulated_errors(
    db: &dyn crate::Db,
    file: hir::SourceFile,
) -> impl Iterator<Item = MistError> + '_ {
    let parse = hir::file::parse_file(db, file);
    let parse_errors = parse.errors();
    let type_errors = lower_file_for_errors::accumulated::<mist_core::TypeCheckErrors>(db, file);
    let mir_errors = lower_file_for_errors::accumulated::<mir::MirErrors>(db, file);
    let viper_errors = if parse_errors.is_empty() && type_errors.is_empty() && mir_errors.is_empty()
    {
        mist_codegen_viper::gen::viper_file::accumulated::<
            mist_codegen_viper::lower::ViperLowerErrors,
        >(db, file)
    } else {
        vec![]
    };

    itertools::chain!(
        parse_errors.iter().cloned().map(Into::into),
        type_errors.into_iter().map(Into::into),
        mir_errors.into_iter().map(Into::into),
        viper_errors.into_iter().map(Into::into),
    )
    .map(move |mut err| {
        match &mut err {
            MistError::Parse(_) => {}
            MistError::TypeCheck(_) => {}
            MistError::Mir(err) => err.populate_spans(
                |expr| Some(expr.ast(db).span()),
                |var| {
                    let (def, var) = var.id();
                    Some(def.hir(db)?.cx(db).var_decl_span(var))
                },
            ),
            MistError::ViperLower(err) => {
                err.populate_spans(|item, block_or_instr| {
                    let item_mir = mir::lower_item(db, item).unwrap();
                    let expr = item_mir.source_map(db).trace_expr(block_or_instr).unwrap();
                    Some(expr.ast(db).span())
                });
            }
        }
        err
    })
    .collect_vec()
    .into_iter()
}

pub struct VerificationContext<'a> {
    pub file: hir::SourceFile,
    pub mist_src_path: &'a std::path::Path,
    pub mist_src: &'a str,
    pub viper_path: &'a std::path::Path,
    pub viper_source_map: &'a ViperSourceMap,
    pub viper_output: &'a ViperOutput,
}

impl VerificationContext<'_> {
    pub fn handle_status(
        &self,
        db: &dyn crate::Db,
        status: VerificationStatus,
    ) -> Vec<miette::Error> {
        use viperserver::client::VerificationStatus as Vs;

        let mut outer_errors = vec![];

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
            Vs::InternalWarningMessage { .. } => {}
            Vs::InvalidArgsReport { .. } => eprintln!("? {status:?}"),
            Vs::AstConstructionResult { details, .. } => {
                let errors = self.details_to_miette(db, details);
                for err in errors {
                    eprintln!("{err:?}");
                    outer_errors.push(err);
                }
            }
            Vs::ProgramOutline { .. } => {}
            Vs::ProgramDefinitions { .. } => {}
            Vs::Statistics { .. } => {}
            Vs::ExceptionReport { .. } => eprintln!("? {status:?}"),
            Vs::ConfigurationConfirmation { .. } => {}
            Vs::VerificationResult { details, .. } => {
                let errors = self.details_to_miette(db, details);
                for err in errors {
                    eprintln!("{err:?}");
                    outer_errors.push(err);
                }
            }
            Vs::BackendSubProcessReport { .. } => eprintln!("? {status:?}"),
        }

        outer_errors
    }

    fn trace_span(&self, db: &dyn crate::Db, viper_span: SourceSpan) -> Option<SourceSpan> {
        if let Some(back) = self.viper_output.trace_expr(viper_span) {
            if let Some((item, back)) = self.viper_source_map.trace_exp(back) {
                let item_mir = mir::lower_item(db, item)?;
                if let Some(back) = item_mir.source_map(db).trace_expr(back) {
                    Some(back.ast(db).span())
                } else {
                    match back {
                        mir::BlockOrInstruction::Block(_) => {
                            warn!("no span was registered block for {back:?}")
                        }
                        mir::BlockOrInstruction::Instruction(_) => {
                            warn!("no span was registered instruction for {back:?}")
                        }
                    }
                    None
                }
            } else {
                warn!("no span was registered for {back:?}");
                None
            }
        } else {
            warn!(
                "unable to backtrace {}..{}",
                Position::from_byte_offset(&self.viper_output.buf, viper_span.offset()),
                Position::from_byte_offset(&self.viper_output.buf, viper_span.end())
            );
            None
        }
    }

    pub fn details_to_miette<'a>(
        &'a self,
        db: &'a dyn crate::Db,
        details: &'a Details,
    ) -> impl Iterator<Item = miette::Error> + 'a {
        details.result.iter().flat_map(|result| {
            result.errors.iter().flat_map(|err| self.details_err_to_miette(db, err))
        })
    }

    pub fn details_err_to_miette(
        &self,
        db: &dyn Db,
        err: &viperserver::verification::DetailsError,
    ) -> Option<miette::ErrReport> {
        let text = err
            .text
            .split_once(self.viper_path.file_name().unwrap().to_str().unwrap())
            .unwrap()
            .0
            .trim_end_matches(" (");
        if let Some(pos) = err.position.inner() {
            let viper_span = viper_position_to_internal(&self.viper_output.buf, pos)
                .unwrap_or_else(|| SourceSpan::new_start_end(0, 0));
            let source_span = self.trace_span(db, viper_span);

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
                        self.mist_src_path.display().to_string(),
                        self.mist_src.to_string(),
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
                        self.viper_path.display().to_string(),
                        self.viper_output.buf.to_string(),
                    )),
                )
            }
        } else {
            eprintln!("{err:?}");
            None
        }
    }
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
pub struct Jar(lower_file_for_errors);

pub trait Db: mist_core::Db + mist_codegen_viper::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + mist_codegen_viper::Db + salsa::DbWithJar<Jar> {}
