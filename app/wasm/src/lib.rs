#![feature(trait_upcasting)]

pub mod db;

use mist_codegen_viper::gen::ViperOutput;
use mist_core::util::Position;
use serde::{Deserialize, Serialize};
use typeshare::typeshare;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn init_hooks() {
    console_error_panic_hook::set_once();
    tracing_wasm::set_as_global_default();
}

#[wasm_bindgen]
pub fn parse(src: &str) -> String {
    let parse = mist_syntax::parse(src);
    let markers = parse
        .errors()
        .iter()
        .cloned()
        .flat_map(|e| miette_to_markers(src, miette::Error::new(e)))
        .collect();
    let node = parse.syntax();
    let res = ParseResult {
        markers,
        parse_tree: format!("{node:#?}"),
    };
    serde_json::to_string(&res).expect("failed to serialize")
}

#[wasm_bindgen]
pub fn type_check(src: &str) -> String {
    let db = db::Database::default();
    let file = mist_core::hir::SourceFile::new(&db, src.to_string());
    let parse = mist_core::hir::file::parse_file(&db, file);

    let parse_errors = parse.errors();
    let (viper_program, viper_body, _viper_source_map) =
        match mist_codegen_viper::gen::viper_file(&db, file) {
            Ok(res) => res,
            Err(e) => return format!("viper error: {e:?}"),
        };
    let viper_src = ViperOutput::generate(&viper_body, &viper_program).buf;
    let type_errors =
        mist_codegen_viper::gen::viper_file::accumulated::<mist_core::TypeCheckErrors>(&db, file);
    let markers = parse_errors
        .iter()
        .cloned()
        .map(miette::Error::new)
        .chain(type_errors.iter().cloned().map(miette::Error::new))
        .flat_map(|e| miette_to_markers(src, e))
        .collect();

    let res = ParseResult {
        markers,
        parse_tree: viper_src,
    };
    serde_json::to_string(&res).expect("failed to serialize")
}

fn miette_to_markers(src: &str, report: miette::Report) -> Vec<MarkerData> {
    report
        .labels()
        .unwrap_or_else(|| Box::new(vec![].into_iter()))
        .map(|label| {
            let start = Position::from_byte_offset(src, label.offset());
            let end = Position::from_byte_offset(src, label.offset() + label.len());
            MarkerData {
                severity: MarkerSeverity::Error,
                message: report.to_string(), // label.label().unwrap_or("here").to_string(),
                start_line_number: start.line + 1,
                start_column: start.character + 1,
                end_line_number: end.line + 1,
                end_column: end.character + 1,
                related_information: None,
                tags: None,
            }
        })
        .collect()
}

#[typeshare]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ParseResult {
    parse_tree: String,
    markers: Vec<MarkerData>,
}

#[typeshare]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MarkerData {
    // code?: string | {
    //     value: string;
    //     target: Uri;
    // };
    // source?: string;
    related_information: Option<Vec<RelatedInformation>>,
    tags: Option<Vec<MarkerTag>>,
    severity: MarkerSeverity,
    message: String,
    start_line_number: u32,
    start_column: u32,
    end_line_number: u32,
    end_column: u32,
}

#[typeshare]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[repr(u8)]
pub enum MarkerSeverity {
    Hint = 1,
    Info = 2,
    Warning = 4,
    Error = 8,
}

#[typeshare]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[repr(u8)]
pub enum MarkerTag {
    Unnecessary = 1,
    Deprecated = 2,
}

#[typeshare]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RelatedInformation {
    /// Is actually a `Uri`
    resource: String,
    message: String,
    start_line_number: u32,
    start_column: u32,
    end_line_number: u32,
    end_column: u32,
}
