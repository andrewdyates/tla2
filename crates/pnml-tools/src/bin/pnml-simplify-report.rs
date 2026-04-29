// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use clap::Parser;
use serde::Serialize;

#[derive(Parser)]
#[command(
    name = "pnml-simplify-report",
    about = "Emit JSON formula-simplification impact for one MCC model examination"
)]
struct Cli {
    /// MCC examination name with property XML, for example ReachabilityFireability
    #[arg(long)]
    examination: String,

    /// Model directory containing model.pnml and the examination XML
    model_dir: PathBuf,
}

#[derive(Serialize)]
struct SimplificationReportOutput<'a> {
    model_name: &'a str,
    source_kind: &'a str,
    examination: &'a str,
    summary: &'a pnml_tools::simplification_report::SimplificationSummary,
    properties: &'a [pnml_tools::simplification_report::PropertySimplificationReport],
}

fn source_kind_label(kind: pnml_tools::model::SourceNetKind) -> &'static str {
    match kind {
        pnml_tools::model::SourceNetKind::Pt => "ptnet",
        pnml_tools::model::SourceNetKind::SymmetricNet => "symmetricnet",
        _ => "unknown",
    }
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let examination = pnml_tools::examination::Examination::from_name(&cli.examination)?;

    let model = pnml_tools::model::load_model_dir(&cli.model_dir)?;
    let report = pnml_tools::model::collect_simplification_report_for_model(&model, examination)?;
    let output = SimplificationReportOutput {
        model_name: model.model_name(),
        source_kind: source_kind_label(model.source_kind()),
        examination: examination.as_str(),
        summary: &report.summary,
        properties: &report.properties,
    };

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}
