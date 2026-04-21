// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use anyhow::Result;
use tla_petri::cli::{run_cli, PetriCommandMode, PetriRunArgs};

pub(crate) fn cmd_petri(model: PathBuf, examination: String, args: PetriRunArgs) -> Result<()> {
    run_cli(
        PetriCommandMode::Petri,
        Some(model),
        Some(examination),
        args,
    )
}

pub(crate) fn cmd_petri_simplify(model_dir: PathBuf, examination: String) -> Result<()> {
    let examination_kind = tla_petri::examination::Examination::from_name(&examination)?;
    let model = tla_petri::model::load_model_dir(&model_dir)?;
    let report =
        tla_petri::model::collect_simplification_report_for_model(&model, examination_kind)?;

    #[derive(serde::Serialize)]
    struct SimplificationReportOutput<'a> {
        model_name: &'a str,
        source_kind: &'a str,
        examination: &'a str,
        summary: &'a tla_petri::simplification_report::SimplificationSummary,
        properties: &'a [tla_petri::simplification_report::PropertySimplificationReport],
    }

    fn source_kind_label(kind: tla_petri::model::SourceNetKind) -> &'static str {
        match kind {
            tla_petri::model::SourceNetKind::Pt => "ptnet",
            tla_petri::model::SourceNetKind::SymmetricNet => "symmetricnet",
            _ => "unknown",
        }
    }

    let output = SimplificationReportOutput {
        model_name: model.model_name(),
        source_kind: source_kind_label(model.source_kind()),
        examination: examination_kind.as_str(),
        summary: &report.summary,
        properties: &report.properties,
    };

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

pub(crate) fn cmd_mcc(
    model_dir: Option<PathBuf>,
    examination: Option<String>,
    args: PetriRunArgs,
) -> Result<()> {
    run_cli(PetriCommandMode::Mcc, model_dir, examination, args)
}
