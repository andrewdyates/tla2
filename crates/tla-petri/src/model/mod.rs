// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! High-level model loading for MCC competition execution.
//!
//! Use [`load_model_dir`] as the public entry point for MCC model directories.
//! It accepts plain P/T nets directly and also attempts HLPNML parsing plus
//! unfolding for the currently supported colored-net (`symmetricnet`) subset.
//! The returned [`PreparedModel`] wraps the executable net with model name,
//! directory, source net kind, and property alias tables.

use std::path::Path;

use crate::error::PnmlError;
use crate::examination::{Examination, ExaminationRecord};
use crate::explorer::ExplorationConfig;
use crate::simplification_report::SimplificationReport;

mod aliases;
mod diagnostics;
mod execution;
mod loader;
mod render;
mod types;

pub(crate) use aliases::PropertyAliases;
pub use types::{PreparedModel, SourceNetKind};

/// Load a model directory into a [`PreparedModel`] ready for examination.
///
/// Plain P/T nets are parsed directly. Supported colored MCC models are
/// parsed through the HLPNML loader and unfolded into an executable P/T net.
///
/// Returns `PnmlError` if the model directory cannot be read, the PNML cannot
/// be parsed, or the input uses an unsupported net kind or colored-net
/// construct outside the supported unfolding subset.
pub fn load_model_dir(path: impl AsRef<Path>) -> Result<PreparedModel, PnmlError> {
    loader::load_model_dir(path)
}

/// Collect examination results for a [`PreparedModel`] as typed records.
pub fn collect_examination_for_model(
    model: &PreparedModel,
    examination: Examination,
    config: &ExplorationConfig,
) -> Result<Vec<ExaminationRecord>, PnmlError> {
    execution::collect_examination_for_model(model, examination, config)
}

/// Collect formula-simplification impact for one property examination.
pub fn collect_simplification_report_for_model(
    model: &PreparedModel,
    examination: Examination,
) -> Result<SimplificationReport, PnmlError> {
    execution::collect_simplification_report_for_model(model, examination)
}

/// Run an examination for a [`PreparedModel`] and print MCC output to stdout.
pub fn run_examination_for_model(
    model: &PreparedModel,
    examination: Examination,
    config: &ExplorationConfig,
) {
    render::run_examination_for_model(model, examination, config);
}

#[cfg(test)]
pub(crate) use loader::load_model_dir_no_colored_reduce;

#[cfg(test)]
#[path = "../model_tests/mod.rs"]
mod model_tests;

#[cfg(test)]
#[path = "../model_ltl_budget_tests.rs"]
mod model_ltl_budget_tests;
