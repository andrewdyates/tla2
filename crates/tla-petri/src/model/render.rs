// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::execution::collect_examination_for_model_inner;
use super::PreparedModel;

pub(super) fn run_examination_for_model(
    model: &PreparedModel,
    examination: crate::examination::Examination,
    config: &crate::explorer::ExplorationConfig,
) {
    match collect_examination_for_model_inner(model, examination, config, true) {
        Ok((records, diagnostics)) => {
            if let Some(load_diagnostics) = model.colored_load_diagnostics() {
                load_diagnostics.emit_stderr();
            }
            diagnostics.emit_stderr();
            for record in &records {
                println!("{}", record.to_mcc_line());
            }
        }
        Err(error) => {
            let exam_name = examination.as_str();
            eprintln!("Warning: failed to parse {exam_name}.xml: {error}");
            println!(
                "{}",
                crate::output::cannot_compute_line(model.model_name(), exam_name)
            );
        }
    }
}
