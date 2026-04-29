// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use pnml_tools::examination::{Examination, ExaminationValue, Verdict};
use pnml_tools::explorer::ExplorationConfig;
use pnml_tools::model::{collect_examination_for_model, load_model_dir};

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_benchmark(model: &str) -> bool {
    mcc_input_dir(model).join("model.pnml").exists()
}

#[test]
fn test_neo_election_col_liveness_matches_registry() {
    const MODEL: &str = "NeoElection-COL-2";

    if !has_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model = load_model_dir(mcc_input_dir(MODEL)).expect("NeoElection-COL-2 should load");
    let config = ExplorationConfig::new(50_000);
    let records = collect_examination_for_model(&model, Examination::Liveness, &config)
        .expect("Liveness should execute through PreparedModel");

    assert_eq!(records.len(), 1, "{MODEL} should emit one Liveness record");
    assert_eq!(
        records[0].formula_id,
        format!("{MODEL}-Liveness"),
        "{MODEL} should preserve the canonical Liveness formula id"
    );
    assert_eq!(
        records[0].value,
        ExaminationValue::Verdict(Verdict::False),
        "{MODEL} Liveness should match registry/mcc-labels/liveness-2024.csv"
    );
}
