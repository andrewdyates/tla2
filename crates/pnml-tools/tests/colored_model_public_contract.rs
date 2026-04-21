// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use pnml_tools::error::PnmlError;
use pnml_tools::examination::{Examination, ExaminationValue};
use pnml_tools::model::{collect_examination_for_model, load_model_dir, SourceNetKind};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn mcc_model_dir(model: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

#[test]
fn test_real_colored_model_requires_high_level_loader() {
    const MODEL: &str = "TokenRing-COL-010";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let dir = mcc_model_dir(MODEL);
    let err = pnml_tools::parser::parse_pnml_dir(&dir)
        .expect_err("low-level parser should reject symmetricnet inputs");
    assert!(
        matches!(err, PnmlError::UnsupportedNetType { .. }),
        "expected UnsupportedNetType from low-level parser, got: {err:?}"
    );

    let model = load_model_dir(&dir).expect("high-level loader should unfold supported MCC net");
    assert_eq!(model.model_name(), MODEL);
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);
    assert!(
        model.net().num_places() > 0 && model.net().num_transitions() > 0,
        "prepared colored model should expose a non-empty unfolded P/T net"
    );
}

#[test]
fn test_real_colored_model_runs_statespace_smoke_through_prepared_model() {
    const MODEL: &str = "TokenRing-COL-010";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let dir = mcc_model_dir(MODEL);
    let model = load_model_dir(&dir).expect("TokenRing colored model should load");
    // Keep this as a fast public-contract smoke: the goal is to prove that the
    // prepared colored model can execute a typed examination path externally,
    // not to run a full MCC measurement slice in the build loop.
    let config = pnml_tools::explorer::ExplorationConfig::new(1).with_workers(1);
    let records = collect_examination_for_model(&model, Examination::StateSpace, &config)
        .expect("StateSpace should execute through PreparedModel");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, format!("{MODEL}-StateSpace"));
    assert!(
        matches!(records[0].value, ExaminationValue::StateSpace(_)),
        "expected typed StateSpace result, got {:?}",
        records[0].value
    );
}
