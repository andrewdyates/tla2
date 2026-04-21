// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::parser::parse_pnml_dir;
use crate::reduction::{analyze, reduce_iterative};

use super::super::{collect_examination_with_dir, Examination, ExaminationValue};

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

#[test]
fn test_ibm5964_iterative_reduction_discovers_stable_removed_places() {
    let model_dir = mcc_input_dir("IBM5964-PT-none");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: IBM5964-PT-none benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&model_dir).expect("IBM5964 PNML should parse");
    let pre_reduction = analyze(&net);
    assert!(
        pre_reduction.constant_places.is_empty() && pre_reduction.isolated_places.is_empty(),
        "IBM5964 should not hit the original-net stable-place shortcut; otherwise #1442 is not the right root cause"
    );

    let reduced = reduce_iterative(&net).expect("IBM5964 iterative reduction should succeed");
    assert!(
        !reduced.report.constant_places.is_empty() || !reduced.report.isolated_places.is_empty(),
        "IBM5964 should accumulate constant/isolated places during iterative reduction; otherwise #1442 does not exercise the intended multi-round reduction invariant"
    );
}

#[test]
fn test_ibm5964_stable_marking_dispatch_returns_true() {
    let model_dir = mcc_input_dir("IBM5964-PT-none");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: IBM5964-PT-none benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&model_dir).expect("IBM5964 PNML should parse");
    let records = collect_examination_with_dir(
        &net,
        "IBM5964-PT-none",
        &model_dir,
        Examination::StableMarking,
        &ExplorationConfig::default(),
    )
    .expect("StableMarking dispatch should succeed");

    assert_eq!(records.len(), 1, "StableMarking should emit one MCC record");
    assert_eq!(records[0].formula_id, "IBM5964-PT-none-StableMarking");
    assert_eq!(
        records[0].value,
        ExaminationValue::Verdict(Verdict::True),
        "IBM5964 StableMarking should be TRUE on the production dispatch path"
    );
}
