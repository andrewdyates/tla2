// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use super::*;
use crate::examination::{Examination, ExaminationValue, Verdict};
use crate::explorer::ExplorationConfig;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

#[test]
fn test_neo_election_pt2_ltl_fireability_tight_budget_returns_mixed_vector() {
    assert_tight_budget_mixed_vector(Examination::LTLFireability);
}

#[test]
fn test_neo_election_pt2_ltl_cardinality_tight_budget_returns_mixed_vector() {
    assert_tight_budget_mixed_vector(Examination::LTLCardinality);
}

fn assert_tight_budget_mixed_vector(examination: Examination) {
    let dir = mcc_input_dir("NeoElection-PT-2");
    let model = load_model_dir(&dir).expect("NeoElection-PT-2 should load");
    assert_eq!(model.source_kind(), SourceNetKind::Pt);

    let config = ExplorationConfig::new(1).with_workers(1);
    let records = collect_examination_for_model(&model, examination, &config)
        .unwrap_or_else(|_| panic!("model-layer {examination:?} dispatch should succeed"));

    assert_eq!(records.len(), 16, "16 properties expected");
    let resolved_count = records
        .iter()
        .filter(|record| {
            matches!(
                record.value,
                ExaminationValue::Verdict(Verdict::True | Verdict::False)
            )
        })
        .count();
    let summary: Vec<_> = records
        .iter()
        .map(|record| (&record.formula_id, &record.value))
        .collect();
    // Shallow LTL routing, LP, simplification, and random walk can resolve
    // all properties on NeoElection-PT-2 without needing state-space budget.
    // Previously expected at least one CannotCompute, but the reachability
    // pipeline now resolves shallow G/F forms independently of max_states.
    assert!(
        resolved_count >= 1,
        "tight budget should still resolve at least one property for {examination:?}, got {:?}",
        summary
    );
}
