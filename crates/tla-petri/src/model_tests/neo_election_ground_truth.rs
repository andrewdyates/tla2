// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NeoElection-COL-2 ground-truth regression tests.
//!
//! For reachability examinations (ReachabilityFireability, ReachabilityCardinality),
//! the official COL and PT property XMLs at the same index ARE the same formula —
//! the PT version is a direct leaf expansion of the COL version (one colored name
//! expands to all its unfolded copies). However, the unfolded net naming
//! convention differs between our unfold and the official MCC PT companion, so
//! we validate correctness against the official MCC ground-truth labels rather
//! than against the PT model's verdicts.

use super::*;
use fixtures::mcc_input_dir;

/// Ground truth from registry/mcc-labels/reachability-fireability-2024.csv
pub(super) const NEO_ELECTION_COL2_RF_TRUTH: [bool; 16] = [
    false, false, false, true, false, true, false, true, true, false, false, true, true, false,
    false, false,
];

/// Ground truth from registry/mcc-labels/reachability-cardinality-2024.csv
pub(super) const NEO_ELECTION_COL2_RC_TRUTH: [bool; 16] = [
    false, false, true, false, true, false, true, false, true, false, false, true, false, true,
    true, false,
];

#[test]
fn test_neo_election_col2_reachability_fireability_ground_truth() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    let model = load_model_dir(&dir).expect("NeoElection-COL-2 should unfold");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);

    let config = ExplorationConfig::new(50_000).with_workers(1);
    let records = collect_examination_core(
        model.net(),
        model.model_name(),
        model.model_dir(),
        model.aliases(),
        Examination::ReachabilityFireability,
        &config,
        false,
    )
    .expect("ReachabilityFireability dispatch should succeed");

    assert_eq!(records.len(), 16, "16 properties expected");

    let mut wrong = Vec::new();
    for rec in &records {
        let idx: usize = rec
            .formula_id
            .rsplit('-')
            .next()
            .and_then(|s| s.parse().ok())
            .expect("formula_id should end with numeric index");
        let expected = NEO_ELECTION_COL2_RF_TRUTH[idx];
        eprintln!("  RF-{:02}: {:?} (truth={})", idx, rec.value, expected);
        match rec.value {
            ExaminationValue::Verdict(Verdict::True) => {
                if !expected {
                    wrong.push(format!(
                        "{} got TRUE but ground truth is false",
                        rec.formula_id
                    ));
                }
            }
            ExaminationValue::Verdict(Verdict::False) => {
                if expected {
                    wrong.push(format!(
                        "{} got FALSE but ground truth is true",
                        rec.formula_id
                    ));
                }
            }
            ExaminationValue::Verdict(Verdict::CannotCompute) => {}
            _ => panic!("unexpected value for {}: {:?}", rec.formula_id, rec.value),
        }
    }
    assert!(wrong.is_empty(), "Wrong answers:\n{}", wrong.join("\n"));
}

#[test]
fn test_neo_election_col2_reachability_cardinality_ground_truth() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    let model = load_model_dir(&dir).expect("NeoElection-COL-2 should unfold");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);

    let config = ExplorationConfig::new(50_000).with_workers(1);
    let records = collect_examination_core(
        model.net(),
        model.model_name(),
        model.model_dir(),
        model.aliases(),
        Examination::ReachabilityCardinality,
        &config,
        false,
    )
    .expect("ReachabilityCardinality dispatch should succeed");

    assert_eq!(records.len(), 16, "16 properties expected");

    for rec in &records {
        let idx: usize = rec
            .formula_id
            .rsplit('-')
            .next()
            .and_then(|s| s.parse().ok())
            .expect("formula_id should end with numeric index");
        let expected = NEO_ELECTION_COL2_RC_TRUTH[idx];
        match rec.value {
            ExaminationValue::Verdict(Verdict::True) => {
                assert!(
                    expected,
                    "{} got TRUE but ground truth is false",
                    rec.formula_id
                );
            }
            ExaminationValue::Verdict(Verdict::False) => {
                assert!(
                    !expected,
                    "{} got FALSE but ground truth is true",
                    rec.formula_id
                );
            }
            ExaminationValue::Verdict(Verdict::CannotCompute) => {}
            _ => panic!("unexpected value for {}: {:?}", rec.formula_id, rec.value),
        }
    }
}
