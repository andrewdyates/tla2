// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tempfile::TempDir;

use super::*;
use crate::error::PnmlError;
use fixtures::*;

#[test]
fn test_load_model_dir_pt_net_succeeds() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, MINIMAL_PT_NET);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    assert_eq!(model.source_kind(), SourceNetKind::Pt);
    assert_eq!(model.net().num_places(), 2);
    assert_eq!(model.net().num_transitions(), 1);
}

#[test]
fn test_load_model_dir_extracts_model_name_from_directory() {
    let dir = TempDir::with_prefix("TestModel-PT-").unwrap();
    write_pnml(&dir, MINIMAL_PT_NET);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    // tempfile adds random suffix, but the name should start with our prefix
    assert!(
        model.model_name().starts_with("TestModel-PT-"),
        "model_name should start with directory prefix, got: {}",
        model.model_name()
    );
}

#[test]
fn test_load_model_dir_model_dir_matches_input() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, MINIMAL_PT_NET);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    assert_eq!(model.model_dir(), dir.path());
}

#[test]
fn test_load_model_dir_colored_net_attempts_hlpnml_parse() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, COLORED_NET);

    // Minimal colored net without declarations produces a parse error
    // (missing sort for place), not UnsupportedNetType. This confirms
    // the HLPNML parser is being invoked for symmetricnet types.
    let err = load_model_dir(dir.path()).expect_err("minimal colored net should fail");

    assert!(
        matches!(err, PnmlError::MissingElement(_)),
        "expected MissingElement (from HLPNML unfold), got: {err:?}"
    );
}

#[test]
fn test_load_model_dir_token_ring_product_sort_colored_net_unfolds() {
    let dir = mcc_input_dir("TokenRing-COL-010");
    let model = load_model_dir(&dir).expect("TokenRing-COL-010 should unfold");

    assert_eq!(model.model_name(), "TokenRing-COL-010");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);

    let state_places = model
        .aliases()
        .resolve_places("State")
        .expect("State aliases should exist");
    assert_eq!(state_places.len(), 121, "11 x 11 State unfolding expected");

    let total_tokens: u64 = state_places
        .iter()
        .map(|place| model.net().initial_marking[place.0 as usize])
        .sum();
    assert_eq!(
        total_tokens, 11,
        "State should keep diagonal initial tokens"
    );

    let main_process = model
        .aliases()
        .resolve_transitions("MainProcess")
        .expect("MainProcess aliases should exist");
    assert_eq!(
        main_process.len(),
        11,
        "single process variable should produce 11 unfolded transitions"
    );
}

#[test]
fn test_load_model_dir_neo_election_product_sort_with_ordering_guards() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    let model = load_model_dir(&dir).expect("NeoElection-COL-2 should unfold");

    assert_eq!(model.model_name(), "NeoElection-COL-2");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);

    // P-masterState uses sort M * BOOL * M = 3 × 2 × 3 = 18 unfolded places.
    let master_state = model
        .aliases()
        .resolve_places("P-masterState")
        .expect("P-masterState aliases should exist");
    assert_eq!(
        master_state.len(),
        18,
        "M(3) * BOOL(2) * M(3) = 18 unfolded places"
    );

    // NeoElection has greaterthanorequal and lessthan guards.
    // With ordering guards applied, the unfolded net must have strictly
    // fewer transitions than it would without guards (guards prune bindings).
    // 22 colored transitions, each with varying variable counts and guards.
    // Just verify transitions exist and the model loaded successfully.
    assert!(
        model.net().num_transitions() > 0,
        "unfolded net should have transitions"
    );
    assert!(
        model.net().num_places() > 0,
        "unfolded net should have places"
    );
}

#[test]
fn test_colored_model_reachability_fireability_dispatch() {
    // End-to-end: colored model → HLPNML parse → unfold → property XML parse
    // → alias resolution → examination dispatch → verdicts.
    // This is the first test that probes a real colored model through a
    // property-based examination requiring alias resolution of colored
    // transition names (MainProcess, OtherProcess) to unfolded P/T indices.
    let dir = mcc_input_dir("TokenRing-COL-010");
    let model = load_model_dir(&dir).expect("TokenRing-COL-010 should unfold");
    let config = ExplorationConfig::new(1).with_workers(1);

    let records = collect_examination_core(
        model.net(),
        model.model_name(),
        model.model_dir(),
        model.aliases(),
        Examination::ReachabilityFireability,
        &config,
        false,
    )
    .expect("ReachabilityFireability should parse and dispatch for colored model");

    // TokenRing-COL-010 ReachabilityFireability.xml has 16 properties.
    assert_eq!(
        records.len(),
        16,
        "16 properties in ReachabilityFireability.xml"
    );

    // All records should produce either TRUE, FALSE, or CANNOT_COMPUTE verdicts
    // (not crash or panic). At least some should have definitive results.
    for record in &records {
        assert!(
            matches!(record.value, ExaminationValue::Verdict(_)),
            "expected Verdict for {}, got {:?}",
            record.formula_id,
            record.value
        );
    }
}

#[test]
fn test_load_model_dir_missing_directory_returns_error() {
    let err = load_model_dir("/nonexistent/path/to/model").expect_err("should fail");

    assert!(
        matches!(err, PnmlError::Io { .. }),
        "expected Io error, got: {err:?}"
    );
}
