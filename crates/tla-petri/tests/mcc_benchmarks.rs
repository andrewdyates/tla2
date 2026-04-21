// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for MCC Petri net competition benchmarks.
//!
//! Each benchmark model lives in `tests/mcc_benchmarks/<name>/` at the repo
//! root, with a `model.pnml`, optional property XML files, and an
//! `expected.json` encoding the expected examination results.
//!
//! Tests parse the PNML, run each supported examination, and verify results
//! against the expected output.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tla_petri::examination::{
    collect_examination_with_dir, Examination, ExaminationRecord, ExaminationValue,
};
use tla_petri::explorer::ExplorationConfig;
use tla_petri::output::Verdict;
use tla_petri::parser;

/// Root of the MCC benchmarks directory relative to the workspace root.
fn benchmarks_dir() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/tla-petri -> repo root -> tests/mcc_benchmarks
    manifest
        .parent()
        .expect("crates/")
        .parent()
        .expect("repo root")
        .join("tests")
        .join("mcc_benchmarks")
}

fn config() -> ExplorationConfig {
    ExplorationConfig::new(100_000)
}

fn verdict_str(v: Verdict) -> &'static str {
    match v {
        Verdict::True => "TRUE",
        Verdict::False => "FALSE",
        Verdict::CannotCompute => "CANNOT_COMPUTE",
    }
}

fn load_expected(model_dir: &Path) -> serde_json::Value {
    let path = model_dir.join("expected.json");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    serde_json::from_str(&content)
        .unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

fn check_verdict_examination(
    records: &[ExaminationRecord],
    expected: &serde_json::Value,
    exam_name: &str,
) {
    let expected_map = expected[exam_name]
        .as_object()
        .unwrap_or_else(|| panic!("expected.json missing object for {exam_name}"));

    let actual: HashMap<&str, &ExaminationRecord> =
        records.iter().map(|r| (r.formula_id.as_str(), r)).collect();

    for (formula_id, expected_verdict) in expected_map {
        let record = actual
            .get(formula_id.as_str())
            .unwrap_or_else(|| panic!("missing result for formula {formula_id}"));
        let expected_str = expected_verdict
            .as_str()
            .expect("verdict should be a string");
        match &record.value {
            ExaminationValue::Verdict(v) => {
                assert_eq!(
                    verdict_str(*v),
                    expected_str,
                    "{formula_id}: expected {expected_str}, got {v}"
                );
            }
            other => {
                panic!("{formula_id}: expected verdict, got {other:?}");
            }
        }
    }
}

fn check_bound_examination(
    records: &[ExaminationRecord],
    expected: &serde_json::Value,
    exam_name: &str,
) {
    let expected_map = expected[exam_name]
        .as_object()
        .unwrap_or_else(|| panic!("expected.json missing object for {exam_name}"));

    let actual: HashMap<&str, &ExaminationRecord> =
        records.iter().map(|r| (r.formula_id.as_str(), r)).collect();

    for (formula_id, expected_bound) in expected_map {
        let record = actual
            .get(formula_id.as_str())
            .unwrap_or_else(|| panic!("missing result for formula {formula_id}"));
        let expected_val = expected_bound.as_u64().expect("bound should be a number");
        match &record.value {
            ExaminationValue::OptionalBound(Some(b)) => {
                assert_eq!(
                    *b, expected_val,
                    "{formula_id}: expected bound {expected_val}, got {b}"
                );
            }
            other => {
                panic!("{formula_id}: expected bound, got {other:?}");
            }
        }
    }
}

fn check_non_property_verdict(
    records: &[ExaminationRecord],
    expected: &serde_json::Value,
    exam_key: &str,
) {
    let expected_str = expected[exam_key]
        .as_str()
        .unwrap_or_else(|| panic!("expected.json missing string for {exam_key}"));

    assert_eq!(records.len(), 1, "{exam_key}: expected 1 record");
    match &records[0].value {
        ExaminationValue::Verdict(v) => {
            assert_eq!(
                verdict_str(*v),
                expected_str,
                "{exam_key}: expected {expected_str}, got {v}"
            );
        }
        other => {
            panic!("{exam_key}: expected verdict, got {other:?}");
        }
    }
}

fn check_state_space(records: &[ExaminationRecord], expected: &serde_json::Value) {
    let ss = &expected["StateSpace"];
    let expected_states = ss["states"].as_u64().expect("states") as usize;
    let expected_max_token_in_place = ss["max_token_in_place"]
        .as_u64()
        .expect("max_token_in_place");
    let expected_max_token_sum = ss["max_token_sum"].as_u64().expect("max_token_sum");

    assert_eq!(records.len(), 1, "StateSpace: expected 1 record");
    match &records[0].value {
        ExaminationValue::StateSpace(Some(report)) => {
            assert_eq!(
                report.states, expected_states,
                "StateSpace states: expected {expected_states}, got {}",
                report.states
            );
            assert_eq!(
                report.max_token_in_place, expected_max_token_in_place,
                "StateSpace max_token_in_place: expected {expected_max_token_in_place}, got {}",
                report.max_token_in_place
            );
            assert_eq!(
                report.max_token_sum, expected_max_token_sum,
                "StateSpace max_token_sum: expected {expected_max_token_sum}, got {}",
                report.max_token_sum
            );
        }
        other => {
            panic!("StateSpace: expected StateSpace report, got {other:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Mutex model tests
// ---------------------------------------------------------------------------

#[test]
fn test_mutex_reachability_deadlock() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "Mutex",
        &dir,
        Examination::ReachabilityDeadlock,
        &config(),
    )
    .expect("ReachabilityDeadlock");
    check_non_property_verdict(&records, &expected, "ReachabilityDeadlock");
}

#[test]
fn test_mutex_one_safe() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::OneSafe, &config())
            .expect("OneSafe");
    check_non_property_verdict(&records, &expected, "OneSafe");
}

#[test]
fn test_mutex_quasi_liveness() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::QuasiLiveness, &config())
            .expect("QuasiLiveness");
    check_non_property_verdict(&records, &expected, "QuasiLiveness");
}

#[test]
fn test_mutex_stable_marking() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::StableMarking, &config())
            .expect("StableMarking");
    check_non_property_verdict(&records, &expected, "StableMarking");
}

#[test]
fn test_mutex_liveness() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::Liveness, &config())
            .expect("Liveness");
    check_non_property_verdict(&records, &expected, "Liveness");
}

#[test]
fn test_mutex_state_space() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::StateSpace, &config())
            .expect("StateSpace");
    check_state_space(&records, &expected);
}

#[test]
fn test_mutex_reachability_fireability() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "Mutex",
        &dir,
        Examination::ReachabilityFireability,
        &config(),
    )
    .expect("ReachabilityFireability");
    check_verdict_examination(&records, &expected, "ReachabilityFireability");
}

#[test]
fn test_mutex_ctl_fireability() {
    let dir = benchmarks_dir().join("mutex");
    let net = parser::parse_pnml_dir(&dir).expect("parse mutex PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "Mutex", &dir, Examination::CTLFireability, &config())
            .expect("CTLFireability");
    check_verdict_examination(&records, &expected, "CTLFireability");
}

// ---------------------------------------------------------------------------
// ProducerConsumer model tests
// ---------------------------------------------------------------------------

#[test]
fn test_producer_consumer_reachability_deadlock() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::ReachabilityDeadlock,
        &config(),
    )
    .expect("ReachabilityDeadlock");
    check_non_property_verdict(&records, &expected, "ReachabilityDeadlock");
}

#[test]
fn test_producer_consumer_one_safe() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::OneSafe,
        &config(),
    )
    .expect("OneSafe");
    check_non_property_verdict(&records, &expected, "OneSafe");
}

#[test]
fn test_producer_consumer_quasi_liveness() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::QuasiLiveness,
        &config(),
    )
    .expect("QuasiLiveness");
    check_non_property_verdict(&records, &expected, "QuasiLiveness");
}

#[test]
fn test_producer_consumer_stable_marking() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::StableMarking,
        &config(),
    )
    .expect("StableMarking");
    check_non_property_verdict(&records, &expected, "StableMarking");
}

#[test]
fn test_producer_consumer_liveness() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::Liveness,
        &config(),
    )
    .expect("Liveness");
    check_non_property_verdict(&records, &expected, "Liveness");
}

#[test]
fn test_producer_consumer_state_space() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::StateSpace,
        &config(),
    )
    .expect("StateSpace");
    check_state_space(&records, &expected);
}

#[test]
fn test_producer_consumer_upper_bounds() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::UpperBounds,
        &config(),
    )
    .expect("UpperBounds");
    check_bound_examination(&records, &expected, "UpperBounds");
}

#[test]
fn test_producer_consumer_reachability_cardinality() {
    let dir = benchmarks_dir().join("producer_consumer");
    let net = parser::parse_pnml_dir(&dir).expect("parse producer_consumer PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "ProducerConsumer",
        &dir,
        Examination::ReachabilityCardinality,
        &config(),
    )
    .expect("ReachabilityCardinality");
    check_verdict_examination(&records, &expected, "ReachabilityCardinality");
}

// ---------------------------------------------------------------------------
// TokenRing model tests
// ---------------------------------------------------------------------------

#[test]
fn test_token_ring_reachability_deadlock() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "TokenRing",
        &dir,
        Examination::ReachabilityDeadlock,
        &config(),
    )
    .expect("ReachabilityDeadlock");
    check_non_property_verdict(&records, &expected, "ReachabilityDeadlock");
}

#[test]
fn test_token_ring_one_safe() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "TokenRing", &dir, Examination::OneSafe, &config())
            .expect("OneSafe");
    check_non_property_verdict(&records, &expected, "OneSafe");
}

#[test]
fn test_token_ring_quasi_liveness() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "TokenRing",
        &dir,
        Examination::QuasiLiveness,
        &config(),
    )
    .expect("QuasiLiveness");
    check_non_property_verdict(&records, &expected, "QuasiLiveness");
}

#[test]
fn test_token_ring_stable_marking() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "TokenRing",
        &dir,
        Examination::StableMarking,
        &config(),
    )
    .expect("StableMarking");
    check_non_property_verdict(&records, &expected, "StableMarking");
}

#[test]
fn test_token_ring_liveness() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "TokenRing", &dir, Examination::Liveness, &config())
            .expect("Liveness");
    check_non_property_verdict(&records, &expected, "Liveness");
}

#[test]
fn test_token_ring_state_space() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records =
        collect_examination_with_dir(&net, "TokenRing", &dir, Examination::StateSpace, &config())
            .expect("StateSpace");
    check_state_space(&records, &expected);
}

#[test]
fn test_token_ring_ltl_fireability() {
    let dir = benchmarks_dir().join("token_ring");
    let net = parser::parse_pnml_dir(&dir).expect("parse token_ring PNML");
    let expected = load_expected(&dir);
    let records = collect_examination_with_dir(
        &net,
        "TokenRing",
        &dir,
        Examination::LTLFireability,
        &config(),
    )
    .expect("LTLFireability");
    check_verdict_examination(&records, &expected, "LTLFireability");
}
