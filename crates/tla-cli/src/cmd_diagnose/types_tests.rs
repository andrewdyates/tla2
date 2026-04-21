// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn make_result(name: &str, verdict: SpecVerdict) -> SpecResult {
    SpecResult {
        name: name.to_string(),
        verdict,
        tla2_status: None,
        tla2_states: None,
        tlc_status: "pass".to_string(),
        tlc_states: None,
        tlc_error_type: None,
        error_details: None,
        expected_mismatch_reason: None,
        time_seconds: 0.0,
        timeout_seconds: 120,
        timeout_source: TimeoutSource::Cli,
    }
}

#[test]
fn test_tally_from_empty_results() {
    let tally = Tally::from_results(&[], 10);
    assert_eq!(tally.pass, 0);
    assert_eq!(tally.expected_mismatch, 0);
    assert_eq!(tally.mismatch, 0);
    assert!((tally.coverage - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_tally_from_mixed_results() {
    let results = vec![
        make_result("a", SpecVerdict::Pass),
        make_result("b", SpecVerdict::Pass),
        make_result("c", SpecVerdict::ExpectedMismatch),
        make_result("d", SpecVerdict::StateMismatch),
        make_result("e", SpecVerdict::Crash),
        make_result("f", SpecVerdict::FlakyTimeout),
        make_result("g", SpecVerdict::Skip),
        make_result("h", SpecVerdict::Timeout),
        make_result("i", SpecVerdict::FalsePositive),
        make_result("j", SpecVerdict::FalseNegative),
        make_result("k", SpecVerdict::BothFail),
        make_result("l", SpecVerdict::OomKilled),
    ];
    let tally = Tally::from_results(&results, 100);
    assert_eq!(tally.pass, 2);
    assert_eq!(tally.expected_mismatch, 1);
    assert_eq!(tally.mismatch, 1);
    assert_eq!(tally.crash, 1);
    assert_eq!(tally.oom_killed, 1);
    assert_eq!(tally.flaky_timeout, 1);
    assert_eq!(tally.skip, 1);
    assert_eq!(tally.timeout, 1);
    assert_eq!(tally.false_pos, 1);
    assert_eq!(tally.false_neg, 1);
    assert_eq!(tally.both_fail, 1);
    assert!((tally.coverage - 0.03).abs() < f64::EPSILON);
}

#[test]
fn test_tally_coverage_includes_flaky() {
    let results = vec![
        make_result("a", SpecVerdict::Pass),
        make_result("b", SpecVerdict::FlakyTimeout),
    ];
    let tally = Tally::from_results(&results, 4);
    assert!((tally.coverage - 0.5).abs() < f64::EPSILON);
}

fn appended_args_with_continue(
    policy: DiagnoseCheckPolicy,
    continue_on_error: bool,
) -> Vec<String> {
    let mut cmd = std::process::Command::new("tla2");
    policy.append_check_args(&mut cmd, continue_on_error);
    cmd.get_args()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect()
}

#[test]
fn test_diagnose_check_policy_baseline_parity_appends_auto_workers() {
    assert_eq!(
        appended_args_with_continue(DiagnoseCheckPolicy::from_checker_workers(None), true),
        vec!["--workers", "0", "--continue-on-error"]
    );
}

#[test]
fn test_diagnose_check_policy_auto_override_appends_zero_workers() {
    assert_eq!(
        appended_args_with_continue(DiagnoseCheckPolicy::from_checker_workers(Some(0)), true),
        vec!["--workers", "0", "--continue-on-error"]
    );
}

#[test]
fn test_diagnose_check_policy_explicit_parallel_override_appends_workers() {
    assert_eq!(
        appended_args_with_continue(DiagnoseCheckPolicy::from_checker_workers(Some(4)), true),
        vec!["--workers", "4", "--continue-on-error"]
    );
}

#[test]
fn test_diagnose_check_policy_first_error_omits_continue_flag() {
    assert_eq!(
        appended_args_with_continue(DiagnoseCheckPolicy::from_checker_workers(None), false),
        vec!["--workers", "0"]
    );
}

#[test]
fn test_diagnose_check_policy_parallel_first_error_omits_continue_flag() {
    assert_eq!(
        appended_args_with_continue(DiagnoseCheckPolicy::from_checker_workers(Some(4)), false),
        vec!["--workers", "4"]
    );
}

#[test]
fn test_continue_on_error_default_is_true() {
    let json = r#"{
        "tlc": {"status": "pass", "states": 100},
        "tla2": {"status": "unknown", "states": null},
        "verified_match": false,
        "category": "small"
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(
        spec.continue_on_error,
        "default should be true for backward compat"
    );
}

#[test]
fn test_continue_on_error_explicit_false() {
    let json = r#"{
        "tlc": {"status": "error", "states": 11285, "error_type": "invariant"},
        "tla2": {"status": "fail", "states": null},
        "verified_match": false,
        "category": "small",
        "continue_on_error": false
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(!spec.continue_on_error);
}

#[test]
fn test_effective_continue_on_error_invariant_auto_disables() {
    let json = r#"{
        "tlc": {"status": "pass", "states": 88152, "error_type": "invariant"},
        "tla2": {"status": "fail", "states": null},
        "verified_match": false,
        "category": "medium"
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(spec.continue_on_error, "raw field defaults to true");
    assert!(
        !spec.effective_continue_on_error(),
        "invariant error_type should auto-disable continue-on-error"
    );
}

#[test]
fn test_effective_continue_on_error_assume_violation_auto_disables() {
    let json = r#"{
        "tlc": {"status": "pass", "states": 500, "error_type": "assume_violation"},
        "tla2": {"status": "fail", "states": null},
        "verified_match": false,
        "category": "small"
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(
        !spec.effective_continue_on_error(),
        "assume_violation error_type should auto-disable continue-on-error"
    );
}

#[test]
fn test_effective_continue_on_error_no_error_type_stays_true() {
    let json = r#"{
        "tlc": {"status": "pass", "states": 100},
        "tla2": {"status": "unknown", "states": null},
        "verified_match": false,
        "category": "small"
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(
        spec.effective_continue_on_error(),
        "specs without error_type should continue-on-error"
    );
}

#[test]
fn test_effective_continue_on_error_explicit_false_overrides() {
    let json = r#"{
        "tlc": {"status": "pass", "states": 100},
        "tla2": {"status": "unknown", "states": null},
        "verified_match": false,
        "category": "small",
        "continue_on_error": false
    }"#;
    let spec: BaselineSpec = serde_json::from_str(json).unwrap();
    assert!(
        !spec.effective_continue_on_error(),
        "explicit false override should be respected"
    );
}
