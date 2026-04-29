// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use super::*;

fn sample_expected_mismatch_result() -> SpecResult {
    SpecResult {
        name: "ExampleExpectedMismatch".to_string(),
        verdict: SpecVerdict::ExpectedMismatch,
        tla2_status: Some("ok".to_string()),
        tla2_states: Some(0),
        tlc_status: "error".to_string(),
        tlc_states: None,
        tlc_error_type: Some("unknown".to_string()),
        error_details: None,
        expected_mismatch_reason: Some(
            "TLC smoke harness requires IOEnvExec/CSVWrite side effects.".to_string(),
        ),
        time_seconds: 1.0,
        timeout_seconds: 120,
        timeout_source: TimeoutSource::Cli,
    }
}

fn sample_pass_result() -> SpecResult {
    SpecResult {
        name: "SmokeEWD998_SC".to_string(),
        verdict: SpecVerdict::Pass,
        tla2_status: Some("ok".to_string()),
        tla2_states: Some(0),
        tlc_status: "pass".to_string(),
        tlc_states: Some(0),
        tlc_error_type: None,
        error_details: None,
        expected_mismatch_reason: None,
        time_seconds: 1.0,
        timeout_seconds: 120,
        timeout_source: TimeoutSource::Cli,
    }
}

#[test]
fn test_build_json_report_includes_expected_mismatch_fields() {
    let results = vec![sample_expected_mismatch_result()];
    let tally = Tally::from_results(&results, 10);
    let report = build_json_report(
        &results,
        &tally,
        10,
        1,
        Path::new("/tmp/tla2"),
        RunConditions {
            cpu_count: 1,
            load_avg_1m: 0.0,
            load_avg_5m: 0.0,
            load_avg_15m: 0.0,
            timeout_floor_seconds: 120,
            timeout_seconds: 120,
            retries: 0,
            checker_policy: "baseline_parity",
            checker_workers: None,
        },
    );

    assert_eq!(report.schema_version, 7);
    assert_eq!(report.run_conditions.timeout_floor_seconds, 120);
    assert_eq!(report.run_conditions.timeout_seconds, 120);
    assert_eq!(report.summary.expected_mismatch, 1);
    assert_eq!(report.run_conditions.checker_policy, "baseline_parity");
    assert_eq!(report.run_conditions.checker_workers, None);
    assert_eq!(
        report.specs["ExampleExpectedMismatch"].status,
        "expected_mismatch"
    );
    assert_eq!(
        report.specs["ExampleExpectedMismatch"]
            .expected_mismatch_reason
            .as_deref(),
        Some("TLC smoke harness requires IOEnvExec/CSVWrite side effects.")
    );
}

#[test]
fn test_build_json_report_records_explicit_checker_worker_override() {
    let results = vec![sample_pass_result()];
    let tally = Tally::from_results(&results, 1);
    let report = build_json_report(
        &results,
        &tally,
        1,
        1,
        Path::new("/tmp/tla2"),
        RunConditions {
            cpu_count: 8,
            load_avg_1m: 1.0,
            load_avg_5m: 0.5,
            load_avg_15m: 0.25,
            timeout_floor_seconds: 300,
            timeout_seconds: 300,
            retries: 2,
            checker_policy: "checker_workers",
            checker_workers: Some(4),
        },
    );

    assert_eq!(report.run_conditions.checker_policy, "checker_workers");
    assert_eq!(report.run_conditions.checker_workers, Some(4));
    assert_eq!(report.specs["SmokeEWD998_SC"].status, "pass");
    assert!(
        report.specs["SmokeEWD998_SC"]
            .expected_mismatch_reason
            .is_none(),
        "passing results should not carry an expected mismatch reason"
    );
}
