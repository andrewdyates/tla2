// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::classify::*;
use super::subprocess::is_signal_killed;
use crate::cmd_diagnose::types::{
    Baseline, BaselineSource, BaselineSpec, BaselineTla2, BaselineTlc, SpecVerdict,
};
#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
#[cfg(windows)]
use std::os::windows::process::ExitStatusExt;

fn make_spec(
    tlc_status: &str,
    tlc_states: Option<u64>,
    tlc_error_type: Option<&str>,
) -> BaselineSpec {
    BaselineSpec {
        tlc: BaselineTlc {
            status: tlc_status.to_string(),
            states: tlc_states,
            error_type: tlc_error_type.map(|s| s.to_string()),
        },
        tla2: BaselineTla2 {
            status: "unknown".to_string(),
            states: None,
            error_type: None,
            last_run: None,
            git_commit: None,
        },
        verified_match: false,
        category: "small".to_string(),
        source: None,
        expected_mismatch: false,
        expected_mismatch_reason: None,
        tla2_expected_states: None,
        diagnose_timeout_seconds: None,
        continue_on_error: true,
    }
}

fn make_simulation_spec(
    tlc_status: &str,
    tlc_states: Option<u64>,
    tlc_error_type: Option<&str>,
) -> BaselineSpec {
    let mut spec = make_spec(tlc_status, tlc_states, tlc_error_type);
    spec.source = Some(BaselineSource {
        tla_path: "spec.tla".to_string(),
        cfg_path: "spec.cfg".to_string(),
        mode: Some("simulate".to_string()),
    });
    spec
}

fn make_json_output(stdout: &str) -> std::process::Output {
    std::process::Output {
        status: std::process::ExitStatus::from_raw(0),
        stdout: stdout.as_bytes().to_vec(),
        stderr: Vec::new(),
    }
}

#[test]
fn test_classify_both_success_state_match() {
    let spec = make_spec("pass", Some(100), None);
    let v = classify_raw(Some("ok"), Some(100), &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_both_success_state_mismatch() {
    let spec = make_spec("pass", Some(100), None);
    let v = classify_raw(Some("ok"), Some(200), &None, &spec);
    assert_eq!(v, SpecVerdict::StateMismatch);
}

#[test]
fn test_classify_simulation_success_ignores_state_counts() {
    let spec = make_simulation_spec("pass", Some(0), None);
    let v = classify_raw(Some("ok"), None, &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_false_negative() {
    // TLA2 ok but TLC found an error
    let spec = make_spec("error", Some(50), Some("invariant"));
    let v = classify_raw(Some("ok"), Some(50), &None, &spec);
    assert_eq!(v, SpecVerdict::FalseNegative);
}

#[test]
fn test_classify_false_positive() {
    // TLA2 error but TLC found no error
    let spec = make_spec("pass", Some(100), None);
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::FalsePositive);
}

#[test]
fn test_classify_both_error_same() {
    // Both error, same error type and states
    let spec = make_spec("error", Some(50), Some("invariant"));
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_both_error_same_type_different_states() {
    // Part of #3305: same error type but different state counts → still Pass.
    // Einstein streaming scan reports 0 states (no storage), TLC reports null.
    let spec = make_spec("pass", None, Some("invariant"));
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(0), &err, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_both_error_different() {
    // Both error, different error type
    let spec = make_spec("error", Some(50), Some("deadlock"));
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::BothFail);
}

#[test]
fn test_classify_tlc_pass_with_error_type() {
    // TLC status="pass" but error_type="invariant" means TLC found an expected error.
    // TLA2 also finds the error → Pass.
    let spec = make_spec("pass", Some(50), Some("invariant"));
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_tlc_pass_with_error_type_tla2_ok() {
    // TLC status="pass" + error_type="invariant" → TLC expected an error.
    // TLA2 says ok → FalseNegative.
    let spec = make_spec("pass", Some(50), Some("invariant"));
    let v = classify_raw(Some("ok"), Some(50), &None, &spec);
    assert_eq!(v, SpecVerdict::FalseNegative);
}

#[test]
fn test_classify_tla2_status_none_tlc_no_error() {
    // tla2_status=None (crash/unparseable) + TLC no error → FalsePositive
    let spec = make_spec("pass", Some(100), None);
    let v = classify_raw(None, None, &None, &spec);
    assert_eq!(v, SpecVerdict::FalsePositive);
}

#[test]
fn test_classify_tla2_status_none_tlc_has_error() {
    // tla2_status=None (crash) + TLC has error → BothFail (error types can't match)
    let spec = make_spec("error", Some(50), Some("invariant"));
    let v = classify_raw(None, None, &None, &spec);
    assert_eq!(v, SpecVerdict::BothFail);
}

#[test]
fn test_classify_tla2_ok_tlc_timeout() {
    // TLA2 succeeds but TLC timed out → we can't compare, treat as Pass
    let spec = make_spec("timeout", None, None);
    let v = classify_raw(Some("ok"), Some(100), &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_tla2_ok_tlc_timeout_with_error_type() {
    // Part of #3733: bcastFolklore-like specs have tlc.status="timeout" AND
    // tlc.error_type="timeout". The error_type caused tlc_has_real_error_type()
    // to return true, making the FalseNegative branch fire before the timeout
    // check. The timeout early return must fire first.
    let spec = make_spec("timeout", None, Some("timeout"));
    let v = classify_raw(Some("ok"), Some(100), &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_tla2_error_tlc_timeout() {
    // TLA2 errors but TLC timed out → BothFail (can't confirm either way)
    let spec = make_spec("timeout", None, None);
    let err = Some("invariant_violation".to_string());
    let v = classify_raw(Some("error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::BothFail);
}

#[test]
fn test_classify_fallback_crash() {
    // Unrecognized TLC status with tla2_ok → falls through to Crash
    let spec = make_spec("weird_status", None, None);
    let v = classify_raw(Some("ok"), Some(100), &None, &spec);
    assert_eq!(v, SpecVerdict::Crash);
}

#[test]
fn test_apply_expected_mismatch_maps_false_negative() {
    let mut spec = make_spec("error", None, Some("unknown"));
    spec.expected_mismatch = true;
    spec.expected_mismatch_reason =
        Some("simulation baseline is intentionally incomparable".to_string());
    let raw = classify_raw(Some("ok"), None, &None, &spec);
    assert_eq!(raw, SpecVerdict::FalseNegative);
    assert_eq!(
        apply_expected_mismatch(raw, &spec),
        SpecVerdict::ExpectedMismatch
    );
}

#[test]
fn test_apply_expected_mismatch_maps_state_mismatch() {
    let mut spec = make_spec("pass", Some(100), None);
    spec.expected_mismatch = true;
    let raw = classify_raw(Some("ok"), Some(200), &None, &spec);
    assert_eq!(raw, SpecVerdict::StateMismatch);
    assert_eq!(
        apply_expected_mismatch(raw, &spec),
        SpecVerdict::ExpectedMismatch
    );
}

#[test]
fn test_apply_expected_mismatch_leaves_timeout_unchanged() {
    // Part of #3742: Timeout + expected_mismatch=true now correctly converts
    // to ExpectedMismatch (intractable specs where TLC also times out).
    let mut spec = make_spec("pass", Some(100), None);
    spec.expected_mismatch = true;
    assert_eq!(
        apply_expected_mismatch(SpecVerdict::Timeout, &spec),
        SpecVerdict::ExpectedMismatch
    );
}

#[test]
fn test_apply_expected_mismatch_leaves_exact_pass_unchanged() {
    let spec = make_spec("pass", Some(100), None);
    let raw = classify_raw(Some("ok"), Some(100), &None, &spec);
    assert_eq!(raw, SpecVerdict::Pass);
    assert_eq!(apply_expected_mismatch(raw, &spec), SpecVerdict::Pass);
}

#[test]
fn test_smokeewd998_sc_baseline_entry_classifies_as_pass() {
    let baseline_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/tlc_comparison/spec_baseline.json");
    let baseline_text =
        std::fs::read_to_string(&baseline_path).expect("should read spec baseline JSON");
    let baseline: Baseline =
        serde_json::from_str(&baseline_text).expect("baseline JSON should deserialize");
    let spec = baseline
        .specs
        .get("SmokeEWD998_SC")
        .expect("SmokeEWD998_SC baseline entry should exist");

    assert!(
        !spec.expected_mismatch,
        "SmokeEWD998_SC should no longer be marked as expected_mismatch"
    );
    assert_eq!(
        spec.tlc.status, "pass",
        "SmokeEWD998_SC TLC baseline should record the verified pass result"
    );
    assert_eq!(
        spec.tla2.status, "pass",
        "SmokeEWD998_SC TLA2 baseline should record the verified pass result"
    );

    let raw = classify_raw(Some("ok"), Some(0), &None, spec);
    assert_eq!(
        raw,
        SpecVerdict::Pass,
        "raw classification should reflect the exact TLC/TLA2 parity"
    );
    assert_eq!(apply_expected_mismatch(raw, spec), SpecVerdict::Pass);
    assert!(
        spec.expected_mismatch_reason.is_none(),
        "SmokeEWD998_SC should not carry an expected mismatch reason after #3311"
    );
}

#[test]
fn test_invariant_specs_get_effective_first_error_mode() {
    let baseline_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/tlc_comparison/spec_baseline.json");
    let baseline_text =
        std::fs::read_to_string(&baseline_path).expect("should read spec baseline JSON");
    let baseline: Baseline =
        serde_json::from_str(&baseline_text).expect("baseline JSON should deserialize");

    // All specs with TLC error_type "invariant" or "assume_violation"
    // should get effective_continue_on_error() == false, regardless of
    // whether the per-spec override is set in the baseline JSON.
    let effective_first_error: Vec<&str> = baseline
        .specs
        .iter()
        .filter_map(|(name, spec)| (!spec.effective_continue_on_error()).then_some(name.as_str()))
        .collect();

    // Every invariant/assume_violation spec must be in first-error mode.
    let invariant_specs: Vec<&str> = baseline
        .specs
        .iter()
        .filter_map(|(name, spec)| {
            matches!(
                spec.tlc.error_type.as_deref(),
                Some("invariant" | "assume_violation")
            )
            .then_some(name.as_str())
        })
        .collect();

    for spec_name in &invariant_specs {
        assert!(
            effective_first_error.contains(spec_name),
            "{spec_name} has TLC error_type invariant/assume_violation but \
             effective_continue_on_error() returned true"
        );
    }

    // Verify MCCheckpointCoordinationFailure is now covered (Part of #833).
    let checkpoint = baseline
        .specs
        .get("MCCheckpointCoordinationFailure")
        .expect("MCCheckpointCoordinationFailure baseline entry should exist");
    assert_eq!(
        checkpoint.tlc.error_type.as_deref(),
        Some("invariant"),
        "TLC baseline should record an invariant violation"
    );
    assert!(
        !checkpoint.effective_continue_on_error(),
        "MCCheckpointCoordinationFailure should get first-error mode from TLC error_type"
    );

    // Verify explicit overrides still work (SlidingPuzzles, sunder).
    let sliding = baseline
        .specs
        .get("SlidingPuzzles")
        .expect("SlidingPuzzles baseline entry should exist");
    assert!(!sliding.continue_on_error, "explicit override preserved");
    assert!(!sliding.effective_continue_on_error());
}

#[test]
fn test_error_types_match_normalized() {
    let t2 = Some("invariant_violation".to_string());
    let tlc = Some("invariant".to_string());
    assert!(error_types_match(&t2, &tlc));
}

#[test]
fn test_error_types_match_liveness() {
    let t2 = Some("liveness_violation".to_string());
    let tlc = Some("liveness".to_string());
    assert!(error_types_match(&t2, &tlc));
}

#[test]
fn test_error_types_no_match() {
    let t2 = Some("invariant_violation".to_string());
    let tlc = Some("deadlock".to_string());
    assert!(!error_types_match(&t2, &tlc));
}

#[test]
fn test_normalize_error_type_passthrough() {
    assert_eq!(normalize_error_type("deadlock"), "deadlock");
    assert_eq!(normalize_error_type("custom_thing"), "custom_thing");
}

#[test]
fn test_normalize_error_type_known() {
    assert_eq!(normalize_error_type("invariant_violation"), "invariant");
    assert_eq!(normalize_error_type("property_violation"), "property");
    assert_eq!(normalize_error_type("liveness_violation"), "liveness");
}

// Part of #2927: signal-killed process detection tests.

#[cfg(unix)]
#[test]
fn test_is_signal_killed_sigkill() {
    use std::process::Command;
    // Spawn a process that kills itself with SIGKILL.
    let output = Command::new("sh")
        .args(["-c", "kill -9 $$"])
        .output()
        .expect("failed to spawn sh");
    assert!(
        is_signal_killed(&output.status),
        "SIGKILL exit should be detected as signal-killed"
    );
}

#[cfg(unix)]
#[test]
fn test_is_signal_killed_sigterm() {
    use std::process::Command;
    // Spawn a process that kills itself with SIGTERM.
    let output = Command::new("sh")
        .args(["-c", "kill -15 $$"])
        .output()
        .expect("failed to spawn sh");
    assert!(
        is_signal_killed(&output.status),
        "SIGTERM exit should be detected as signal-killed"
    );
}

#[cfg(unix)]
#[test]
fn test_is_signal_killed_normal_exit_not_detected() {
    use std::process::Command;
    // Normal exit code 1 should NOT be signal-killed.
    let output = Command::new("sh")
        .args(["-c", "exit 1"])
        .output()
        .expect("failed to spawn sh");
    assert!(
        !is_signal_killed(&output.status),
        "Normal exit(1) should not be detected as signal-killed"
    );
}

#[cfg(unix)]
#[test]
fn test_is_signal_killed_success_not_detected() {
    use std::process::Command;
    let output = Command::new("true").output().expect("failed to spawn true");
    assert!(
        !is_signal_killed(&output.status),
        "Successful exit should not be detected as signal-killed"
    );
}

#[test]
fn test_oom_killed_verdict_label() {
    assert_eq!(SpecVerdict::OomKilled.label(), "oom_killed");
}

#[test]
fn test_classify_tla2_expected_states_overrides_tlc_states() {
    // SpanTreeRandom: TLC has 87898 states, TLA2 has 27242 (PRNG difference).
    // With tla2_expected_states = 27242, classify should compare against that.
    let mut spec = make_spec("pass", Some(87898), None);
    spec.tla2_expected_states = Some(27242);
    let v = classify_raw(Some("ok"), Some(27242), &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_tla2_expected_states_mismatch() {
    // If TLA2 produces wrong count even against tla2_expected_states, still mismatch.
    let mut spec = make_spec("pass", Some(87898), None);
    spec.tla2_expected_states = Some(27242);
    let v = classify_raw(Some("ok"), Some(99999), &None, &spec);
    assert_eq!(v, SpecVerdict::StateMismatch);
}

#[test]
fn test_classify_simulation_ok_tlc_error_is_pass() {
    // SimTokenRing: TLC baseline is "error" (from BFS mode failing ASSUME).
    // TLA2 succeeds in simulate mode → should be Pass, not FalseNegative.
    let spec = make_simulation_spec("error", None, Some("unknown"));
    let v = classify_raw(Some("ok"), None, &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_non_simulation_ok_tlc_error_is_false_negative() {
    // Non-simulation spec: TLA2 ok + TLC error → FalseNegative (unchanged).
    let spec = make_spec("error", Some(50), Some("invariant"));
    let v = classify_raw(Some("ok"), Some(50), &None, &spec);
    assert_eq!(v, SpecVerdict::FalseNegative);
}

#[test]
fn test_parse_and_classify_downgrades_liveness_checker_setup_failure() {
    let spec = make_spec("pass", Some(42), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: Failed to create liveness checker for temporal formula <>~A"
            },
            "statistics": {
                "states_found": 42
            }
        }"#,
    );

    let result = parse_and_classify("TemporalSpec", &spec, &output, 1.25);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
    assert_eq!(result.tla2_states, Some(42));
    assert_eq!(result.error_details, None);
}

#[test]
fn test_parse_and_classify_downgrades_fingerprint_only_replay_failure() {
    let spec = make_spec("pass", Some(9), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: fingerprint-only parallel liveness could not replay state 123"
            },
            "statistics": {
                "states_found": 9
            }
        }"#,
    );

    let result = parse_and_classify("ReplaySpec", &spec, &output, 0.5);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
    assert_eq!(result.tla2_states, Some(9));
    assert_eq!(result.error_details, None);
}

#[test]
fn test_parse_and_classify_keeps_non_liveness_runtime_error() {
    // Non-liveness runtime_error with state count mismatch → FalsePositive.
    // Use different state counts (TLC=100, TLA2=9) so the state-count-aware
    // pass-through (#3746) does not apply.
    let spec = make_spec("pass", Some(100), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Failed to deserialize checkpoint"
            },
            "statistics": {
                "states_found": 9
            }
        }"#,
    );

    let result = parse_and_classify("CheckpointSpec", &spec, &output, 0.5);

    assert_eq!(result.verdict, SpecVerdict::FalsePositive);
    assert_eq!(result.tla2_status.as_deref(), Some("runtime_error"));
    assert_eq!(result.tla2_states, Some(9));
    assert_eq!(result.error_details.as_deref(), Some("runtime_error"));
}

#[test]
fn test_parse_and_classify_downgrades_runtime_error_when_state_counts_match() {
    // Part of #3746: parallel liveness crash produces runtime_error, but BFS
    // state count matches TLC exactly → should downgrade to pass (BFS correct).
    let spec = make_spec("pass", Some(214), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Evaluation error: Internal error: populate_node_check_masks: missing batched ENABLED successor array state for fp abc123"
            },
            "statistics": {
                "states_found": 214
            }
        }"#,
    );

    let result = parse_and_classify("LivenessSpec", &spec, &output, 1.0);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
    assert_eq!(result.tla2_states, Some(214));
    assert_eq!(result.error_details, None);
}

#[test]
fn test_parse_and_classify_keeps_runtime_error_when_state_counts_differ() {
    // Part of #3746: runtime_error with state count mismatch should NOT
    // be downgraded — the error might be real.
    let spec = make_spec("pass", Some(100), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Evaluation error: Internal error: populate_node_check_masks: missing batched ENABLED successor array state for fp abc123"
            },
            "statistics": {
                "states_found": 50
            }
        }"#,
    );

    let result = parse_and_classify("LivenessSpec", &spec, &output, 1.0);

    assert_eq!(result.verdict, SpecVerdict::FalsePositive);
    assert_eq!(result.tla2_status.as_deref(), Some("runtime_error"));
}

#[test]
fn test_classify_tlc_timeout_error_type_excluded_from_real_errors() {
    // Defense-in-depth for #3733: even if the early-return for tlc.status=="timeout"
    // were removed, tlc_has_real_error_type() should NOT treat error_type="timeout"
    // as a real error. This test uses status="pass" with error_type="timeout" — a
    // hypothetical baseline entry — to verify the exclusion in tlc_has_real_error_type.
    let spec = make_spec("pass", Some(100), Some("timeout"));
    let v = classify_raw(Some("ok"), Some(100), &None, &spec);
    // With "timeout" excluded from real error types, tlc_no_error=true, so this
    // should be Pass (state counts match), not FalseNegative.
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_simulation_ok_tlc_pass_is_pass() {
    // Part of #3448: EWD998ChanID_export-like specs — TLC baseline is "pass" (no
    // error), TLA2 runs with --no-invariants so it also succeeds. Simulation
    // short-circuit at classify_raw line 332-334 should return Pass without
    // comparing state counts (which are unavailable in simulation mode).
    let spec = make_simulation_spec("pass", None, None);
    let v = classify_raw(Some("ok"), None, &None, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

// Part of #3746: state-count-aware classification for liveness infra errors.

#[test]
fn test_classify_runtime_error_exact_state_match_is_pass() {
    // When BFS completed with exact TLC state count match, a runtime_error
    // (from liveness infra crash) should classify as Pass, not FalsePositive.
    let spec = make_spec("pass", Some(100), None);
    let err = Some("runtime_error".to_string());
    let v = classify_raw(Some("runtime_error"), Some(100), &err, &spec);
    assert_eq!(v, SpecVerdict::Pass);
}

#[test]
fn test_classify_runtime_error_state_mismatch_is_false_positive() {
    // If states don't match TLC, it's still FalsePositive — the BFS may
    // not have completed correctly.
    let spec = make_spec("pass", Some(100), None);
    let err = Some("runtime_error".to_string());
    let v = classify_raw(Some("runtime_error"), Some(50), &err, &spec);
    assert_eq!(v, SpecVerdict::FalsePositive);
}

#[test]
fn test_classify_runtime_error_no_states_is_false_positive() {
    // No state count data → can't confirm BFS completed → FalsePositive.
    let spec = make_spec("pass", Some(100), None);
    let err = Some("runtime_error".to_string());
    let v = classify_raw(Some("runtime_error"), None, &err, &spec);
    assert_eq!(v, SpecVerdict::FalsePositive);
}

// Part of #3746: expanded liveness infra error prefix tests.

#[test]
fn test_parse_and_classify_downgrades_liveness_successor_fingerprint_failure() {
    let spec = make_spec("pass", Some(20), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: Failed to derive liveness successor fingerprints for state 0x1234"
            },
            "statistics": {
                "states_found": 20
            }
        }"#,
    );

    let result = parse_and_classify("SuccFP", &spec, &output, 0.3);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
}

#[test]
fn test_parse_and_classify_downgrades_on_the_fly_liveness_failure() {
    let spec = make_spec("pass", Some(15), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: On-the-fly liveness runtime failure in SCC analysis"
            },
            "statistics": {
                "states_found": 15
            }
        }"#,
    );

    let result = parse_and_classify("OnTheFly", &spec, &output, 0.2);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
}

#[test]
fn test_parse_and_classify_downgrades_missing_state_for_fingerprint() {
    let spec = make_spec("pass", Some(8), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: missing state for fingerprint 0xABCD in liveness graph"
            },
            "statistics": {
                "states_found": 8
            }
        }"#,
    );

    let result = parse_and_classify("MissingFP", &spec, &output, 0.1);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
}

#[test]
fn test_parse_and_classify_downgrades_checkpoint_resume_liveness() {
    let spec = make_spec("pass", Some(50), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness error: Checkpoint resume does not yet support PROPERTY/liveness checking"
            },
            "statistics": {
                "states_found": 50
            }
        }"#,
    );

    let result = parse_and_classify("CkptLiveness", &spec, &output, 0.4);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
}

#[test]
fn test_parse_and_classify_downgrades_parallel_liveness_counterexample() {
    let spec = make_spec("pass", Some(30), None);
    let output = make_json_output(
        r#"{
            "result": {
                "status": "runtime_error",
                "error_type": "runtime_error",
                "error_message": "Liveness failure: parallel liveness checker unexpectedly returned fingerprint-only counterexample data"
            },
            "statistics": {
                "states_found": 30
            }
        }"#,
    );

    let result = parse_and_classify("ParLiveness", &spec, &output, 0.3);

    assert_eq!(result.verdict, SpecVerdict::Pass);
    assert_eq!(result.tla2_status.as_deref(), Some("ok"));
}

// Part of #3742: expected_mismatch now covers OomKilled and Timeout verdicts.

#[test]
fn test_apply_expected_mismatch_maps_oom_killed() {
    // CarTalkPuzzle_M3-like: intractable spec, TLC also timed out.
    // OomKilled + expected_mismatch=true -> ExpectedMismatch.
    let mut spec = make_spec("timeout", None, Some("timeout"));
    spec.expected_mismatch = true;
    spec.expected_mismatch_reason =
        Some("Intractable spec; both TLC and TLA2 timeout/OOM".to_string());
    assert_eq!(
        apply_expected_mismatch(SpecVerdict::OomKilled, &spec),
        SpecVerdict::ExpectedMismatch
    );
}

#[test]
fn test_apply_expected_mismatch_maps_timeout() {
    // SpanTreeTest5Nodes-like: exponential state space, TLC timed out too.
    // Timeout + expected_mismatch=true -> ExpectedMismatch.
    let mut spec = make_spec("timeout", None, None);
    spec.expected_mismatch = true;
    spec.expected_mismatch_reason = Some("Exponential state space; TLC times out too".to_string());
    assert_eq!(
        apply_expected_mismatch(SpecVerdict::Timeout, &spec),
        SpecVerdict::ExpectedMismatch
    );
}

#[cfg(unix)]
#[test]
fn test_parse_and_classify_signal_kill_maps_to_expected_mismatch() {
    use std::process::Command;

    let mut spec = make_spec("timeout", Some(0), None);
    spec.expected_mismatch = true;
    spec.expected_mismatch_reason =
        Some("Exponential state space; TLC could not complete".to_string());

    let output = Command::new("sh")
        .args(["-c", "kill -9 $$"])
        .output()
        .expect("failed to spawn sh");

    let result = parse_and_classify("SpanTreeTest5Nodes", &spec, &output, 0.2);

    assert_eq!(result.verdict, SpecVerdict::ExpectedMismatch);
    assert_eq!(
        result.expected_mismatch_reason.as_deref(),
        Some("Exponential state space; TLC could not complete")
    );
}

#[test]
fn test_timeout_result_maps_to_expected_mismatch() {
    let mut spec = make_spec("timeout", Some(0), None);
    spec.expected_mismatch = true;
    spec.expected_mismatch_reason =
        Some("Exponential state space; TLC could not complete".to_string());

    let result = timeout_result(
        "SpanTreeTest5Nodes",
        &spec,
        std::time::Duration::from_secs(30),
        30.0,
    );

    assert_eq!(result.verdict, SpecVerdict::ExpectedMismatch);
    assert_eq!(result.tla2_status.as_deref(), Some("timeout"));
    assert_eq!(
        result.expected_mismatch_reason.as_deref(),
        Some("Exponential state space; TLC could not complete")
    );
}

#[test]
fn test_apply_expected_mismatch_oom_without_flag_unchanged() {
    // Without expected_mismatch=true, OomKilled stays OomKilled.
    let spec = make_spec("pass", Some(100), None);
    assert_eq!(
        apply_expected_mismatch(SpecVerdict::OomKilled, &spec),
        SpecVerdict::OomKilled
    );
}

#[test]
fn test_apply_expected_mismatch_timeout_without_flag_unchanged() {
    // Without expected_mismatch=true, Timeout stays Timeout.
    let spec = make_spec("pass", Some(100), None);
    assert_eq!(
        apply_expected_mismatch(SpecVerdict::Timeout, &spec),
        SpecVerdict::Timeout
    );
}
