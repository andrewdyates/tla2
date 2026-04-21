// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::process::Command;

const RESUME_TRACE_DEGRADED_CHILD_ENV: &str = "TLA2_RESUME_TRACE_DEGRADED_CHILD";
const RESUME_TRACE_DEGRADED_CHILD_SENTINEL: &str = "RESUME_TRACE_DEGRADED_CHILD_RAN";

/// Verify that a checkpoint at `path` recorded a first_violation for `expected_invariant`.
fn verify_checkpoint_violation(path: &std::path::Path, expected_invariant: &str) {
    use crate::checkpoint::Checkpoint;
    let cp = Checkpoint::load(path).expect("checkpoint load");
    let (inv, _) = cp
        .first_violation
        .as_ref()
        .expect("checkpoint must persist first_violation from continue_on_error mode");
    assert_eq!(inv, expected_invariant);
}

/// Regression test for #1797: check_with_resume must evaluate ASSUME statements.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_rejects_false_assume() {
    use tempfile::tempdir;

    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
ASSUME FALSE
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );
    let config = init_next_config(&[]);

    // Normal check should fail with AssumeFalse
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        match checker.check() {
            CheckResult::Error { error, .. } => assert!(
                matches!(
                    error,
                    CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. })
                ),
                "Expected AssumeFalse, got {:?}",
                error
            ),
            other => panic!("Expected Error(AssumeFalse), got {:?}", other),
        }
    }

    // Create checkpoint from a spec WITHOUT ASSUME FALSE
    let valid_module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );
    let valid_config = init_next_config(&[]);
    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    save_checkpoint_stopping_at(&valid_module, &valid_config, &checkpoint_path, 1);

    // Resume with ASSUME FALSE spec — must still fail
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("Resume I/O should succeed");
    match result {
        CheckResult::Error { error, .. } => assert!(
            matches!(
                error,
                CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. })
            ),
            "#1797: Resumed check should return AssumeFalse, got {:?}",
            error
        ),
        other => panic!(
            "#1797: Expected Error(AssumeFalse) on resume, got {:?}",
            other
        ),
    }
}

/// Regression test for #1811: continue_on_error violation must survive checkpoint/resume.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_preserves_continue_on_error_violation() {
    use tempfile::tempdir;

    // 5-state ring: invariant fails at x=1
    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 5
Safe == x /= 1
====
"#,
    );
    let config = init_next_config(&["Safe"]);

    // Baseline: continue_on_error should find the violation
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_continue_on_error(true);
        let result = checker.check();
        assert!(matches!(result, CheckResult::InvariantViolation { .. }));
    }

    // Checkpoint at 3 states (after violation at x=1)
    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_continue_on_error(true);
        checker.set_max_states(3);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
        let result = checker.check();
        assert!(matches!(
            result,
            CheckResult::LimitReached {
                limit_type: LimitType::States,
                ..
            }
        ));
    }

    verify_checkpoint_violation(&checkpoint_path, "Safe");

    // Resume: should find the violation, NOT return Success
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);
    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("Resume I/O should succeed");
    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(
                invariant, "Safe",
                "#1811: should name the failing invariant"
            );
        }
        CheckResult::Success(_) => {
            panic!("#1811: Resume returned Success — first_violation lost across checkpoint");
        }
        other => panic!(
            "#1811: Expected InvariantViolation on resume, got {:?}",
            other
        ),
    }
}

/// Part of #2233: restore_from_checkpoint must reject a checkpoint where a
/// frontier state is missing from the depth map.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restore_checkpoint_missing_frontier_depth_rejected() {
    use crate::checkpoint::Checkpoint;
    use crate::state::State;

    let module = parse_module(
        r#"
---- MODULE DepthCheck ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = init_next_config(&[]);
    let mut checker = ModelChecker::new(&module, &config);

    // Build a checkpoint with a frontier state that has NO depth entry.
    let s0 = State::from_pairs([("x", crate::Value::int(0))]);
    let fp0 = s0.fingerprint();
    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints.push(fp0);
    checkpoint.frontier.push(s0);
    // Deliberately omit depth entry — this is the corruption.

    let result = checker.restore_from_checkpoint(checkpoint);
    assert!(
        result.is_err(),
        "Must reject frontier state with no depth entry"
    );
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("depth metadata is incomplete"),
        "error should describe missing depth metadata, got: {msg}"
    );
}

/// Part of #1793: check_with_resume must return an error when the spec has
/// liveness properties, because liveness checking is not supported on resumed runs.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_resume_rejects_unchecked_liveness_properties() {
    use tempfile::tempdir;

    let module = parse_module(
        r#"
---- MODULE ResumeLiveness ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
EventuallyDone == <>(x = 3)
====
"#,
    );
    let mut config = init_next_config(&[]);
    config.properties = vec!["EventuallyDone".to_string()];
    config.check_deadlock = false;

    // Create checkpoint by hitting states limit in full-state mode
    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_store_states(true);
        checker.set_max_states(2);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
        let _result = checker.check();
    }
    assert!(
        checkpoint_path.exists(),
        "Checkpoint should have been saved"
    );

    // Resume in full-state mode: must return LivenessError, not Success
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("Resume IO should not fail");
    match &result {
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            assert!(
                msg.contains("liveness") || msg.contains("PROPERTY") || msg.contains("temporal"),
                "Error should mention liveness/PROPERTY/temporal, got: {msg}"
            );
            assert!(
                msg.contains("EventuallyDone"),
                "Should list the property, got: {msg}"
            );
        }
        CheckResult::Success(_) => {
            panic!("Resume with liveness properties should NOT return Success (Part of #1793)");
        }
        other => panic!("Expected Error with liveness message, got: {other:?}"),
    }
}

/// Part of #1806: check_with_resume must surface setup_error before replaying
/// any checkpoint work, matching the fresh-run entry point.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_surfaces_setup_error() {
    use tempfile::tempdir;

    let valid_module = parse_module(
        r#"
---- MODULE ValidResume ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );
    let config = init_next_config(&[]);

    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    save_checkpoint_stopping_at(&valid_module, &config, &checkpoint_path, 1);

    let invalid_module = parse_module(
        r#"
---- MODULE InvalidResume ----
EXTENDS Missing
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );

    let mut checker = ModelChecker::new_with_extends(&invalid_module, &[], &config);
    checker.set_deadlock_check(false);

    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should return a CheckResult setup error, not an I/O failure");

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert!(
                    msg.contains("via EXTENDS"),
                    "setup error should preserve missing-module provenance, got: {msg}"
                );
            }
            other => panic!("expected setup error, got {other:?}"),
        },
        other => panic!("expected setup error result on resume, got {other:?}"),
    }
}

/// Part of #1807: check_with_resume must flush suppressed guard-evaluation
/// counts into the returned CheckStats and reset the shared counter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_carries_suppressed_guard_errors() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use tempfile::tempdir;

    crate::guard_error_stats::with_test_lock(|| {
        let module = parse_module(
            r#"
---- MODULE ResumeGuardStats ----
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1
====
"#,
        );
        let config = init_next_config(&[]);

        let checkpoint_dir = tempdir().unwrap();
        let checkpoint_path = checkpoint_dir.path().join("checkpoint");
        save_checkpoint_stopping_at(&module, &config, &checkpoint_path, 1);

        let injected = Arc::new(AtomicBool::new(false));
        let injected_callback = Arc::clone(&injected);

        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_progress_interval(1);
        checker.set_progress_callback(Box::new(move |_| {
            if !injected_callback.swap(true, Ordering::SeqCst) {
                crate::guard_error_stats::record_suppressed_action_level_error();
                crate::guard_error_stats::record_suppressed_action_level_error();
            }
        }));

        let result = checker
            .check_with_resume(&checkpoint_path)
            .expect("resume should succeed");

        let stats = match result {
            CheckResult::Success(stats) => stats,
            other => panic!("expected resumed success result, got {other:?}"),
        };

        assert!(
            injected.load(Ordering::SeqCst),
            "progress callback should have run during resumed exploration"
        );
        assert_eq!(
            stats.suppressed_guard_errors, 2,
            "resume path must carry suppressed guard counts into CheckStats"
        );
        assert_eq!(
            crate::guard_error_stats::take_and_reset(),
            0,
            "resume path must reset the shared suppressed-guard counter"
        );
    });
}

/// Part of #1812: check_with_resume must surface the same terminal degraded-trace
/// warning as fresh runs when trace reconstruction degraded during exploration.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_emits_terminal_trace_degraded_warning_child() {
    use tempfile::tempdir;

    if std::env::var_os(RESUME_TRACE_DEGRADED_CHILD_ENV).is_none() {
        return;
    }

    eprintln!("{RESUME_TRACE_DEGRADED_CHILD_SENTINEL}");

    let module = parse_module(
        r#"
---- MODULE ResumeTraceDegraded ----
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
"#,
    );
    let config = init_next_config(&[]);

    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    save_checkpoint_stopping_at(&module, &config, &checkpoint_path, 1);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_trace_degraded(true);

    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should succeed");
    assert!(
        matches!(result, CheckResult::Success(_)),
        "expected resumed success result, got {result:?}"
    );
}

/// Part of #1812: resume must print the terminal degraded-trace warning on stderr,
/// matching the fresh-run `check()` entry lifecycle.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_emits_terminal_trace_degraded_warning() {
    let exe = std::env::current_exe().expect("current_exe");
    let child_module = module_path!()
        .split_once("::")
        .map_or(module_path!(), |(_, path)| path);
    let child_test =
        format!("{child_module}::test_resume_emits_terminal_trace_degraded_warning_child");
    let output = Command::new(exe)
        .env(RESUME_TRACE_DEGRADED_CHILD_ENV, "1")
        .arg("--exact")
        .arg(&child_test)
        .arg("--nocapture")
        .output()
        .expect("failed to spawn child process");

    assert!(
        output.status.success(),
        "child process failed (status={:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(RESUME_TRACE_DEGRADED_CHILD_SENTINEL),
        "child process succeeded but did not run the expected child test.\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains(
            "WARNING: Counterexample trace may be incomplete due to I/O errors during model checking."
        ),
        "resume must print the terminal degraded-trace warning.\nstderr:\n{stderr}"
    );
}
