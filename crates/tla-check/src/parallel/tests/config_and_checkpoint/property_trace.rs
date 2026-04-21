// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Saved property-trace fast path and resume tests.

use super::*;
use std::process::Command;

const RESUME_PROPERTY_TRACE_CHILD_ENV: &str = "TLA2_PARALLEL_RESUME_PROPERTY_TRACE_CHILD";
const RESUME_PROPERTY_TRACE_CHILD_SENTINEL: &str = "PARALLEL_RESUME_PROPERTY_TRACE_CHILD_RAN";

/// Part of #3111: Resume must preserve PROPERTY attribution for saved
/// continue-on-error state-level violations instead of downgrading them to
/// plain invariant violations on the fast path.
fn run_parallel_resume_preserves_property_violation_fixture() {
    let src = r#"
---- MODULE BadProperty ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == [](x < 2)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Small".to_string()],
        ..Default::default()
    };

    let tmpdir = tempfile::tempdir().unwrap();

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);
    checker.set_store_states(true);
    checker.set_max_states(10);
    checker.set_checkpoint(tmpdir.path().join("ckpt"), Duration::from_secs(3600));

    let result = checker.check();
    match &result {
        CheckResult::PropertyViolation { property, kind, .. } => {
            assert_eq!(property, "Small");
            assert_eq!(*kind, crate::check::PropertyViolationKind::StateLevel);
        }
        other => panic!("Expected PropertyViolation, got: {other:?}"),
    }
    assert!(
        checker
            .first_violation_trace
            .get()
            .is_some_and(|trace| !trace.is_empty()),
        "checker should cache the finalized violation trace before checkpoint creation"
    );

    let checkpoint = checker.create_checkpoint().unwrap();
    assert!(
        checkpoint.first_violation.is_some(),
        "checkpoint should preserve first_violation"
    );
    let (property_name, _fp) = checkpoint.first_violation.as_ref().unwrap();
    assert_eq!(property_name, "Small");

    // Part of #3112: Verify violation trace is captured in checkpoint.
    assert!(
        !checkpoint.first_violation_trace.is_empty(),
        "checkpoint should preserve violation trace states when store_full_states is true"
    );
    let ckpt_dir = tmpdir.path().join("ckpt_saved");
    checkpoint.save(&ckpt_dir).unwrap();

    let mut checker2 = ParallelChecker::new(&module, &config, 1);
    checker2.set_deadlock_check(false);
    checker2.set_store_states(true);
    let resume_result = checker2
        .check_with_resume(&ckpt_dir)
        .expect("resume IO should succeed");

    match resume_result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "Small", "resumed property should match");
            assert_eq!(kind, crate::check::PropertyViolationKind::StateLevel);
            // Part of #3112: Verify trace is non-empty on resume.
            assert!(
                !trace.is_empty(),
                "resumed PropertyViolation should include non-empty trace"
            );
        }
        other => panic!("Expected PropertyViolation from resume, got: {other:?}"),
    }
}

/// Part of #3709/#3710: resume-time state-property attribution must classify
/// mixed on-the-fly PROPERTY entries the same way as full liveness mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_classifies_on_the_fly_mixed_state_property_names() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE BadMixedProperty ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Mixed == [](x < 2) /\ <>(x = 5)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Mixed".to_string()],
        liveness_execution: crate::config::LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };
    let checker = ParallelChecker::new(&module, &config, 1);

    let names = checker
        .state_property_violation_names_for_resume()
        .expect("on-the-fly mixed property classification should succeed");
    assert_eq!(names, vec!["Mixed".to_string()]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_preserves_property_violation() {
    let _serial = super::super::acquire_interner_lock();
    run_parallel_resume_preserves_property_violation_fixture();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_preserves_property_violation_without_missing_trace_warning_child() {
    let _serial = super::super::acquire_interner_lock();
    if std::env::var_os(RESUME_PROPERTY_TRACE_CHILD_ENV).is_none() {
        return;
    }

    eprintln!("{RESUME_PROPERTY_TRACE_CHILD_SENTINEL}");
    run_parallel_resume_preserves_property_violation_fixture();
}

/// Part of #3112: Resume should use the saved violation trace directly and avoid
/// emitting the missing-fingerprint warning from `reconstruct_trace`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_preserves_property_violation_without_missing_trace_warning() {
    let _serial = super::super::acquire_interner_lock();
    let exe = std::env::current_exe().expect("current_exe");
    let child_module = module_path!()
        .split_once("::")
        .map_or(module_path!(), |(_, path)| path);
    let child_test = format!(
        "{child_module}::test_parallel_resume_preserves_property_violation_without_missing_trace_warning_child"
    );
    let output = Command::new(exe)
        .env(RESUME_PROPERTY_TRACE_CHILD_ENV, "1")
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
        stderr.contains(RESUME_PROPERTY_TRACE_CHILD_SENTINEL),
        "child process succeeded but did not run the expected child test.\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("Warning: reconstruct_trace:"),
        "resume must not emit the incomplete-trace warning when a saved violation trace exists.\nstderr:\n{stderr}"
    );
}
