// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checkpoint save/load round-trip and resume tests.

use super::*;

/// Helper: run Counter spec to completion and save a checkpoint.
/// Returns (tmpdir, ckpt_dir_path, checker_after_check).
fn checkpoint_counter_spec() -> (std::path::PathBuf, std::path::PathBuf, ParallelChecker) {
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
TypeOK == x \in 0..5
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let tmpdir = std::env::temp_dir().join("tla2_test_parallel_ckpt_roundtrip");
    let _ = std::fs::remove_dir_all(&tmpdir);
    std::fs::create_dir_all(&tmpdir).unwrap();

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_checkpoint(tmpdir.join("ckpt"), Duration::from_secs(3600));
    checker.set_checkpoint_paths(Some("Counter.tla".into()), Some("Counter.cfg".into()));

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => assert_eq!(stats.states_found, 6),
        other => panic!("Expected Success, got: {other:?}"),
    }

    let checkpoint = checker
        .create_checkpoint()
        .expect("checkpoint should succeed");
    let ckpt_dir = tmpdir.join("ckpt_saved");
    checkpoint.save(&ckpt_dir).expect("save should succeed");

    (tmpdir, ckpt_dir, checker)
}

/// Part of #2749: Parallel checkpoint save/load round-trip.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_checkpoint_save_load_roundtrip() {
    let _serial = super::super::acquire_interner_lock();
    let (tmpdir, ckpt_dir, checker) = checkpoint_counter_spec();

    // Verify saved checkpoint data.
    assert_eq!(checker.depths.len(), 6);

    // Resume from checkpoint with a fresh checker.
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
TypeOK == x \in 0..5
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    let mut checker2 = ParallelChecker::new(&module, &config, 2);
    checker2.set_deadlock_check(false);
    checker2.set_store_states(false);
    checker2.set_checkpoint_paths(Some("Counter.tla".into()), Some("Counter.cfg".into()));

    let resume_result = checker2
        .check_with_resume(&ckpt_dir)
        .expect("resume should succeed");

    match resume_result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 6, "resumed states_found");
            assert_eq!(stats.max_depth, 5, "resumed max_depth");
        }
        other => panic!("Expected Success from resume, got: {other:?}"),
    }
    // Use states_count() so this assertion stays valid regardless of the chosen
    // state-storage backend.
    assert_eq!(checker2.states_count(), 6, "states after resume");
    // Part of #3233: this resume run re-explores without checkpointing and has
    // no liveness properties, so both init-state and successor depth writes are skipped.
    assert!(
        checker2.depths.is_empty(),
        "depths after non-checkpoint resume should stay empty"
    );

    let _ = std::fs::remove_dir_all(&tmpdir);
}

/// Part of #2749: Resume rejects mismatched checkpoint spec path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_rejects_path_mismatch() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE Tiny ----
VARIABLE x
Init == x = 0
Next == x' = 1 - x
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let tmpdir = std::env::temp_dir().join("tla2_test_parallel_ckpt_mismatch");
    let _ = std::fs::remove_dir_all(&tmpdir);
    std::fs::create_dir_all(&tmpdir).unwrap();

    // Run and checkpoint.
    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);
    checker.set_checkpoint(tmpdir.join("ckpt"), Duration::from_secs(3600));
    checker.set_checkpoint_paths(Some("Tiny.tla".into()), None);

    let result = checker.check();
    assert!(matches!(result, CheckResult::Success(_)));

    let checkpoint = checker.create_checkpoint().unwrap();
    let ckpt_dir = tmpdir.join("ckpt_saved");
    checkpoint.save(&ckpt_dir).unwrap();

    // Resume with different spec path — should fail.
    let mut checker2 = ParallelChecker::new(&module, &config, 1);
    checker2.set_deadlock_check(false);
    checker2.set_checkpoint_paths(Some("Other.tla".into()), None);

    let resume_err = checker2.check_with_resume(&ckpt_dir);
    assert!(resume_err.is_err(), "resume should fail on path mismatch");
    let err_msg = resume_err.unwrap_err().to_string();
    assert!(
        err_msg.contains("mismatch"),
        "error should mention path mismatch: {err_msg}"
    );

    let _ = std::fs::remove_dir_all(&tmpdir);
}

/// Part of #2749: Resume restores first_violation from continue-on-error mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_preserves_violation() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE Bad ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == x < 2
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Small".to_string()],
        ..Default::default()
    };

    let tmpdir = std::env::temp_dir().join("tla2_test_parallel_ckpt_violation");
    let _ = std::fs::remove_dir_all(&tmpdir);
    std::fs::create_dir_all(&tmpdir).unwrap();

    // Run with continue_on_error to capture violation without stopping.
    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);
    checker.set_max_states(10);
    checker.set_checkpoint(tmpdir.join("ckpt"), Duration::from_secs(3600));

    let result = checker.check();
    // Continue-on-error: should report violation after exploring states.
    match &result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "Small");
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    }

    // Create and save checkpoint — should have first_violation set.
    let checkpoint = checker.create_checkpoint().unwrap();
    assert!(
        checkpoint.first_violation.is_some(),
        "checkpoint should preserve first_violation"
    );
    let (inv_name, _fp) = checkpoint.first_violation.as_ref().unwrap();
    assert_eq!(inv_name, "Small");

    let ckpt_dir = tmpdir.join("ckpt_saved");
    checkpoint.save(&ckpt_dir).unwrap();

    // Resume — should report the saved violation.
    let mut checker2 = ParallelChecker::new(&module, &config, 1);
    checker2.set_deadlock_check(false);

    let resume_result = checker2
        .check_with_resume(&ckpt_dir)
        .expect("resume IO should succeed");

    match resume_result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "Small", "resumed violation should match");
        }
        other => panic!("Expected InvariantViolation from resume, got: {other:?}"),
    }

    let _ = std::fs::remove_dir_all(&tmpdir);
}

/// Part of #850: checkpoint resume must preserve detected-action names and
/// stable ids on the saved-violation fast path so duplicate action names stay
/// distinguishable in resumed JSON/error output.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_resume_preserves_detected_action_ids_for_saved_violation() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE DuplicateActions ----
VARIABLE x
Init == x = 0
Foo == x' = x + 1
Next == Foo \/ Foo
Small == x < 2
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Small".to_string()],
        ..Default::default()
    };

    let tmpdir = std::env::temp_dir().join("tla2_test_parallel_ckpt_detected_action_ids");
    let _ = std::fs::remove_dir_all(&tmpdir);
    std::fs::create_dir_all(&tmpdir).unwrap();

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);
    checker.set_max_states(10);
    checker.set_checkpoint(tmpdir.join("ckpt"), Duration::from_secs(3600));

    let result = checker.check();
    let (expected_actions, expected_ids) = match result {
        CheckResult::InvariantViolation {
            invariant, stats, ..
        } => {
            assert_eq!(invariant, "Small");
            assert_eq!(stats.detected_actions, ["Foo", "Foo"]);
            assert_eq!(stats.detected_action_ids.len(), 2);
            assert_ne!(
                stats.detected_action_ids[0], stats.detected_action_ids[1],
                "duplicate detected action names must still carry distinct ids"
            );
            (stats.detected_actions, stats.detected_action_ids)
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    };

    let checkpoint = checker.create_checkpoint().unwrap();
    let ckpt_dir = tmpdir.join("ckpt_saved");
    checkpoint.save(&ckpt_dir).unwrap();

    let mut checker2 = ParallelChecker::new(&module, &config, 1);
    checker2.set_deadlock_check(false);
    let resume_result = checker2
        .check_with_resume(&ckpt_dir)
        .expect("resume IO should succeed");

    match resume_result {
        CheckResult::InvariantViolation {
            invariant, stats, ..
        } => {
            assert_eq!(invariant, "Small");
            assert_eq!(stats.detected_actions, expected_actions);
            assert_eq!(stats.detected_action_ids, expected_ids);
        }
        other => panic!("Expected InvariantViolation from resume, got: {other:?}"),
    }

    let _ = std::fs::remove_dir_all(&tmpdir);
}
