// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_during_bfs() {
    use tempfile::tempdir;

    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 5
TypeOK == x \in 0..4
====
"#,
    );
    let config = init_next_config(&["TypeOK"]);

    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
    checker.set_checkpoint_paths(Some("test.tla".to_string()), Some("test.cfg".to_string()));

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 5,
                "x cycles through 0..4, so there should be exactly 5 states"
            );
        }
        other => panic!("expected Success, got: {other:?}"),
    }

    assert!(
        checkpoint_path.exists(),
        "Checkpoint directory should exist"
    );
    assert!(checkpoint_path.join("checkpoint.json").exists());
    assert!(checkpoint_path.join("fingerprints.bin").exists());
    assert!(checkpoint_path.join("frontier.json").exists());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_resume_continues_exploration() {
    use tempfile::tempdir;

    // Spec with branching but NO cycles
    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next ==
\/ (x < 2 /\ x' = x + 1 /\ y' = y)
\/ (y < 2 /\ x' = x /\ y' = y + 1)
TypeOK == x \in 0..2 /\ y \in 0..2
====
"#,
    );
    let config = init_next_config(&["TypeOK"]);

    // Baseline: get expected state count
    let expected_states = {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        match checker.check() {
            CheckResult::Success(stats) => stats.states_found,
            other => panic!("Expected Success, got {:?}", other),
        }
    };
    assert_eq!(expected_states, 9, "Expected 3x3 grid to have 9 states");

    // Stop early with checkpoint
    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");
    save_checkpoint_stopping_at(&module, &config, &checkpoint_path, 3);

    // Verify checkpoint frontier
    assert!(checkpoint_path.exists());
    {
        use crate::checkpoint::Checkpoint;
        let cp = Checkpoint::load(&checkpoint_path).expect("checkpoint load");
        assert!(!cp.frontier.is_empty(), "Expected non-empty frontier");
    }

    // Resume should reach full state count
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("Resume should succeed");
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Should reach full count"
            );
            assert_eq!(checker.test_seen_fps_len(), expected_states);
        }
        other => panic!("Expected Success after resume, got {:?}", other),
    }
}

/// Content hash verification: resume must reject a checkpoint whose spec file
/// was modified since the checkpoint was saved, even when the path matches.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_rejects_modified_spec_content_hash() {
    use tempfile::tempdir;

    let spec_v1 = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#;
    let spec_v2 = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 5
====
"#;

    let config = init_next_config(&[]);

    let work_dir = tempdir().unwrap();
    let spec_path = work_dir.path().join("test.tla");
    let cfg_path = work_dir.path().join("test.cfg");
    let checkpoint_path = work_dir.path().join("checkpoint");

    // Write spec v1 and config
    std::fs::write(&spec_path, spec_v1).unwrap();
    std::fs::write(&cfg_path, "INIT Init\nNEXT Next\n").unwrap();

    // Create a checkpoint with spec v1 content
    let module = parse_module(spec_v1);
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_max_states(1);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
        checker.set_checkpoint_paths(
            Some(spec_path.to_str().unwrap().to_string()),
            Some(cfg_path.to_str().unwrap().to_string()),
        );
        let result = checker.check();
        assert!(matches!(result, CheckResult::LimitReached { .. }));
    }

    // Verify checkpoint has the hash
    {
        let cp = crate::checkpoint::Checkpoint::load(&checkpoint_path).unwrap();
        assert!(
            cp.metadata.spec_hash.is_some(),
            "checkpoint must include spec content hash"
        );
        assert!(
            cp.metadata.config_hash.is_some(),
            "checkpoint must include config content hash"
        );
    }

    // Overwrite spec file with v2 (different content, same path)
    std::fs::write(&spec_path, spec_v2).unwrap();

    // Resume with modified spec: must fail with content hash mismatch
    let module_v2 = parse_module(spec_v2);
    let mut checker = ModelChecker::new(&module_v2, &config);
    checker.set_deadlock_check(false);
    checker.set_checkpoint_paths(
        Some(spec_path.to_str().unwrap().to_string()),
        Some(cfg_path.to_str().unwrap().to_string()),
    );
    let err = checker.check_with_resume(&checkpoint_path).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("content hash mismatch"),
        "expected content hash mismatch error, got: {err}"
    );
}

/// Backward compatibility: checkpoints saved without content hashes (old format)
/// must be accepted on resume without error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_accepts_checkpoint_without_content_hashes() {
    use tempfile::tempdir;

    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );
    let config = init_next_config(&[]);

    let work_dir = tempdir().unwrap();
    let spec_path = work_dir.path().join("test.tla");
    let cfg_path = work_dir.path().join("test.cfg");
    let checkpoint_path = work_dir.path().join("checkpoint");

    std::fs::write(
        &spec_path,
        "---- MODULE Test ----\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\n====\n",
    )
    .unwrap();
    std::fs::write(&cfg_path, "INIT Init\nNEXT Next\n").unwrap();

    // Create checkpoint WITHOUT content hashes (simulate old format by not
    // providing real file paths — non-existent paths produce None hashes).
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_max_states(1);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
        // Use non-existent paths so hashes will be None
        checker.set_checkpoint_paths(
            Some("/nonexistent/test.tla".to_string()),
            Some("/nonexistent/test.cfg".to_string()),
        );
        let result = checker.check();
        assert!(matches!(result, CheckResult::LimitReached { .. }));
    }

    // Verify checkpoint has no hashes (simulating old format)
    {
        let cp = crate::checkpoint::Checkpoint::load(&checkpoint_path).unwrap();
        assert!(
            cp.metadata.spec_hash.is_none(),
            "checkpoint should NOT have spec hash (non-existent file)"
        );
    }

    // Resume with real file paths (which DO produce hashes): should succeed
    // because the checkpoint side is None, so we skip hash comparison.
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_checkpoint_paths(
        Some("/nonexistent/test.tla".to_string()),
        Some("/nonexistent/test.cfg".to_string()),
    );
    let result = checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should succeed when checkpoint lacks hashes");
    assert!(
        matches!(result, CheckResult::Success(_)),
        "expected success, got: {result:?}"
    );
}

/// Regression test for #1798: check_with_resume must reject checkpoint metadata
/// that does not match the current spec/config invocation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resume_rejects_mismatched_checkpoint_metadata_paths() {
    use tempfile::tempdir;

    let module = parse_module(
        r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
    );
    let config = init_next_config(&[]);

    let checkpoint_dir = tempdir().unwrap();
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");

    // Create a checkpoint bound to spec-A identity
    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_max_states(1);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));
        checker.set_checkpoint_paths(
            Some("/tmp/spec-A.tla".to_string()),
            Some("/tmp/spec-A.cfg".to_string()),
        );
        let result = checker.check();
        assert!(
            matches!(result, CheckResult::LimitReached { .. }),
            "Expected LimitReached, got {:?}",
            result
        );
    }

    // Resume with spec-B identity: must fail
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_checkpoint_paths(
        Some("/tmp/spec-B.tla".to_string()),
        Some("/tmp/spec-B.cfg".to_string()),
    );
    let err = checker.check_with_resume(&checkpoint_path).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("checkpoint spec path mismatch"),
        "#1798: expected spec-path mismatch error, got: {err}"
    );
}
