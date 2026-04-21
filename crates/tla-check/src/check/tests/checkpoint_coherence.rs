// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for checkpoint coherence gate (#2353).

use super::*;

/// Regression test for #2353: create_checkpoint must fail when trace.depths
/// and seen_fps cardinalities diverge (checkpoint coherence gate).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_coherence_gate_rejects_mismatch() {
    use crate::state::Fingerprint;
    use std::collections::VecDeque;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
TypeOK == x \in {0, 1, 2}
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Part of #2881 Step 3: depths HashMap is only populated when checkpoint is
    // configured. Set a checkpoint dir so the coherence gate test exercises the
    // expected path.
    let tmpdir = std::env::temp_dir().join("tla2_test_checkpoint_coherence");
    let _ = std::fs::create_dir_all(&tmpdir);
    checker.set_checkpoint(tmpdir.clone(), std::time::Duration::from_secs(3600));

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected 3 states");
        }
        other => panic!("expected Success, got: {other:?}"),
    }

    // Coherent checkpoint should succeed.
    let frontier: VecDeque<crate::state::State> = VecDeque::new();
    let ok_result = checker.create_checkpoint(&frontier, None, None);
    assert!(ok_result.is_ok(), "coherent checkpoint should succeed");

    // Inject a spurious fingerprint to create a mismatch.
    checker.test_inject_spurious_fingerprint(Fingerprint(0xDEADBEEF));
    assert_eq!(
        checker.test_seen_fps_len(),
        4,
        "seen_fps should now have 4 entries"
    );

    // Incoherent checkpoint should fail.
    let err_result = checker.create_checkpoint(&frontier, None, None);
    assert!(err_result.is_err(), "incoherent checkpoint should fail");

    let err = err_result.unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("coherence failure"),
        "error should mention coherence failure: {msg}"
    );
    assert!(
        msg.contains('3') && msg.contains('4'),
        "error should mention the cardinality mismatch (3 vs 4): {msg}"
    );
}
