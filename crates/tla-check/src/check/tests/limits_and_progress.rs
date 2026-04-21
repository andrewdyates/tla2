// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================
// Exploration limit tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_max_states_limit() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Unbounded counter that would run forever without limits
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(5);

    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(limit_type, LimitType::States);
            assert_eq!(stats.states_found, 5);
        }
        other => panic!("Expected LimitReached(States), got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_max_depth_limit() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Unbounded counter that would run forever without limits
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_depth(3);

    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(limit_type, LimitType::Depth);
            // Should have explored: x=0 (depth 0), x=1 (depth 1), x=2 (depth 2), x=3 (depth 3)
            // But x=3 is at max_depth so we don't generate x=4
            assert_eq!(stats.states_found, 4);
            assert_eq!(stats.max_depth, 3);
        }
        other => panic!("Expected LimitReached(Depth), got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_found_before_limit() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter with invariant that will be violated before hitting limit
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallValue == x < 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(100); // High limit that won't be reached

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant, stats, ..
        } => {
            assert_eq!(invariant, "SmallValue");
            // Should find violation at x=3 before hitting 100 state limit
            assert!(stats.states_found < 100);
        }
        other => panic!("Expected InvariantViolation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_success_within_limits() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Bounded counter that terminates naturally
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
InRange == x >= 0 /\ x <= 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(100);
    checker.set_max_depth(100);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should complete naturally with 4 states
            assert_eq!(stats.states_found, 4);
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_depth_tracking() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Bounded counter
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 6); // x=0,1,2,3,4,5
            assert_eq!(stats.max_depth, 5); // 0->1->2->3->4->5
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

// ============================
// Progress callback tests
// ============================

fn assert_duplicate_init_progress_counts(
    src: &str,
    expected_generated: usize,
    expected_distinct: usize,
) {
    use std::sync::{Arc, Mutex};
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    for (store_full_states, mode_name) in [(false, "no-trace"), (true, "full-state")] {
        let init_progress = Arc::new(Mutex::new(Vec::new()));
        let init_progress_clone = Arc::clone(&init_progress);

        let mut checker = ModelChecker::new(&module, &config);
        checker.set_store_states(store_full_states);
        checker.set_deadlock_check(false);
        if !store_full_states {
            checker.set_auto_create_trace_file(false);
        }
        checker.set_init_progress_callback(Box::new(move |progress| {
            init_progress_clone
                .lock()
                .expect("init progress callback mutex poisoned")
                .push((progress.states_generated, progress.distinct_states));
        }));

        let result = checker.check();

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.initial_states, expected_distinct,
                    "{mode_name}: initial_states should match distinct init states"
                );
                assert_eq!(
                    stats.states_found, expected_distinct,
                    "{mode_name}: stuttering Next should keep the reachable count at the distinct init count"
                );
            }
            other => panic!("{mode_name}: expected Success, got {:?}", other),
        }

        let recorded = init_progress
            .lock()
            .expect("init progress results mutex poisoned");
        assert_eq!(
            recorded.as_slice(),
            &[(expected_generated, expected_distinct)],
            "{mode_name}: expected one init progress callback with pre-dedup and distinct counts"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_progress_reports_generated_and_distinct_for_streaming_duplicates() {
    let src = r#"
---- MODULE DuplicateInitStreaming ----
VARIABLE x
Init == x = 0 \/ x = 0
Next == x' = x
====
"#;

    assert_duplicate_init_progress_counts(src, 2, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_progress_reports_generated_and_distinct_for_fallback_duplicates() {
    let src = r#"
---- MODULE DuplicateInitFallback ----
VARIABLE x
Init == x \in {y \in {0, 1} : y = 0} \/ x \in {y \in {0, 1} : y = 0}
Next == x' = x
====
"#;

    assert_duplicate_init_progress_counts(src, 2, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_progress_callback() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Counter that explores a moderate number of states
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 100 /\ x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let callback_count = Arc::new(AtomicUsize::new(0));
    let callback_count_clone = Arc::clone(&callback_count);
    let memory_samples = Arc::new(Mutex::new(Vec::new()));
    let memory_samples_clone = Arc::clone(&memory_samples);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_progress_interval(10); // Report every 10 states
    checker.set_progress_callback(Box::new(move |progress| {
        callback_count_clone.fetch_add(1, Ordering::SeqCst);
        // Verify progress values are reasonable
        assert!(progress.states_found > 0);
        memory_samples_clone
            .lock()
            .expect("progress memory samples mutex poisoned")
            .push(progress.memory_usage_bytes);
    }));

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 101); // x=0,1,2,...,100
                                                 // Should have been called approximately 10 times (101 states / 10 interval)
            let count = callback_count.load(Ordering::SeqCst);
            assert!(
                count >= 5,
                "Expected at least 5 progress callbacks, got {}",
                count
            );
            let samples = memory_samples
                .lock()
                .expect("progress memory samples mutex poisoned");
            if cfg!(any(target_os = "macos", target_os = "linux")) {
                assert!(
                    samples
                        .iter()
                        .any(|sample| sample.is_some_and(|bytes| bytes > 0)),
                    "expected at least one progress callback to report RSS bytes, got {:?}",
                    samples.as_slice()
                );
            }
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_progress_callback_disabled() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 10 /\ x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let callback_count = Arc::new(AtomicUsize::new(0));
    let callback_count_clone = Arc::clone(&callback_count);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_progress_interval(0); // Disabled
    checker.set_progress_callback(Box::new(move |_| {
        callback_count_clone.fetch_add(1, Ordering::SeqCst);
    }));

    let result = checker.check();

    match result {
        CheckResult::Success(_) => {
            // Callback should never be called when interval is 0
            let count = callback_count.load(Ordering::SeqCst);
            assert_eq!(
                count, 0,
                "Expected 0 callbacks when disabled, got {}",
                count
            );
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}
