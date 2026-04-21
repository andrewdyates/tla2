// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Setup and progress callback tests for ParallelChecker.

use super::super::*;
use crate::test_support::parse_module;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn register_inline_next_recomputes_uses_trace_detector() {
    let src = r#"
---- MODULE InlineNextTraceDetect ----
EXTENDS TLCExt
VARIABLE x
Init == x = 0
Spec == Init /\ [][(x' = x + 1 /\ TLCExt!Trace = TLCExt!Trace)]_x
====
"#;
    let tree = parse_to_syntax_tree(src);
    let module = lower(FileId(0), &tree).module.unwrap();

    let mut config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = crate::check::resolve_spec_from_config(&config, &tree)
        .expect("SPECIFICATION with inline NEXT should resolve");
    assert_eq!(resolved.next, crate::check::INLINE_NEXT_NAME);
    assert!(
        resolved.next_node.is_some(),
        "resolved spec should include inline NEXT node"
    );

    config.init = Some(resolved.init.clone());
    config.next = Some(resolved.next.clone());

    let mut checker = ParallelChecker::new(&module, &config, 1);
    assert!(
        !checker.uses_trace,
        "inline NEXT is not registered yet; detector should still be false"
    );

    checker.set_store_states(false);
    assert!(
        !checker.store_full_states,
        "precondition: no-trace mode accepted before inline NEXT registration"
    );

    checker
        .register_inline_next(&resolved)
        .expect("inline NEXT registration should succeed");
    assert!(
        checker.uses_trace,
        "register_inline_next must recompute uses_trace when inline NEXT references TLCExt!Trace"
    );
    assert!(
        checker.store_full_states,
        "Trace usage from inline NEXT must auto-enable full-state storage"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_progress_callback_reports_memory_usage() {
    let _serial = crate::test_utils::acquire_interner_lock();
    let src = r#"
---- MODULE ParallelProgress ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let callback_count = Arc::new(AtomicUsize::new(0));
    let callback_count_clone = Arc::clone(&callback_count);
    let memory_samples = Arc::new(Mutex::new(Vec::new()));
    let memory_samples_clone = Arc::clone(&memory_samples);

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_max_states(20_000);
    checker.progress_interval_ms = 1;
    checker.set_progress_callback(Box::new(move |progress| {
        callback_count_clone.fetch_add(1, Ordering::SeqCst);
        assert!(progress.states_found > 0);
        memory_samples_clone
            .lock()
            .expect("parallel progress memory samples mutex poisoned")
            .push(progress.memory_usage_bytes);
    }));

    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(limit_type, LimitType::States);
            assert_eq!(stats.states_found, 20_000);
        }
        other => panic!("Expected LimitReached(States), got {:?}", other),
    }

    let count = callback_count.load(Ordering::SeqCst);
    assert!(
        count > 0,
        "expected at least one parallel progress callback, got {count}"
    );
    let samples = memory_samples
        .lock()
        .expect("parallel progress memory samples mutex poisoned");
    if cfg!(any(target_os = "macos", target_os = "linux")) {
        assert!(
            samples
                .iter()
                .any(|sample| sample.is_some_and(|bytes| bytes > 0)),
            "expected at least one parallel progress callback to report RSS bytes, got {:?}",
            samples.as_slice()
        );
    }
}
