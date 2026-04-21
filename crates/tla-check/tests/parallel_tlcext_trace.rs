// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::CheckResult;
use tla_check::Config;
use tla_check::ParallelChecker;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_tlcext_trace_invariants_use_full_prefix() {
    // Trace is expected to be the behavior prefix up to the current state.
    // This invariant checks that Len(Trace) == x + 1 AND that each Trace[i].x == i - 1.
    // Part of #1139 audit: Checks both length and content to catch trace reconstruction bugs.
    let src = r#"
---- MODULE ParallelTraceTest ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
\* Check both length AND content of trace
TraceInv == /\ Len(Trace) = x + 1
            /\ \A i \in 1..(x+1) : Trace[i].x = i - 1
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TraceInv".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    // Part of #1139: Trace requires full state storage; ParallelChecker should auto-enable it
    // even if the caller tries to disable it via the public API.
    checker.set_store_states(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // Verify state count matches expected: x goes from 0 to 5, so 6 states
            assert_eq!(
                stats.states_found, 6,
                "Expected 6 states (x=0..5), got {}",
                stats.states_found
            );
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}
