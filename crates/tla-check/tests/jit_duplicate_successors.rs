// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for JIT duplicate-successor bookkeeping in the full-state BFS path.
//!
//! Part of #4300: duplicate self-loops must still count as observable successors
//! after JIT dedup, otherwise the checker can undercount transitions or report a
//! false deadlock.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};
use tla_eval::clear_for_test_reset;

const LIMIT: usize = 2500;

const DUPLICATE_SELF_LOOP_SPEC: &str = r#"
---- MODULE JitDuplicateSelfLoop ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Advance ==
    /\ x < 2500
    /\ x' = x + 1

Stutter == x' = x

Next == Advance \/ Stutter

====
"#;

/// Force the legacy full-state BFS route (no flat BFS, no diff path) and enable
/// tiered JIT with an immediate promotion threshold. The run keeps a duplicate
/// self-loop on every state, so once JIT activates both the validation and fused
/// JIT paths must preserve transition bookkeeping for already-seen successors.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_jit_duplicate_self_loops_preserve_transitions_and_avoid_false_deadlock() {
    let _jit = common::EnvVarGuard::set("TLA2_JIT", Some("1"));
    let _show_tiers = common::EnvVarGuard::set("TLA2_SHOW_TIERS", Some("1"));
    let _tier1 = common::EnvVarGuard::set("TLA2_JIT_TIER1_THRESHOLD", Some("1"));
    let _tier2 = common::EnvVarGuard::set("TLA2_JIT_TIER2_THRESHOLD", Some("1000000"));
    let _no_diffs = common::EnvVarGuard::set("TLA2_FORCE_NO_DIFFS", Some("1"));
    clear_for_test_reset();

    let module = common::parse_module(DUPLICATE_SELF_LOOP_SPEC);
    let mut config = Config::parse("INIT Init\nNEXT Next\n").expect("valid cfg");
    config.auto_por = Some(false);
    config.use_flat_state = Some(false);
    config.use_compiled_bfs = Some(false);
    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found,
                LIMIT + 1,
                "expected one state per counter value plus the initial state",
            );
            assert_eq!(
                stats.transitions,
                LIMIT * 2 + 1,
                "duplicate self-loops must still be counted as observable transitions",
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            panic!(
                "JIT duplicate bookkeeping regressed: terminal duplicate self-loop was treated as deadlock \
                 (states_found={}, transitions={})",
                stats.states_found, stats.transitions
            );
        }
        other => panic!("expected success, got {other:?}"),
    }
}
