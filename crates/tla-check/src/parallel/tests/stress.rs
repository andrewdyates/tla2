// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stress tests for high concurrency — many workers, contention, determinism

use super::parse_module;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_stress_many_workers() {
    let _serial = super::acquire_interner_lock();
    // Stress test with 8, 12, and 16 workers on a moderate state space
    // Verifies that more workers still produce correct results
    let src = r#"
---- MODULE StressWorkers ----
VARIABLE x, y, z

Init == x \in 0..2 /\ y \in 0..2 /\ z \in 0..2
Next == /\ x' \in 0..2
        /\ y' \in 0..2
        /\ z' \in 0..2
        /\ x' + y' + z' <= 6

Valid == x + y + z <= 6
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        ..Default::default()
    };

    // Get baseline from sequential checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    let (expected_states, expected_transitions) = match seq_result {
        CheckResult::Success(stats) => (stats.states_found, stats.transitions),
        other => panic!("Sequential check failed: {:?}", other),
    };

    // Test with increasing worker counts
    for workers in [8, 12, 16] {
        let mut checker = ParallelChecker::new(&module, &config, workers);
        checker.set_deadlock_check(false);
        let result = checker.check();

        match result {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.states_found, expected_states,
                    "Worker count {} produced wrong state count: {} vs expected {}",
                    workers, stats.states_found, expected_states
                );
                assert_eq!(
                    stats.transitions, expected_transitions,
                    "Worker count {} produced wrong transition count: {} vs expected {} (regression #982)",
                    workers, stats.transitions, expected_transitions
                );
            }
            other => panic!(
                "Parallel check with {} workers failed: {:?}",
                workers, other
            ),
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_stress_high_contention() {
    let _serial = super::acquire_interner_lock();
    // High-contention scenario: many initial states, all workers
    // competing for work simultaneously
    //
    // This creates 4*4*4*4 = 256 initial states, causing high contention
    // as workers race to claim and process them.
    let src = r#"
---- MODULE HighContention ----
VARIABLE a, b, c, d

Init == a \in 1..4 /\ b \in 1..4 /\ c \in 1..4 /\ d \in 1..4
Next == /\ a' = (a % 4) + 1
        /\ b' = (b % 4) + 1
        /\ c' = (c % 4) + 1
        /\ d' = (d % 4) + 1

TypeOK == /\ a \in 1..4
          /\ b \in 1..4
          /\ c \in 1..4
          /\ d \in 1..4
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Get baseline from sequential checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    let (expected_states, expected_initial) = match seq_result {
        CheckResult::Success(stats) => (stats.states_found, stats.initial_states),
        other => panic!("Sequential check failed: {:?}", other),
    };

    // Verify we have many initial states (high contention)
    assert_eq!(expected_initial, 256, "Should have 256 initial states");

    // Run with 8 workers under high contention
    let mut checker = ParallelChecker::new(&module, &config, 8);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.initial_states, expected_initial,
                "Initial state count mismatch under contention"
            );
            assert_eq!(
                stats.states_found, expected_states,
                "State count mismatch under high contention"
            );
        }
        other => panic!("High contention test failed: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_determinism_across_worker_counts() {
    let _serial = super::acquire_interner_lock();
    // Determinism verification: same spec should produce identical
    // results regardless of worker count
    //
    // This tests a spec with non-trivial state space to verify
    // determinism across 1, 2, 4, 8, and 12 workers.
    let src = r#"
---- MODULE Determinism ----
EXTENDS Naturals

VARIABLE pc, x, y

Init == pc = "start" /\ x = 0 /\ y = 0

Next == \/ /\ pc = "start"
           /\ pc' = "inc_x"
           /\ x' = x
           /\ y' = y
        \/ /\ pc = "inc_x"
           /\ x < 3
           /\ x' = x + 1
           /\ pc' = "inc_x"
           /\ y' = y
        \/ /\ pc = "inc_x"
           /\ x >= 3
           /\ pc' = "inc_y"
           /\ x' = x
           /\ y' = y
        \/ /\ pc = "inc_y"
           /\ y < 3
           /\ y' = y + 1
           /\ pc' = "inc_y"
           /\ x' = x
        \/ /\ pc = "inc_y"
           /\ y >= 3
           /\ pc' = "done"
           /\ x' = x
           /\ y' = y
        \/ /\ pc = "done"
           /\ UNCHANGED <<pc, x, y>>

TypeOK == /\ pc \in {"start", "inc_x", "inc_y", "done"}
          /\ x \in 0..3
          /\ y \in 0..3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Collect results from different worker counts
    let worker_counts = [1, 2, 4, 8, 12];
    let mut results: Vec<(usize, usize, usize, usize)> = Vec::new();

    for workers in worker_counts {
        let mut checker = ParallelChecker::new(&module, &config, workers);
        checker.set_deadlock_check(false);
        let result = checker.check();

        match result {
            CheckResult::Success(stats) => {
                results.push((
                    workers,
                    stats.states_found,
                    stats.initial_states,
                    stats.transitions,
                ));
            }
            other => panic!(
                "Determinism test failed with {} workers: {:?}",
                workers, other
            ),
        }
    }

    // Verify all results match
    let (_, first_states, first_initial, first_transitions) = results[0];
    for (workers, states, initial, transitions) in &results[1..] {
        assert_eq!(
            *states, first_states,
            "State count differs between 1 worker and {} workers: {} vs {}",
            workers, first_states, states
        );
        assert_eq!(
            *initial, first_initial,
            "Initial state count differs between 1 worker and {} workers",
            workers
        );
        assert_eq!(
            *transitions, first_transitions,
            "Transition count differs between 1 worker and {} workers",
            workers
        );
    }
}

/// Regression test for #982: transition counts must match between sequential and
/// parallel checkers for multi-action specs with overlapping successor states.
///
/// The original bug manifested with kafka2_core where --workers 1 produced 51440
/// transitions but --workers 16 produced 51512. The root cause was a divergence
/// in successor deduplication between evaluation paths.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_sequential_vs_parallel_transition_count_regression_982() {
    let _serial = super::acquire_interner_lock();
    // Multi-action spec where different OR branches can produce the same successor.
    // This exercises the dedup path that caused the original #982 divergence.
    let src = r#"
---- MODULE TransitionCountRegression ----
VARIABLES x, y, z

Init == x = 0 /\ y = 0 /\ z = 0

\* Action A and Action B can produce overlapping successors
ActionA ==
    /\ x' \in {0, 1, 2}
    /\ y' \in {0, 1}
    /\ z' = z

ActionB ==
    /\ x' \in {1, 2, 3}
    /\ y' = y
    /\ z' \in {0, 1}

ActionC ==
    /\ x' = x
    /\ y' \in {0, 1, 2}
    /\ z' \in {0, 1}

Next == ActionA \/ ActionB \/ ActionC

TypeOK == x \in 0..3 /\ y \in 0..2 /\ z \in 0..1
====
"#;
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Each checker here is an independent same-process run. Re-establish the
    // documented parse+check reset boundary before every run so pointer-keyed
    // caches and global interners cannot leak across the worker-count sweep.
    let run_sequential = || -> crate::check::CheckStats {
        if !crate::intern::has_active_model_check_runs() {
            crate::reset_global_state();
        }
        let module = parse_module(src);
        let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
        seq_checker.set_deadlock_check(false);
        match seq_checker.check() {
            CheckResult::Success(stats) => stats,
            other => panic!("Sequential checker failed: {:?}", other),
        }
    };
    let run_parallel = |workers: usize| -> crate::check::CheckStats {
        if !crate::intern::has_active_model_check_runs() {
            crate::reset_global_state();
        }
        let module = parse_module(src);
        let mut par_checker = ParallelChecker::new(&module, &config, workers);
        par_checker.set_deadlock_check(false);
        match par_checker.check() {
            CheckResult::Success(stats) => stats,
            other => panic!("Parallel checker ({} workers) failed: {:?}", workers, other),
        }
    };

    let seq_stats = run_sequential();

    // Pin expected counts to prevent "both wrong in the same way" regressions.
    // Baseline: TLC reports 433 states generated = 432 transitions + 1 initial.
    // ActionA(6) + ActionB(6) + ActionC(6) = 18 raw successors per state.
    // TLC does not deduplicate across action disjuncts, so 18 * 24 = 432.
    assert_eq!(
        seq_stats.states_found, 24,
        "Expected 24 states (4*3*2 state space)"
    );
    assert_eq!(seq_stats.initial_states, 1, "Expected 1 initial state");
    assert_eq!(
        seq_stats.transitions, 432,
        "Expected 432 transitions (24 states * 18 per-action fanout, TLC: 433 generated)"
    );

    // Run parallel checker across worker counts including 16 (the original #982 repro)
    let mut par_baseline: Option<(usize, usize, usize, usize)> = None;
    for workers in [1, 2, 4, 8, 16] {
        let par_stats = run_parallel(workers);

        assert_eq!(
            seq_stats.states_found, par_stats.states_found,
            "State count differs: seq={}, par({} workers)={}",
            seq_stats.states_found, workers, par_stats.states_found
        );
        assert_eq!(
            seq_stats.initial_states, par_stats.initial_states,
            "Initial state count differs: seq={}, par({} workers)={}",
            seq_stats.initial_states, workers, par_stats.initial_states
        );
        assert_eq!(
            seq_stats.transitions, par_stats.transitions,
            "Transition count differs: seq={}, par({} workers)={} (regression #982)",
            seq_stats.transitions, workers, par_stats.transitions
        );

        // #982 was worker-count dependent; enforce parity across parallel worker counts too.
        if let Some((baseline_workers, baseline_states, baseline_initial, baseline_transitions)) =
            par_baseline
        {
            assert_eq!(
                par_stats.states_found, baseline_states,
                "Parallel state count differs: {} workers={} vs {} workers={}",
                baseline_workers, baseline_states, workers, par_stats.states_found
            );
            assert_eq!(
                par_stats.initial_states, baseline_initial,
                "Parallel initial state count differs: {} workers={} vs {} workers={}",
                baseline_workers, baseline_initial, workers, par_stats.initial_states
            );
            assert_eq!(
                par_stats.transitions, baseline_transitions,
                "Parallel transition count differs: {} workers={} vs {} workers={} (regression #982)",
                baseline_workers, baseline_transitions, workers, par_stats.transitions
            );
        } else {
            par_baseline = Some((
                workers,
                par_stats.states_found,
                par_stats.initial_states,
                par_stats.transitions,
            ));
        }
    }

    if !crate::intern::has_active_model_check_runs() {
        crate::reset_global_state();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_stress_large_fanout() {
    let _serial = super::acquire_interner_lock();
    // Large fanout: each state has many successors, creating work
    // stealing opportunities
    //
    // From each state, there are up to 3 successors, reduced from original to speed up test
    let src = r#"
---- MODULE LargeFanout ----
VARIABLE a, b

Init == a = 0 /\ b = 0

Next == /\ a' \in {a, (a + 1) % 3}
        /\ b' \in {b, (b + 1) % 3}
        /\ (a' /= a \/ b' /= b)

TypeOK == a \in 0..2 /\ b \in 0..2
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Get baseline from sequential checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    let expected_states = match seq_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Sequential check failed: {:?}", other),
    };

    // Run with 8 workers to exercise work stealing
    let mut checker = ParallelChecker::new(&module, &config, 8);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Large fanout test produced wrong state count"
            );
        }
        other => panic!("Large fanout test failed: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_stress_repeated_runs() {
    let _serial = super::acquire_interner_lock();
    // Run the same spec multiple times to check for race conditions
    // that might cause non-deterministic failures
    let src = r#"
---- MODULE RepeatedRuns ----
VARIABLE x

Init == x \in 1..5
Next == x' = (x % 5) + 1

TypeOK == x \in 1..5
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Run 10 times and verify consistent results
    let mut state_counts: Vec<usize> = Vec::new();
    for _ in 0..10 {
        let mut checker = ParallelChecker::new(&module, &config, 8);
        checker.set_deadlock_check(false);
        let result = checker.check();

        match result {
            CheckResult::Success(stats) => {
                state_counts.push(stats.states_found);
            }
            other => panic!("Repeated run failed: {:?}", other),
        }
    }

    // All runs should produce the same state count
    let first = state_counts[0];
    for (i, count) in state_counts.iter().enumerate() {
        assert_eq!(
            *count, first,
            "Run {} produced {} states, expected {} (non-deterministic behavior detected)",
            i, count, first
        );
    }
}
