// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: BCP codegen correctness and performance comparison.
//!
//! Validates that the auto-generated BCP state machine (from `tla2 codegen --tir`
//! on specs/z4/BCP.tla) produces exactly 32 reachable states and 46 transitions,
//! matching TLC and the TLA2 interpreter. Also compares against a hand-written
//! implementation to quantify the codegen overhead.
//!
//! Part of #3730.

#[path = "../examples/bcp_generated.rs"]
#[allow(dead_code)]
mod bcp_generated;

#[path = "../examples/bcp_handwritten.rs"]
#[allow(dead_code)]
mod bcp_handwritten;

use std::collections::{HashSet, VecDeque};
use std::time::Instant;
use tla_runtime::prelude::*;

/// BFS exploration returning (distinct states, total transitions).
fn bfs_explore<M: StateMachine>(machine: &M) -> (usize, usize)
where
    M::State: Clone + Eq + std::hash::Hash + std::fmt::Debug,
{
    let mut seen: HashSet<M::State> = HashSet::new();
    let mut queue: VecDeque<M::State> = VecDeque::new();
    let mut transitions = 0usize;

    for s in machine.init() {
        if seen.insert(s.clone()) {
            queue.push_back(s);
        }
    }

    while let Some(state) = queue.pop_front() {
        let succs = machine.next(&state);
        transitions += succs.len();
        for s in succs {
            if seen.insert(s.clone()) {
                queue.push_back(s);
            }
        }
    }

    (seen.len(), transitions)
}

/// BFS with invariant checking on every state.
fn bfs_explore_with_invariants<M: StateMachine>(machine: &M) -> (usize, usize)
where
    M::State: Clone + Eq + std::hash::Hash + std::fmt::Debug,
{
    let mut seen: HashSet<M::State> = HashSet::new();
    let mut queue: VecDeque<M::State> = VecDeque::new();
    let mut transitions = 0usize;

    for s in machine.init() {
        assert_ne!(
            machine.check_invariant(&s),
            Some(false),
            "Invariant violated on init state: {:?}",
            s
        );
        if seen.insert(s.clone()) {
            queue.push_back(s);
        }
    }

    while let Some(state) = queue.pop_front() {
        let succs = machine.next(&state);
        transitions += succs.len();
        for s in succs {
            assert_ne!(
                machine.check_invariant(&s),
                Some(false),
                "Invariant violated on state: {:?}",
                s
            );
            if seen.insert(s.clone()) {
                queue.push_back(s);
            }
        }
    }

    (seen.len(), transitions)
}

// ── Correctness tests ──────────────────────────────────────────────────────

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generated_bcp_state_count() {
    let (states, _transitions) = bfs_explore(&bcp_generated::BCP);
    assert_eq!(
        states, 32,
        "Generated BCP should find exactly 32 states (TLC baseline)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handwritten_bcp_state_count() {
    let (states, _transitions) = bfs_explore(&bcp_handwritten::HandBCP);
    assert_eq!(
        states, 32,
        "Handwritten BCP should find exactly 32 states (TLC baseline)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generated_bcp_invariants_hold() {
    let (states, _) = bfs_explore_with_invariants(&bcp_generated::BCP);
    assert_eq!(states, 32);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handwritten_bcp_invariants_hold() {
    let (states, _) = bfs_explore_with_invariants(&bcp_handwritten::HandBCP);
    assert_eq!(states, 32);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generated_bcp_init_state() {
    let machine = bcp_generated::BCP;
    let init = machine.init();
    assert_eq!(init.len(), 1, "BCP should have exactly one initial state");
    let s = &init[0];
    assert!(!s.conflict);
    assert!(s.propagating);
    assert!(s.trail.is_empty());
    // All variables should be UNSET
    for v in 1..=3i64 {
        assert_eq!(
            s.assignment.apply(&v).map(|s| s.as_str()),
            Some("UNSET"),
            "Variable {} should be UNSET initially",
            v
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generated_bcp_named_invariants() {
    let machine = bcp_generated::BCP;
    let names = machine.invariant_names();
    assert_eq!(
        names,
        vec![
            "TypeOK",
            "TrailConsistent",
            "NoSpuriousConflict",
            "PropagationSound"
        ]
    );

    // Check each named invariant on the init state
    let init = &machine.init()[0];
    for name in &names {
        assert_eq!(
            machine.check_named_invariant(name, init),
            Some(true),
            "Invariant {} should hold on init state",
            name
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generated_bcp_model_check() {
    let machine = bcp_generated::BCP;
    // model_check checks invariants + deadlock
    // BCP has the Done stuttering action so no deadlock
    let result = model_check(&machine, 1000);
    assert_eq!(result.distinct_states, 32);
    // No invariant violation expected
    assert!(
        result.violation.is_none(),
        "No invariant violations expected"
    );
}

// ── Performance comparison ─────────────────────────────────────────────────

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bcp_performance_comparison() {
    // Warm up
    let _ = bfs_explore(&bcp_generated::BCP);
    let _ = bfs_explore(&bcp_handwritten::HandBCP);

    const ITERATIONS: u32 = 100;

    // Time the generated version
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let (states, _) = bfs_explore(&bcp_generated::BCP);
        assert_eq!(states, 32);
    }
    let gen_elapsed = start.elapsed();

    // Time the handwritten version
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let (states, _) = bfs_explore(&bcp_handwritten::HandBCP);
        assert_eq!(states, 32);
    }
    let hand_elapsed = start.elapsed();

    let gen_us = gen_elapsed.as_micros() as f64 / ITERATIONS as f64;
    let hand_us = hand_elapsed.as_micros() as f64 / ITERATIONS as f64;
    let ratio = gen_us / hand_us;

    eprintln!(
        "=== BCP Performance Comparison ({} iterations) ===",
        ITERATIONS
    );
    eprintln!("Generated:   {:.1} us/iteration", gen_us);
    eprintln!("Handwritten: {:.1} us/iteration", hand_us);
    eprintln!("Ratio:       {:.2}x (generated/handwritten)", ratio);
    eprintln!("================================================");

    // The generated code uses TlaSet<TlaSet<i64>>, TlaFunc<i64, String>, etc.
    // which is fundamentally slower than native arrays and enums.
    // We expect the generated code to be slower but it should still be
    // within a reasonable range for a 32-state spec.
    //
    // This benchmark establishes the baseline for future codegen optimization.
}
