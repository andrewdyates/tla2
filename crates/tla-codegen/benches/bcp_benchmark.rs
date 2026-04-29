// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Benchmark: BCP codegen-generated vs hand-written Rust.
//!
//! Compares the auto-generated BCP state machine (from `tla2 codegen --tir`)
//! against a hand-optimized native Rust implementation of the same spec.
//!
//! Both implementations model BCP (Boolean Constraint Propagation) for a
//! 3-variable, 4-clause SAT instance and should produce exactly 32 reachable
//! states (matching TLC).
//!
//! Part of #3730.

use criterion::{black_box, criterion_group, criterion_main, Criterion};

// ── Generated BCP (from `tla2 codegen --tir`) ──────────────────────────────

#[path = "../examples/bcp_generated.rs"]
#[allow(dead_code)]
mod bcp_generated;

// ── Hand-written BCP ────────────────────────────────────────────────────────

#[path = "../examples/bcp_handwritten.rs"]
#[allow(dead_code)]
mod bcp_handwritten;

use tla_runtime::prelude::*;

/// BFS state exploration returning (distinct_states, transitions).
fn explore_generated() -> (usize, usize) {
    use std::collections::{HashSet, VecDeque};

    let machine = bcp_generated::BCP;
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
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

fn explore_handwritten() -> (usize, usize) {
    use std::collections::{HashSet, VecDeque};

    let machine = bcp_handwritten::HandBCP;
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
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
fn explore_generated_with_invariants() -> (usize, usize) {
    use std::collections::{HashSet, VecDeque};

    let machine = bcp_generated::BCP;
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
    let mut transitions = 0usize;

    for s in machine.init() {
        assert_ne!(machine.check_invariant(&s), Some(false));
        if seen.insert(s.clone()) {
            queue.push_back(s);
        }
    }

    while let Some(state) = queue.pop_front() {
        let succs = machine.next(&state);
        transitions += succs.len();
        for s in succs {
            assert_ne!(machine.check_invariant(&s), Some(false));
            if seen.insert(s.clone()) {
                queue.push_back(s);
            }
        }
    }

    (seen.len(), transitions)
}

fn explore_handwritten_with_invariants() -> (usize, usize) {
    use std::collections::{HashSet, VecDeque};

    let machine = bcp_handwritten::HandBCP;
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
    let mut transitions = 0usize;

    for s in machine.init() {
        assert_ne!(machine.check_invariant(&s), Some(false));
        if seen.insert(s.clone()) {
            queue.push_back(s);
        }
    }

    while let Some(state) = queue.pop_front() {
        let succs = machine.next(&state);
        transitions += succs.len();
        for s in succs {
            assert_ne!(machine.check_invariant(&s), Some(false));
            if seen.insert(s.clone()) {
                queue.push_back(s);
            }
        }
    }

    (seen.len(), transitions)
}

fn bench_bcp(c: &mut Criterion) {
    // Sanity check: both produce the same state count
    let (gen_states, gen_trans) = explore_generated();
    let (hand_states, hand_trans) = explore_handwritten();
    assert_eq!(gen_states, 32, "Generated BCP should find 32 states");
    assert_eq!(hand_states, 32, "Handwritten BCP should find 32 states");
    eprintln!(
        "Generated:    {} states, {} transitions",
        gen_states, gen_trans
    );
    eprintln!(
        "Handwritten:  {} states, {} transitions",
        hand_states, hand_trans
    );

    let mut group = c.benchmark_group("bcp_state_exploration");

    group.bench_function("generated_bfs", |b| {
        b.iter(|| {
            let (states, _) = explore_generated();
            black_box(states)
        })
    });

    group.bench_function("handwritten_bfs", |b| {
        b.iter(|| {
            let (states, _) = explore_handwritten();
            black_box(states)
        })
    });

    group.bench_function("generated_bfs_with_invariants", |b| {
        b.iter(|| {
            let (states, _) = explore_generated_with_invariants();
            black_box(states)
        })
    });

    group.bench_function("handwritten_bfs_with_invariants", |b| {
        b.iter(|| {
            let (states, _) = explore_handwritten_with_invariants();
            black_box(states)
        })
    });

    group.finish();
}

criterion_group!(benches, bench_bcp);
criterion_main!(benches);
