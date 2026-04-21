// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_merge_additive_fields() {
    let mut a = ChcStatistics {
        iterations: 10,
        lemmas_learned: 5,
        max_frame: 3,
        restarts: 1,
        smt_unknowns: 2,
        cache_hits: 4,
        cache_model_rejections: 3,
        cache_solver_calls: 20,
    };
    let b = ChcStatistics {
        iterations: 20,
        lemmas_learned: 15,
        max_frame: 7,
        restarts: 2,
        smt_unknowns: 1,
        cache_hits: 6,
        cache_model_rejections: 2,
        cache_solver_calls: 30,
    };
    a.merge(&b);
    assert_eq!(a.iterations, 30);
    assert_eq!(a.lemmas_learned, 20);
    assert_eq!(a.restarts, 3);
    assert_eq!(a.smt_unknowns, 3);
    assert_eq!(a.cache_hits, 10);
    assert_eq!(a.cache_model_rejections, 5);
    assert_eq!(a.cache_solver_calls, 50);
}

#[test]
fn test_merge_max_frame_takes_maximum() {
    let mut a = ChcStatistics {
        max_frame: 10,
        ..Default::default()
    };
    let b = ChcStatistics {
        max_frame: 5,
        ..Default::default()
    };
    a.merge(&b);
    assert_eq!(a.max_frame, 10, "max_frame should keep larger value");

    let mut c = ChcStatistics {
        max_frame: 3,
        ..Default::default()
    };
    let d = ChcStatistics {
        max_frame: 8,
        ..Default::default()
    };
    c.merge(&d);
    assert_eq!(c.max_frame, 8, "max_frame should take other's larger value");
}

#[test]
fn test_merge_with_default_is_identity() {
    let a = ChcStatistics {
        iterations: 42,
        lemmas_learned: 7,
        max_frame: 3,
        restarts: 1,
        smt_unknowns: 0,
        cache_hits: 2,
        cache_model_rejections: 1,
        cache_solver_calls: 10,
    };
    let mut b = a.clone();
    b.merge(&ChcStatistics::default());
    assert_eq!(b.iterations, a.iterations);
    assert_eq!(b.lemmas_learned, a.lemmas_learned);
    assert_eq!(b.max_frame, a.max_frame);
    assert_eq!(b.cache_solver_calls, a.cache_solver_calls);
}

#[test]
fn test_from_solver_stats_conversion() {
    let s = SolverStats {
        iterations: 100,
        lemmas_learned: 50,
        max_frame: 12,
        restart_count: 3,
        smt_unknowns: 5,
        implication_cache_hits: 20,
        implication_model_rejections: 10,
        implication_solver_calls: 80,
        ..Default::default()
    };
    let chc: ChcStatistics = s.into();
    assert_eq!(chc.iterations, 100);
    assert_eq!(chc.lemmas_learned, 50);
    assert_eq!(chc.max_frame, 12);
    assert_eq!(chc.restarts, 3);
    assert_eq!(chc.smt_unknowns, 5);
    assert_eq!(chc.cache_hits, 20);
    assert_eq!(chc.cache_model_rejections, 10);
    assert_eq!(chc.cache_solver_calls, 80);
}

#[test]
fn test_merge_saturates_on_overflow() {
    let mut a = ChcStatistics {
        iterations: u64::MAX - 1,
        lemmas_learned: u64::MAX - 2,
        max_frame: 1,
        restarts: u64::MAX - 3,
        smt_unknowns: u64::MAX - 4,
        cache_hits: u64::MAX - 5,
        cache_model_rejections: u64::MAX - 6,
        cache_solver_calls: u64::MAX - 7,
    };
    let b = ChcStatistics {
        iterations: 100,
        lemmas_learned: 100,
        max_frame: 2,
        restarts: 100,
        smt_unknowns: 100,
        cache_hits: 100,
        cache_model_rejections: 100,
        cache_solver_calls: 100,
    };
    a.merge(&b);

    assert_eq!(a.iterations, u64::MAX);
    assert_eq!(a.lemmas_learned, u64::MAX);
    assert_eq!(a.max_frame, 2);
    assert_eq!(a.restarts, u64::MAX);
    assert_eq!(a.smt_unknowns, u64::MAX);
    assert_eq!(a.cache_hits, u64::MAX);
    assert_eq!(a.cache_model_rejections, u64::MAX);
    assert_eq!(a.cache_solver_calls, u64::MAX);
}
