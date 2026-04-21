// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Adaptive-entrypoint regression coverage for the current #6047 array-MBP lane.
//!
//! `chc_dt_array_zani_harder.smt2` is the benchmark-backed single-predicate
//! zani-style heap case that the March 19 spot check proved safe through
//! `z4 --chc`, matching Z3's `sat` result.
//!
//! This test pins that consumer-facing behavior on the actual benchmark rather
//! than a synthetic approximation. The still-open multi-predicate surrogate
//! (`chc_loop_alloc_multi_pred.smt2`) is intentionally not asserted here
//! because current HEAD still returns `unknown` there.

use ntest::timeout;
use std::time::Duration;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

const ZANI_HARDER_ARRAY_BENCHMARK_6047: &str =
    include_str!("../../../benchmarks/smt/chc_dt_array_zani_harder.smt2");

#[test]
#[timeout(120_000)]
fn adaptive_zani_harder_array_benchmark_is_safe_6047() {
    let problem = ChcParser::parse(ZANI_HARDER_ARRAY_BENCHMARK_6047)
        .expect("chc_dt_array_zani_harder benchmark should parse");
    problem
        .validate()
        .expect("chc_dt_array_zani_harder benchmark should validate");

    // Debug builds are ~10x slower than release for CHC with bit-blasting.
    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(10)
    };

    let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::with_budget(budget, false));
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#6047: chc_dt_array_zani_harder.smt2 is safe (z3 returns sat). \
         AdaptivePortfolio returned {result:?}."
    );
}
