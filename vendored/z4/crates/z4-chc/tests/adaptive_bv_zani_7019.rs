// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression guard for #7019's remaining zani BV lane.
//!
//! `chc_bv64_simple_zani.smt2` used to abort inside Farkas linear parsing when
//! BV64 constants were lowered into large Rational64 coefficients. The adaptive
//! entrypoint must now return a verified Safe result instead of crashing.

use ntest::timeout;
use std::time::Duration;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

const BV64_SIMPLE_ZANI_BENCHMARK_7019: &str =
    include_str!("../../../benchmarks/smt/chc_bv64_simple_zani.smt2");

#[test]
#[timeout(120_000)]
fn adaptive_bv64_simple_zani_benchmark_is_safe_7019() {
    let problem = ChcParser::parse(BV64_SIMPLE_ZANI_BENCHMARK_7019).unwrap_or_else(|err| {
        panic!("chc_bv64_simple_zani.smt2 should parse: {err}");
    });
    problem
        .validate()
        .unwrap_or_else(|err| panic!("chc_bv64_simple_zani.smt2 should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(10)
    };

    let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::with_budget(budget, false));
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#7019: chc_bv64_simple_zani.smt2 is safe (z3 returns sat). \
         AdaptivePortfolio returned {result:?}."
    );
}
