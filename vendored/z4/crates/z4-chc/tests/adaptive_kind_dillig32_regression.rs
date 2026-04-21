// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

use ntest::timeout;
use std::time::Duration;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

const DILLIG32_BENCHMARK: &str =
    include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig32_000.smt2");

/// Regression guard for #7598 / #5970.
///
/// `dillig32` is a pure-LIA simple loop that should solve within the adaptive
/// budget. KIND can time out on the hardened path, so adaptive must give the
/// focused PDR fallback a chance to return the verified `Safe` result instead
/// of spending the whole budget in the broad simple-loop portfolio.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(40_000))]
fn test_adaptive_kind_accepts_dillig32_k_inductive_safe() {
    let problem = ChcParser::parse(DILLIG32_BENCHMARK)
        .unwrap_or_else(|err| panic!("dillig32 benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("dillig32 benchmark should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(20)
    };

    let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::with_budget(budget, false));
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#7598 regression: dillig32_000.smt2 is safe, but AdaptivePortfolio returned {result:?}"
    );
}
