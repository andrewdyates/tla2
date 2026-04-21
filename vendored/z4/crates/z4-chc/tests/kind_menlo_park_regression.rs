// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

use ntest::timeout;
use std::time::Duration;
use z4_chc::{testing, ChcParser, KindConfig, KindResult};

/// Regression test for #1362 / #7371: KIND must prove `menlo_park_term_simpl_2`
/// safe after an incremental base-case false result at k=0.
///
/// The benchmark's k=0 base case includes mod-elimination auxiliaries and can
/// produce a spurious incremental failure. The solver must retry the base case
/// with a fresh SMT context so the later backward-induction proof is not
/// poisoned by an incorrect "base case incomplete" state.
#[test]
#[cfg_attr(debug_assertions, timeout(45_000))]
#[cfg_attr(not(debug_assertions), timeout(25_000))]
fn test_kind_issue_1362_menlo_park_base_case_fresh_retry() {
    let problem = ChcParser::parse(include_str!(
        "../../../benchmarks/chc-comp/2025/extra-small-lia/menlo_park_term_simpl_2_000.smt2"
    ))
    .expect("parse menlo_park_term_simpl_2 benchmark");
    let config = KindConfig::with_engine_config(
        20,
        Duration::from_secs(2),
        Duration::from_secs(15),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Safe(_) => {}
        KindResult::Unsafe(cex) => {
            panic!(
                "KIND regression (#1362): menlo_park_term_simpl_2 is SAT (safe), but KIND returned Unsafe at steps={}.",
                cex.steps.len()
            );
        }
        KindResult::Unknown => {
            panic!("KIND regression (#1362): menlo_park_term_simpl_2 should be Safe, got Unknown.");
        }
        KindResult::NotApplicable => {
            panic!(
                "KIND regression (#1362): menlo_park_term_simpl_2 is a single-predicate benchmark."
            );
        }
        _ => panic!("unexpected variant"),
    }
}
