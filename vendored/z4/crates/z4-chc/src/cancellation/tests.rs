// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::thread;

#[test]
fn test_initial_state() {
    let token = CancellationToken::new();
    assert!(!token.is_cancelled());
}

#[test]
fn test_cancel() {
    let token = CancellationToken::new();
    token.cancel();
    assert!(token.is_cancelled());
}

#[test]
fn test_clone_shares_state() {
    let token1 = CancellationToken::new();
    let token2 = token1.clone();

    assert!(!token1.is_cancelled());
    assert!(!token2.is_cancelled());

    token1.cancel();

    assert!(token1.is_cancelled());
    assert!(token2.is_cancelled());
}

#[test]
fn test_reset() {
    let token = CancellationToken::new();
    token.cancel();
    assert!(token.is_cancelled());
    token.reset();
    assert!(!token.is_cancelled());
}

#[test]
fn test_cross_thread_cancellation() {
    let token = CancellationToken::new();
    let thread_token = token.clone();

    let handle = thread::spawn(move || {
        // Simulate engine polling
        while !thread_token.is_cancelled() {
            thread::yield_now();
        }
        true // Returned because of cancellation
    });

    // Small delay to let thread start polling
    thread::sleep(std::time::Duration::from_millis(10));

    // Cancel from main thread
    token.cancel();

    // Thread should exit due to cancellation
    let result = handle.join().unwrap();
    assert!(result);
}

/// Test that PDR responds to cancellation within a bounded time (#1005).
#[test]
fn test_pdr_cancellation_responsiveness() {
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use std::time::{Duration, Instant};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 1000 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1000))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 1000 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1000))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    let thread_token = token.clone();

    let config = PdrConfig {
        max_frames: 100,
        max_iterations: 10000,
        max_obligations: 100000,
        verbose: false,
        cancellation_token: Some(thread_token),
        ..PdrConfig::default()
    };

    let start = Instant::now();
    let handle = thread::spawn(move || {
        let mut solver = PdrSolver::new(problem, config);
        solver.solve()
    });

    thread::sleep(Duration::from_millis(100));
    token.cancel();

    let result = handle.join().unwrap();
    let elapsed = start.elapsed();

    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    assert!(
        elapsed < Duration::from_secs(10),
        "PDR took {elapsed:?} to respond to cancellation (expected < 10s)"
    );
    // Either Unknown (cancelled) or Safe (solved quickly) is acceptable.
    assert!(
        matches!(result, PdrResult::Unknown | PdrResult::Safe(_)),
        "PDR returned unexpected result: {result:?}"
    );
}

/// Test that BMC responds to cancellation within a bounded time (#1005).
#[test]
fn test_bmc_cancellation_responsiveness() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::engine_result::ChcEngineResult;
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use std::time::{Duration, Instant};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    let thread_token = token.clone();

    let config = BmcConfig::with_engine_config(1000, false, Some(thread_token));

    let start = Instant::now();
    let handle = thread::spawn(move || {
        let solver = BmcSolver::new(problem, config);
        solver.solve()
    });

    thread::sleep(Duration::from_millis(100));
    token.cancel();

    let result = handle.join().unwrap();
    let elapsed = start.elapsed();

    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    assert!(
        elapsed < Duration::from_secs(10),
        "BMC took {elapsed:?} to respond to cancellation (expected < 10s)"
    );
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "BMC should return Unknown on cancellation, got {result:?}"
    );
}

/// Test that PDKIND responds to cancellation within a bounded time (#1005).
#[test]
fn test_pdkind_cancellation_responsiveness() {
    use crate::engine_config::ChcEngineConfig;
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::pdkind::{PdkindConfig, PdkindResult, PdkindSolver};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use std::time::{Duration, Instant};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 1000 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1000))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 1000 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1000))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    let thread_token = token.clone();

    let config = PdkindConfig {
        base: ChcEngineConfig {
            verbose: false,
            cancellation_token: Some(thread_token),
        },
        max_iterations: 1000,
        ..PdkindConfig::default()
    };

    let start = Instant::now();
    let handle = thread::spawn(move || {
        let solver = PdkindSolver::new(problem, config);
        solver.solve()
    });

    thread::sleep(Duration::from_millis(100));
    token.cancel();

    let result = handle.join().unwrap();
    let elapsed = start.elapsed();

    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    // Raised from 10s to 20s: debug-mode builds under heavy parallel load
    // (6+ concurrent test processes) can take >10s for PDKIND cancellation.
    assert!(
        elapsed < Duration::from_secs(20),
        "PDKIND took {elapsed:?} to respond to cancellation (expected < 20s)"
    );
    // Either Unknown (cancelled) or Safe (solved quickly) is acceptable.
    assert!(
        matches!(result, PdkindResult::Unknown | PdkindResult::Safe(_)),
        "PDKIND returned unexpected result: {result:?}"
    );
}
