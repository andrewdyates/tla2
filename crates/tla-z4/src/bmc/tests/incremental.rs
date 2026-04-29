// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for incremental BMC loop. Part of #3724.

use super::*;
use crate::bmc::incremental::{IncrementalBmc, IncrementalBmcResult};

/// Helper: build `count = 0` expression.
fn make_init_count_eq(val: i64) -> Spanned<Expr> {
    spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(val)))),
    ))
}

/// Helper: build `count' = count + 1` expression.
fn make_next_count_inc() -> Spanned<Expr> {
    spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "count".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    ))
}

/// Helper: build `count <= limit` expression.
fn make_safety_count_leq(limit: i64) -> Spanned<Expr> {
    spanned(Expr::Leq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(limit)))),
    ))
}

/// Incremental BMC finds the same counterexample as non-incremental.
///
/// Spec: Init == count = 0, Next == count' = count + 1, Inv == count <= 5.
/// Violation at step 6 (count = 6 > 5).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_finds_counterexample() {
    let max_k = 10;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(5);

    let result = bmc.run(&init, &next, &safety).expect("should run");

    match result {
        IncrementalBmcResult::Counterexample { depth, trace } => {
            assert_eq!(depth, 6, "violation should be found at depth 6");
            // Trace should have 7 states (steps 0..=6).
            assert_eq!(trace.len(), 7, "trace should have 7 states");
            // Verify count at violation step.
            let last = &trace[6];
            assert_eq!(last.step, 6);
            match last.assignments.get("count") {
                Some(BmcValue::Int(v)) => assert_eq!(*v, 6, "count at step 6 should be 6"),
                other => panic!("expected Int(6), got {other:?}"),
            }
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// Incremental BMC correctly reports Safe when no violation exists.
///
/// Spec: Init == count = 0, Next == count' = count + 1, Inv == count <= 20.
/// With max_k=10, count never exceeds 10, so safety holds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_reports_safe() {
    let max_k = 10;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(20);

    let result = bmc.run(&init, &next, &safety).expect("should run");

    match result {
        IncrementalBmcResult::Safe { max_depth } => {
            assert_eq!(max_depth, 10, "should check all 10 depths");
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Incremental BMC detects Init violation at depth 0.
///
/// Spec: Init == count = 10, Next == count' = count, Inv == count <= 5.
/// Init itself violates the invariant.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_init_violation() {
    let max_k = 5;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(10);
    // Next: count' = count (stuttering)
    let next = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let safety = make_safety_count_leq(5);

    let result = bmc.run(&init, &next, &safety).expect("should run");

    match result {
        IncrementalBmcResult::Counterexample { depth, trace } => {
            assert_eq!(depth, 0, "violation should be found at depth 0 (Init)");
            assert_eq!(trace.len(), 1, "trace should have 1 state");
            assert_eq!(trace[0].step, 0);
        }
        other => panic!("expected Counterexample at depth 0, got {other:?}"),
    }
}

/// Incremental BMC with k=0 and no violation.
///
/// Spec: Init == count = 0, Inv == count <= 5.
/// With max_k=0, only Init is checked, and it satisfies the invariant.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_k0_safe() {
    let max_k = 0;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(5);

    let result = bmc.run(&init, &next, &safety).expect("should run");

    match result {
        IncrementalBmcResult::Safe { max_depth } => {
            assert_eq!(max_depth, 0);
        }
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Verify incremental matches non-incremental counterexample.
///
/// Both approaches should find the same violation step for the same spec.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_matches_non_incremental() {
    let k = 10;

    // --- Non-incremental (existing approach) ---
    let mut trans = BmcTranslator::new(k).expect("should create");
    trans
        .declare_var("count", TlaSort::Int)
        .expect("should declare");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(5);

    let init_term = trans.translate_init(&init).expect("translate init");
    trans.assert(init_term);

    for step in 0..k {
        let next_term = trans.translate_next(&next, step).expect("translate next");
        trans.assert(next_term);
    }

    let not_safety = trans
        .translate_not_safety_all_steps(&safety, k)
        .expect("translate safety");
    trans.assert(not_safety);

    let non_incremental_result = trans.check_sat();
    let non_incremental_violation = match non_incremental_result {
        SolveResult::Sat => {
            let model = trans.get_model().expect("model");
            let trace = trans.extract_trace(&model);
            trace
                .iter()
                .find(|s| matches!(s.assignments.get("count"), Some(BmcValue::Int(v)) if *v > 5))
                .map(|s| s.step)
        }
        _ => panic!("non-incremental should find violation"),
    };

    // --- Incremental ---
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(k, &vars).expect("should create");
    let incremental_result = bmc.run(&init, &next, &safety).expect("should run");

    let incremental_violation = match incremental_result {
        IncrementalBmcResult::Counterexample { depth, .. } => Some(depth),
        _ => panic!("incremental should find violation"),
    };

    assert_eq!(
        non_incremental_violation, incremental_violation,
        "both approaches should find violation at the same step"
    );
}

/// Incremental BMC with two variables and UNCHANGED.
///
/// Spec: Init == x = 1 /\ y = 0
///       Next == x' = x + 1 /\ y' = y
///       Inv  == x + y <= 10
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_two_vars() {
    let max_k = 15;
    let vars = vec![
        ("x".to_string(), TlaSort::Int),
        ("y".to_string(), TlaSort::Int),
    ];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    // Init: x = 1 /\ y = 0
    let init = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));

    // Next: x' = x + 1 /\ y' = y
    let next = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )))))),
            Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )))))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));

    // Safety: x + y <= 10
    let safety = spanned(Expr::Leq(
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));

    let result = bmc.run(&init, &next, &safety).expect("should run");

    match result {
        IncrementalBmcResult::Counterexample { depth, trace } => {
            // x starts at 1, increments by 1. y stays 0.
            // x + y > 10 when x = 11, which is at step 10 (x goes 1,2,...,11).
            assert_eq!(depth, 10, "violation at step 10 where x=11, y=0");
            assert_eq!(trace.len(), 11, "trace should have 11 states (0..=10)");

            // Verify the violation state.
            let last = &trace[10];
            match (last.assignments.get("x"), last.assignments.get("y")) {
                (Some(BmcValue::Int(x)), Some(BmcValue::Int(y))) => {
                    assert_eq!(*x, 11, "x should be 11 at step 10");
                    assert_eq!(*y, 0, "y should be 0 at step 10");
                }
                other => panic!("expected Int values, got {other:?}"),
            }
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// run_all_steps detects Init violation the same as run.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_run_all_steps_init_violation() {
    let max_k = 5;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(10);
    let next = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let safety = make_safety_count_leq(5);

    let result = bmc
        .run_all_steps(&init, &next, &safety)
        .expect("should run");

    match result {
        IncrementalBmcResult::Counterexample { depth, .. } => {
            assert_eq!(depth, 0, "Init violation found at depth 0");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// run_all_steps finds same violation depth as run for monotonic counter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_run_all_steps_matches_run() {
    let max_k = 10;

    // Run with frontier-only check.
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc1 = IncrementalBmc::new(max_k, &vars).expect("should create");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(5);

    let result1 = bmc1.run(&init, &next, &safety).expect("should run");

    // Run with all-steps check.
    let mut bmc2 = IncrementalBmc::new(max_k, &vars).expect("should create");
    let result2 = bmc2
        .run_all_steps(&init, &next, &safety)
        .expect("should run");

    let depth1 = match result1 {
        IncrementalBmcResult::Counterexample { depth, .. } => depth,
        other => panic!("expected Counterexample from run, got {other:?}"),
    };
    let depth2 = match result2 {
        IncrementalBmcResult::Counterexample { depth, .. } => depth,
        other => panic!("expected Counterexample from run_all_steps, got {other:?}"),
    };

    // For a monotonically increasing counter, both should find the violation
    // at the same depth (the first step where count > 5).
    assert_eq!(
        depth1, depth2,
        "both strategies should find the same violation depth"
    );
}

/// current_depth tracks progress correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_incremental_bmc_current_depth() {
    let max_k = 3;
    let vars = vec![("count".to_string(), TlaSort::Int)];
    let mut bmc = IncrementalBmc::new(max_k, &vars).expect("should create");

    assert_eq!(bmc.current_depth(), 0, "initial depth is 0");

    let init = make_init_count_eq(0);
    let next = make_next_count_inc();
    let safety = make_safety_count_leq(100); // Never violates within bound.

    let result = bmc.run(&init, &next, &safety).expect("should run");
    assert!(matches!(result, IncrementalBmcResult::Safe { .. }));
    assert_eq!(
        bmc.current_depth(),
        max_k,
        "after full run, depth should be max_k"
    );
}
