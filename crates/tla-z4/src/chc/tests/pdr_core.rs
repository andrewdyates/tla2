// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::TlaSort;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_counter_safe() {
    // Simple counter: count starts at 0, increments, stays <= 5
    // Init: count = 0
    // Next: count' = count + 1 /\ count < 5
    // Safety: count <= 5
    //
    // This is SAFE because count can only reach 5 (then transition is disabled)

    let mut trans = ChcTranslator::new(&[("count", TlaSort::Int)]).unwrap();

    // Init: count = 0
    let init = eq_expr(var_expr("count"), int_expr(0));
    trans.add_init(&init).unwrap();

    // Next: count < 5 /\ count' = count + 1
    let guard = lt_expr(var_expr("count"), int_expr(5));
    let update = eq_expr(
        prime_expr("count"),
        add_expr(var_expr("count"), int_expr(1)),
    );
    let next = and_expr(guard, update);
    trans.add_next(&next).unwrap();

    // Safety: count <= 5
    let safety = le_expr(var_expr("count"), int_expr(5));
    trans.add_safety(&safety).unwrap();

    // Solve
    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    // Should be Safe
    match result {
        PdrCheckResult::Safe { .. } => {
            // Expected
        }
        PdrCheckResult::Unknown { .. } => {
            // Acceptable for skeleton PDR
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown, got Unsafe for safe spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_counter_unsafe() {
    // Counter that grows unboundedly but claims count <= 5
    // Init: count = 0
    // Next: count' = count + 1 (no guard)
    // Safety: count <= 5
    //
    // This is UNSAFE because count eventually exceeds 5

    let mut trans = ChcTranslator::new(&[("count", TlaSort::Int)]).unwrap();

    // Init: count = 0
    let init = eq_expr(var_expr("count"), int_expr(0));
    trans.add_init(&init).unwrap();

    // Next: count' = count + 1
    let next = eq_expr(
        prime_expr("count"),
        add_expr(var_expr("count"), int_expr(1)),
    );
    trans.add_next(&next).unwrap();

    // Safety: count <= 5
    let safety = le_expr(var_expr("count"), int_expr(5));
    trans.add_safety(&safety).unwrap();

    // Solve
    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    // Should be Unsafe (or Unknown if PDR can't prove it)
    match result {
        PdrCheckResult::Unsafe { trace } => {
            // Expected: found counterexample
            // Trace should show count going from 0 to 6
            assert!(!trace.is_empty(), "counterexample should have states");
        }
        PdrCheckResult::Unknown { .. } => {
            // Acceptable: PDR may not find the counterexample in limited iterations
        }
        PdrCheckResult::Safe { .. } => {
            panic!("Expected Unsafe or Unknown, got Safe for unsafe spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_two_variables() {
    // Two-variable spec: x increments, y = 2*x, invariant y >= 0
    // Init: x = 0 /\ y = 0
    // Next: x' = x + 1 /\ y' = y + 2
    // Safety: y >= 0
    //
    // This is SAFE: y starts at 0 and only increases

    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("y", TlaSort::Int)]).unwrap();

    // Init: x = 0 /\ y = 0
    let init = and_expr(
        eq_expr(var_expr("x"), int_expr(0)),
        eq_expr(var_expr("y"), int_expr(0)),
    );
    trans.add_init(&init).unwrap();

    // Next: x' = x + 1 /\ y' = y + 2
    let next = and_expr(
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        eq_expr(prime_expr("y"), add_expr(var_expr("y"), int_expr(2))),
    );
    trans.add_next(&next).unwrap();

    // Safety: y >= 0
    let safety = Spanned::dummy(Expr::Geq(Box::new(var_expr("y")), Box::new(int_expr(0))));
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {
            // Expected
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown, got Unsafe for safe spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disjunctive_next() {
    // Spec with disjunctive Next (two actions)
    // Init: x = 0
    // Next: (x < 5 /\ x' = x + 1) \/ (x >= 5 /\ x' = x)  (saturates at 5)
    // Safety: x <= 10
    //
    // This is SAFE: x can reach at most 5

    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();

    // Init: x = 0
    let init = eq_expr(var_expr("x"), int_expr(0));
    trans.add_init(&init).unwrap();

    // Action 1: x < 5 /\ x' = x + 1
    let action1 = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );

    // Action 2: x >= 5 /\ x' = x (saturate)
    let action2 = and_expr(
        Spanned::dummy(Expr::Geq(Box::new(var_expr("x")), Box::new(int_expr(5)))),
        eq_expr(prime_expr("x"), var_expr("x")),
    );

    // Next: Action1 \/ Action2
    let next = or_expr(action1, action2);
    trans.add_next(&next).unwrap();

    // Safety: x <= 10
    let safety = le_expr(var_expr("x"), int_expr(10));
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {
            // Expected
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown, got Unsafe for safe spec");
        }
    }
}
