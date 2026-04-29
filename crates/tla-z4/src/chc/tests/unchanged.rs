// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::TlaSort;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_single_var() {
    // Test UNCHANGED with a single variable
    // Init: x = 0 /\ y = 0
    // Next: x' = x + 1 /\ UNCHANGED y
    // Safety: y = 0

    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("y", TlaSort::Int)]).unwrap();

    // Init: x = 0 /\ y = 0
    let init = and_expr(
        eq_expr(var_expr("x"), int_expr(0)),
        eq_expr(var_expr("y"), int_expr(0)),
    );
    trans.add_init(&init).unwrap();

    // Next: x' = x + 1 /\ UNCHANGED y
    let x_update = eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1)));
    let y_unchanged = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("y"))));
    let next = and_expr(x_update, y_unchanged);
    trans.add_next(&next).unwrap();

    // Safety: y = 0
    let safety = eq_expr(var_expr("y"), int_expr(0));
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    // Should be Safe (y is never modified)
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {
            // Expected
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown, got Unsafe for UNCHANGED spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_tuple() {
    // Test UNCHANGED with a tuple of variables
    // Init: x = 0 /\ y = 0 /\ z = 0
    // Next: x' = x + 1 /\ UNCHANGED <<y, z>>
    // Safety: y = 0 /\ z = 0

    let mut trans = ChcTranslator::new(&[
        ("x", TlaSort::Int),
        ("y", TlaSort::Int),
        ("z", TlaSort::Int),
    ])
    .unwrap();

    // Init: x = 0 /\ y = 0 /\ z = 0
    let init = and_expr(
        and_expr(
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(0)),
        ),
        eq_expr(var_expr("z"), int_expr(0)),
    );
    trans.add_init(&init).unwrap();

    // Next: x' = x + 1 /\ UNCHANGED <<y, z>>
    let x_update = eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1)));
    let yz_tuple = Spanned::dummy(Expr::Tuple(vec![var_expr("y"), var_expr("z")]));
    let yz_unchanged = Spanned::dummy(Expr::Unchanged(Box::new(yz_tuple)));
    let next = and_expr(x_update, yz_unchanged);
    trans.add_next(&next).unwrap();

    // Safety: y = 0 /\ z = 0
    let safety = and_expr(
        eq_expr(var_expr("y"), int_expr(0)),
        eq_expr(var_expr("z"), int_expr(0)),
    );
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_test_config()).unwrap();

    // Should be Safe (y, z are never modified)
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {
            // Expected
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown, got Unsafe for UNCHANGED tuple spec");
        }
    }
}
