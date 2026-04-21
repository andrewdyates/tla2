// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::*;
use super::*;
use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::Z4Error;
use crate::TlaSort;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chc_translator_creation() {
    let trans = ChcTranslator::new(&[("x", TlaSort::Int), ("y", TlaSort::Bool)]);
    assert!(trans.is_ok());

    let trans = trans.unwrap();
    assert!(trans.vars.contains_key("x"));
    assert!(trans.vars.contains_key("y"));
    assert!(trans.next_vars.contains_key("x"));
    assert!(trans.next_vars.contains_key("y"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chc_translator_empty_state_vars_supported() {
    let mut trans = ChcTranslator::new(&[]).unwrap();
    trans.add_init(&Spanned::dummy(Expr::Bool(true))).unwrap();
    trans.add_next(&Spanned::dummy(Expr::Bool(true))).unwrap();
    trans.add_safety(&Spanned::dummy(Expr::Bool(true))).unwrap();

    let result = trans.solve_pdr(pdr_config(5, 50)).unwrap();

    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chc_translator_integer_overflow() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();

    let too_big = BigInt::from(i128::MAX);
    let too_big_expr = Spanned::dummy(Expr::Int(too_big));
    let init = eq_expr(var_expr("x"), too_big_expr);

    let err = trans.add_init(&init).unwrap_err();
    match err {
        Z4Error::IntegerOverflow(_) => {}
        other => panic!("Expected Z4Error::IntegerOverflow, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_primed_var_error_in_init() {
    // Primed variables should not be allowed in Init
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();

    let bad_init = eq_expr(prime_expr("x"), int_expr(0));
    let result = trans.add_init(&bad_init);

    assert!(result.is_err());
    match result {
        Err(Z4Error::UntranslatableExpr(msg)) => {
            assert!(msg.contains("primed"));
        }
        _ => panic!("Expected UntranslatableExpr error"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_primed_var_error_in_safety() {
    // Primed variables should not be allowed in Safety
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();

    // Need to add init first to build the problem
    let init = eq_expr(var_expr("x"), int_expr(0));
    trans.add_init(&init).unwrap();

    let bad_safety = le_expr(prime_expr("x"), int_expr(5));
    let result = trans.add_safety(&bad_safety);

    assert!(result.is_err());
}
