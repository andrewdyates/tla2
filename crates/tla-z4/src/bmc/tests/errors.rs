// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test bounds validation - k > MAX_BMC_BOUND should error
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_bounds_validation() {
    use crate::error::MAX_BMC_BOUND;

    // Should succeed with MAX_BMC_BOUND
    assert!(BmcTranslator::new(MAX_BMC_BOUND).is_ok());

    // Should fail with MAX_BMC_BOUND + 1
    let result = BmcTranslator::new(MAX_BMC_BOUND + 1);
    match result {
        Err(Z4Error::BmcBoundTooLarge { bound, max }) => {
            assert_eq!(bound, MAX_BMC_BOUND + 1);
            assert_eq!(max, MAX_BMC_BOUND);
        }
        Ok(_) => panic!("expected BmcBoundTooLarge error, got Ok"),
        Err(other) => panic!("expected BmcBoundTooLarge, got {other:?}"),
    }
}

/// Test error path: unknown variable
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_unknown_variable_error() {
    let k = 2;
    let mut trans = BmcTranslator::new(k).unwrap();

    // Don't declare "x" - it's unknown

    // Try to translate an expression using unknown variable
    let expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let result = trans.translate_init(&expr);
    match result {
        Err(Z4Error::UnknownVariable(msg)) => {
            assert!(msg.contains('x'), "error should mention variable name");
        }
        Ok(_) => panic!("expected UnknownVariable error, got Ok"),
        Err(other) => panic!("expected UnknownVariable, got {other:?}"),
    }
}

/// Test error path: step exceeds bound
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_step_exceeds_bound_error() {
    let k = 2;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Try to translate Next at step k (which would need step k+1)
    let next = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let result = trans.translate_next(&next, k);
    match result {
        Err(Z4Error::UntranslatableExpr(msg)) => {
            assert!(
                msg.contains("exceed") || msg.contains("bound"),
                "error should mention bound: {msg}"
            );
        }
        Ok(_) => panic!("expected UntranslatableExpr error, got Ok"),
        Err(other) => panic!("expected UntranslatableExpr, got {other:?}"),
    }
}

/// Test error path: get_var_at_step with step > bound
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_get_var_step_exceeds_bound() {
    let k = 2;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Try to get variable at step k+1
    let result = trans.get_var_at_step("x", k + 1);
    match result {
        Err(Z4Error::UntranslatableExpr(msg)) => {
            assert!(
                msg.contains("exceed") || msg.contains("bound"),
                "error should mention bound: {msg}"
            );
        }
        Ok(_) => panic!("expected UntranslatableExpr error, got Ok"),
        Err(other) => panic!("expected UntranslatableExpr, got {other:?}"),
    }
}

/// Test error path: UNCHANGED on unsupported expression type
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_unchanged_unsupported_expr_error() {
    let k = 1;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Try UNCHANGED on an addition expression (not Ident or Tuple)
    let unchanged = spanned(Expr::Unchanged(Box::new(spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    )))));

    let result = trans.translate_next(&unchanged, 0);
    match result {
        Err(Z4Error::UntranslatableExpr(msg)) => {
            assert!(
                msg.contains("UNCHANGED") && msg.contains("variable"),
                "error should mention UNCHANGED and variable: {msg}"
            );
        }
        Ok(_) => panic!("expected UntranslatableExpr error, got Ok"),
        Err(other) => panic!("expected UntranslatableExpr, got {other:?}"),
    }
}

/// Test error path: membership in unsupported set type
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_membership_unsupported_set_error() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Try x \in Nat (Nat is just an Ident, not BOOLEAN)
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "Nat".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let result = trans.translate_init(&membership);
    match result {
        Err(Z4Error::UntranslatableExpr(msg)) => {
            assert!(
                msg.contains("membership"),
                "error should mention membership: {msg}"
            );
        }
        Ok(_) => panic!("expected UntranslatableExpr error, got Ok"),
        Err(other) => panic!("expected UntranslatableExpr, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_try_check_sat_zero_timeout_reports_timeout_reason() {
    use std::time::Duration;

    let mut trans = BmcTranslator::new(0).unwrap();
    trans.set_timeout(Some(Duration::ZERO));

    assert_eq!(trans.get_timeout(), Some(Duration::ZERO));
    assert_eq!(trans.try_check_sat().unwrap(), SolveResult::Unknown);
    assert_eq!(
        trans.last_unknown_reason(),
        Some(crate::UnknownReason::Timeout)
    );
}
