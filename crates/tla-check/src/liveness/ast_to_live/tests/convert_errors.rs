// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error path tests (#126): non-boolean constants, unsupported temporal, display formatting
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_non_boolean_constant_int() {
    // Converting an integer constant should produce NonBooleanConstant error
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // Just the integer 42 (not a boolean)
    let expr = spanned(Expr::Int(BigInt::from(42)));
    let result = conv.convert(&ctx, &expr);

    match result {
        Err(ConvertError::NonBooleanConstant(_)) => {
            // Expected error
        }
        Ok(_) => panic!("Expected NonBooleanConstant error, got Ok"),
        Err(other) => panic!("Expected NonBooleanConstant error, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_non_boolean_constant_string() {
    // Converting a string constant should produce NonBooleanConstant error
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::String("hello".to_string()));
    let result = conv.convert(&ctx, &expr);

    match result {
        Err(ConvertError::NonBooleanConstant(_)) => {
            // Expected error
        }
        Ok(_) => panic!("Expected NonBooleanConstant error, got Ok"),
        Err(other) => panic!("Expected NonBooleanConstant error, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_non_boolean_constant_set() {
    // Converting a set constant should produce NonBooleanConstant error
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // {1, 2, 3} - a set of integers
    let expr = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let result = conv.convert(&ctx, &expr);

    match result {
        Err(ConvertError::NonBooleanConstant(_)) => {
            // Expected error
        }
        Ok(_) => panic!("Expected NonBooleanConstant error, got Ok"),
        Err(other) => panic!("Expected NonBooleanConstant error, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_display_non_boolean() {
    // Verify error Display formatting
    let expr = Arc::new(spanned(Expr::Int(BigInt::from(42))));
    let err = ConvertError::NonBooleanConstant(expr);
    let msg = format!("{}", err);
    assert!(msg.contains("Expected boolean constant"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_display_unsupported_temporal() {
    // Verify error Display formatting for unsupported temporal
    let expr = Arc::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))));
    let err = ConvertError::UnsupportedTemporal(expr);
    let msg = format!("{}", err);
    assert!(msg.contains("Unsupported temporal expression"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_display_cannot_handle_formula() {
    let expr = Arc::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))));
    let err = ConvertError::CannotHandleFormula {
        original: expr,
        location_module_name: Some(Arc::<str>::from("Test")),
        reason: Some("because reasons".to_string()),
    };
    assert_eq!(
        format!("{}", err),
        "TLC cannot handle the temporal formula bytes 0-0 of module Test:\nbecause reasons"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_display_cannot_handle_formula_no_reason() {
    let expr = Arc::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))));
    let err = ConvertError::CannotHandleFormula {
        original: expr,
        location_module_name: Some(Arc::<str>::from("Test")),
        reason: None,
    };
    assert_eq!(
        format!("{}", err),
        "TLC cannot handle the temporal formula bytes 0-0 of module Test"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_error_display_cannot_handle_formula_unknown_module() {
    let expr = Arc::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))));
    let err = ConvertError::CannotHandleFormula {
        original: expr,
        location_module_name: None,
        reason: None,
    };
    assert_eq!(
        format!("{}", err),
        "TLC cannot handle the temporal formula bytes 0-0 of module <unknown>"
    );
}
