// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core JIT compiler tests: arithmetic, comparisons, boolean logic,
//! control flow, power, and overflow detection.

use super::*;
use crate::error::JitError;
use crate::jit_native::{Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName};
use cranelift_frontend::FunctionBuilder;
use num_bigint::BigInt;
use tla_core::span::Span;

/// Compile an expression bypassing the preflight validator.
///
/// This is needed for testing lowering-level bounds checks that the preflight
/// would otherwise reject (e.g., function application on out-of-domain args).
fn compile_expr_no_preflight(
    jit: &mut JitContext,
    expr: &Spanned<Expr>,
) -> Result<fn() -> i64, JitError> {
    let mut sig = jit.module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));

    let func_name = format!("expr_{}", jit.func_counter);
    jit.func_counter += 1;
    let func_id = jit
        .module
        .declare_function(&func_name, Linkage::Local, &sig)?;

    jit.ctx.func.signature = sig;
    jit.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

    {
        let mut builder = FunctionBuilder::new(&mut jit.ctx.func, &mut jit.builder_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let value = compile_expr_inner(&mut builder, expr)?;
        builder.ins().return_(&[value]);
        builder.finalize();
    }

    jit.module
        .define_function(func_id, &mut jit.ctx)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    jit.module.clear_context(&mut jit.ctx);
    jit.module
        .finalize_definitions()
        .map_err(|e| JitError::CompileError(format!("Failed to finalize: {e}")))?;

    let code_ptr = jit.module.get_finalized_function(func_id);
    // SAFETY: See JitContext::compile_expr for the full safety argument.
    // Same invariants hold: Cranelift C ABI, () -> I64 signature, valid code ptr.
    let func: fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    Ok(func)
}

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, Span::default())
}

fn num(n: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(n)))
}

fn add(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Add(Box::new(left), Box::new(right)))
}

fn sub(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Sub(Box::new(left), Box::new(right)))
}

fn mul(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Mul(Box::new(left), Box::new(right)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_integer_constant() {
    let mut jit = JitContext::new().unwrap();
    let expr = num(42);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negative_constant() {
    let mut jit = JitContext::new().unwrap();
    let expr = num(-17);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), -17);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_addition() {
    let mut jit = JitContext::new().unwrap();
    let expr = add(num(2), num(3));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 5);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subtraction() {
    let mut jit = JitContext::new().unwrap();
    let expr = sub(num(10), num(3));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multiplication() {
    let mut jit = JitContext::new().unwrap();
    let expr = mul(num(6), num(7));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_arithmetic() {
    let mut jit = JitContext::new().unwrap();
    // 2 + 3 * 4 = 2 + 12 = 14 (note: we're building the AST, not parsing)
    let mul_expr = mul(num(3), num(4));
    let expr = add(num(2), mul_expr);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 14);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_complex_expression() {
    let mut jit = JitContext::new().unwrap();
    // (10 - 3) * (2 + 4) = 7 * 6 = 42
    let left = sub(num(10), num(3));
    let right = add(num(2), num(4));
    let expr = mul(left, right);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_comparison_gt() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Gt(Box::new(num(5)), Box::new(num(3))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::Gt(Box::new(num(3)), Box::new(num(5))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_comparison_eq() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Eq(Box::new(num(5)), Box::new(num(5))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::Eq(Box::new(num(5)), Box::new(num(3))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_and() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(true))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::And(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_or() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Or(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(spanned(Expr::Bool(true))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::Or(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_not() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Bool(true)))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);

    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Bool(false)))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negation() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Neg(Box::new(num(42))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), -42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_then_else() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::If(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(num(42)),
        Box::new(num(0)),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);

    let expr = spanned(Expr::If(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(num(42)),
        Box::new(num(0)),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_implies() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Implies(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(spanned(Expr::Bool(true))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::Implies(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equiv() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Equiv(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(true))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);

    let expr = spanned(Expr::Equiv(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);

    let expr = spanned(Expr::Equiv(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_power() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(0))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 1, "2^0");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(1))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "2^1");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(2))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 4, "2^2");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(3))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 8, "2^3");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(4))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 16, "2^4");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(5))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 32, "2^5");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(6))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 64, "2^6");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(7))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 128, "2^7");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(8))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 256, "2^8");
    let expr = spanned(Expr::Pow(Box::new(num(3)), Box::new(num(2))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 9, "3^2");
    let expr = spanned(Expr::Pow(Box::new(num(3)), Box::new(num(4))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 81, "3^4");
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(9))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 512, "2^9");
    let expr = spanned(Expr::Pow(Box::new(num(1)), Box::new(num(32))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 1, "1^32");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_power_negative_exponent_is_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Pow(Box::new(num(2)), Box::new(num(-1))));
    assert!(jit.compile_expr(&expr).is_err(), "2^-1 should fall back");
}

// =========================================================================
// Overflow tests (Part of #746)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_addition_is_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = add(num(i64::MAX), num(1));
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_negation_is_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Neg(Box::new(num(i64::MIN))));
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_power_is_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Pow(Box::new(num(3_037_000_500)), Box::new(num(2))));
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_subtraction_positive_minus_negative() {
    let mut jit = JitContext::new().unwrap();
    let expr = sub(num(i64::MAX), num(-1));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "MAX - (-1) should overflow"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_subtraction_negative_minus_positive() {
    let mut jit = JitContext::new().unwrap();
    let expr = sub(num(i64::MIN), num(1));
    assert!(jit.compile_expr(&expr).is_err(), "MIN - 1 should underflow");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_multiplication() {
    let mut jit = JitContext::new().unwrap();
    let expr = mul(num(1 << 32), num(1 << 32));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "2^32 * 2^32 should overflow"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_multiplication_negative() {
    let mut jit = JitContext::new().unwrap();
    let expr = mul(num(i64::MIN / 2), num(3));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "(MIN/2) * 3 should overflow"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_division_min_by_neg_one() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::IntDiv(Box::new(num(i64::MIN)), Box::new(num(-1))));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "MIN \\div -1 should overflow"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_chain_of_operations() {
    let mut jit = JitContext::new().unwrap();
    let sub_expr = sub(num(i64::MAX), num(1));
    let expr = add(sub_expr, num(2));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "(MAX - 1) + 2 should overflow"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_overflow_at_boundary() {
    let mut jit = JitContext::new().unwrap();
    let expr = add(num(i64::MAX), num(0));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), i64::MAX);

    let expr = sub(num(i64::MIN), num(0));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), i64::MIN);

    let expr = mul(num(i64::MAX), num(1));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), i64::MAX);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_multiplication_min_times_neg_one() {
    let mut jit = JitContext::new().unwrap();
    let expr = mul(num(i64::MIN), num(-1));
    assert!(jit.compile_expr(&expr).is_err(), "MIN * -1 should overflow");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_overflow_error_message_contains_overflow() {
    let mut jit = JitContext::new().unwrap();
    let expr = add(num(i64::MAX), num(1));
    let err = jit.compile_expr(&expr).unwrap_err();
    match err {
        JitError::CompileError(msg) => {
            assert!(
                msg.contains("overflow"),
                "error message should mention overflow: {msg}"
            );
        }
        other => panic!("expected CompileError, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_predicate_position_requires_boolean_result() {
    let mut jit = JitContext::new().unwrap();
    let expr = num(2);
    assert!(matches!(
        jit.compile_predicate(&expr),
        Err(JitError::TypeMismatch { expected, actual })
            if expected == "boolean" && actual == "integer"
    ));

    let expr = spanned(Expr::Eq(Box::new(num(1)), Box::new(num(1))));
    assert_eq!(jit.compile_predicate(&expr).unwrap()(), 1);
}

// =========================================================================
// Set membership tests (Part of #3788)
// =========================================================================

fn set_enum(elements: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    spanned(Expr::SetEnum(elements))
}

fn member(elem: Spanned<Expr>, set: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::In(Box::new(elem), Box::new(set)))
}

fn not_member(elem: Spanned<Expr>, set: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::NotIn(Box::new(elem), Box::new(set)))
}

fn range(lo: Spanned<Expr>, hi: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Range(Box::new(lo), Box::new(hi)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_single_element_true() {
    let mut jit = JitContext::new().unwrap();
    // 5 \in {5}
    let expr = member(num(5), set_enum(vec![num(5)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_single_element_false() {
    let mut jit = JitContext::new().unwrap();
    // 3 \in {5}
    let expr = member(num(3), set_enum(vec![num(5)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_multiple_elements_first() {
    let mut jit = JitContext::new().unwrap();
    // 1 \in {1, 2, 3}
    let expr = member(num(1), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_multiple_elements_last() {
    let mut jit = JitContext::new().unwrap();
    // 3 \in {1, 2, 3}
    let expr = member(num(3), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_multiple_elements_middle() {
    let mut jit = JitContext::new().unwrap();
    // 2 \in {1, 2, 3}
    let expr = member(num(2), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_not_found() {
    let mut jit = JitContext::new().unwrap();
    // 7 \in {1, 2, 3}
    let expr = member(num(7), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_empty_set() {
    let mut jit = JitContext::new().unwrap();
    // 1 \in {}
    let expr = member(num(1), set_enum(vec![]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_negative_elements() {
    let mut jit = JitContext::new().unwrap();
    // -3 \in {-5, -3, 0, 3, 5}
    let expr = member(
        num(-3),
        set_enum(vec![num(-5), num(-3), num(0), num(3), num(5)]),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_computed_element() {
    let mut jit = JitContext::new().unwrap();
    // (2 + 3) \in {4, 5, 6}
    let expr = member(add(num(2), num(3)), set_enum(vec![num(4), num(5), num(6)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_true() {
    let mut jit = JitContext::new().unwrap();
    // 7 \notin {1, 2, 3}
    let expr = not_member(num(7), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_false() {
    let mut jit = JitContext::new().unwrap();
    // 2 \notin {1, 2, 3}
    let expr = not_member(num(2), set_enum(vec![num(1), num(2), num(3)]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_empty_set() {
    let mut jit = JitContext::new().unwrap();
    // 1 \notin {}
    let expr = not_member(num(1), set_enum(vec![]));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Range membership tests (Part of #3788)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range() {
    let mut jit = JitContext::new().unwrap();
    // 3 \in 1..5
    let expr = member(num(3), range(num(1), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_boundary_lo() {
    let mut jit = JitContext::new().unwrap();
    // 1 \in 1..5
    let expr = member(num(1), range(num(1), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_boundary_hi() {
    let mut jit = JitContext::new().unwrap();
    // 5 \in 1..5
    let expr = member(num(5), range(num(1), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_out_of_bounds() {
    let mut jit = JitContext::new().unwrap();
    // 0 \in 1..5
    let expr = member(num(0), range(num(1), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);

    // 6 \in 1..5
    let expr = member(num(6), range(num(1), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_empty_range() {
    let mut jit = JitContext::new().unwrap();
    // 1 \in 5..1 (empty range)
    let expr = member(num(1), range(num(5), num(1)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

// =========================================================================
// Quantifier tests (Part of #3788)
// =========================================================================

fn forall(var_name: &str, domain: Spanned<Expr>, body: Spanned<Expr>) -> Spanned<Expr> {
    use tla_core::ast::BoundVar;
    let bound = BoundVar {
        name: spanned(var_name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };
    spanned(Expr::Forall(vec![bound], Box::new(body)))
}

fn exists(var_name: &str, domain: Spanned<Expr>, body: Spanned<Expr>) -> Spanned<Expr> {
    use tla_core::ast::BoundVar;
    let bound = BoundVar {
        name: spanned(var_name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };
    spanned(Expr::Exists(vec![bound], Box::new(body)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_constant_true() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : TRUE
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3)]),
        spanned(Expr::Bool(true)),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_constant_false() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : FALSE
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3)]),
        spanned(Expr::Bool(false)),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_empty_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {} : FALSE  (vacuously true)
    let expr = forall("x", set_enum(vec![]), spanned(Expr::Bool(false)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_constant_true() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3} : TRUE
    let expr = exists(
        "x",
        set_enum(vec![num(1), num(2), num(3)]),
        spanned(Expr::Bool(true)),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_constant_false() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3} : FALSE
    let expr = exists(
        "x",
        set_enum(vec![num(1), num(2), num(3)]),
        spanned(Expr::Bool(false)),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_empty_domain() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {} : TRUE  (no elements -> false)
    let expr = exists("x", set_enum(vec![]), spanned(Expr::Bool(true)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_with_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..5 : TRUE
    let expr = forall("x", range(num(1), num(5)), spanned(Expr::Bool(true)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_with_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..5 : TRUE
    let expr = exists("x", range(num(1), num(5)), spanned(Expr::Bool(true)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Set at top level is a type error (Part of #3788)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_enum_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // {1, 2, 3} at top level is not a scalar
    let expr = set_enum(vec![num(1), num(2), num(3)]);
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::TypeMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // 1..5 at top level is not a scalar
    let expr = range(num(1), num(5));
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::TypeMismatch { .. })
    ));
}

// =========================================================================
// Membership combined with boolean operations (Part of #3788)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_combined_with_and() {
    let mut jit = JitContext::new().unwrap();
    // (3 \in {1, 2, 3}) /\ (4 \in {4, 5})
    let left = member(num(3), set_enum(vec![num(1), num(2), num(3)]));
    let right = member(num(4), set_enum(vec![num(4), num(5)]));
    let expr = spanned(Expr::And(Box::new(left), Box::new(right)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_combined_with_or() {
    let mut jit = JitContext::new().unwrap();
    // (7 \in {1, 2, 3}) \/ (4 \in {4, 5})
    let left = member(num(7), set_enum(vec![num(1), num(2), num(3)]));
    let right = member(num(4), set_enum(vec![num(4), num(5)]));
    let expr = spanned(Expr::Or(Box::new(left), Box::new(right)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_with_computed_set_elements() {
    let mut jit = JitContext::new().unwrap();
    // 6 \in {2+3, 3*2, 7}  =>  6 \in {5, 6, 7}
    let expr = member(
        num(6),
        set_enum(vec![add(num(2), num(3)), mul(num(3), num(2)), num(7)]),
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Function application tests (Part of #3798)
// =========================================================================

/// Helper to build a FuncDef: [var_name \in domain |-> body]
fn funcdef(var_name: &str, domain: Spanned<Expr>, body: Spanned<Expr>) -> Spanned<Expr> {
    use tla_core::ast::BoundVar;
    let bound = BoundVar {
        name: spanned(var_name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };
    spanned(Expr::FuncDef(vec![bound], Box::new(body)))
}

/// Helper to build FuncApply: f[x]
fn func_apply(func: Spanned<Expr>, arg: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::FuncApply(Box::new(func), Box::new(arg)))
}

/// Helper to build an Ident expression for bound variable references
fn ident(name: &str) -> Spanned<Expr> {
    use tla_core::name_intern::NameId;
    spanned(Expr::Ident(name.to_string(), NameId::INVALID))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_identity() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> i][2] == 2
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let expr = func_apply(f, num(2));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_double() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> i * 2][3] == 6
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(2)));
    let expr = func_apply(f, num(3));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 6);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_constant_body() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> 42][1] == 42
    let f = funcdef("i", range(num(1), num(3)), num(42));
    let expr = func_apply(f, num(1));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_arithmetic_body() {
    let mut jit = JitContext::new().unwrap();
    // [i \in {1, 2, 3} |-> i + 10][2] == 12
    let f = funcdef(
        "i",
        set_enum(vec![num(1), num(2), num(3)]),
        add(ident("i"), num(10)),
    );
    let expr = func_apply(f, num(2));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 12);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_out_of_domain() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> i][5] should fail (5 not in domain)
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let expr = func_apply(f, num(5));
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_with_computed_arg() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..5 |-> i * i][2 + 1] == 9  (applying at 3, 3*3=9)
    let f = funcdef("i", range(num(1), num(5)), mul(ident("i"), ident("i")));
    let expr = func_apply(f, add(num(2), num(1)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 9);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcdef_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> i] at top level is not a scalar
    let expr = funcdef("i", range(num(1), num(3)), ident("i"));
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::TypeMismatch { .. })
    ));
}

// =========================================================================
// Record field access tests (Part of #3798)
// =========================================================================

/// Helper to build a Record: [a |-> 1, b |-> 2, ...]
fn record(fields: Vec<(&str, Spanned<Expr>)>) -> Spanned<Expr> {
    let field_vec: Vec<(Spanned<String>, Spanned<Expr>)> = fields
        .into_iter()
        .map(|(name, expr)| (spanned(name.to_string()), expr))
        .collect();
    spanned(Expr::Record(field_vec))
}

/// Helper to build RecordAccess: r.field
fn record_access(rec: Spanned<Expr>, field: &str) -> Spanned<Expr> {
    use tla_core::ast::RecordFieldName;
    let field_name = RecordFieldName::new(spanned(field.to_string()));
    spanned(Expr::RecordAccess(Box::new(rec), field_name))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_simple() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 1, b |-> 2].a == 1
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let expr = record_access(rec, "a");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_second_field() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 1, b |-> 2].b == 2
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let expr = record_access(rec, "b");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_computed_value() {
    let mut jit = JitContext::new().unwrap();
    // [x |-> 3 + 4, y |-> 5 * 6].x == 7
    let rec = record(vec![("x", add(num(3), num(4))), ("y", mul(num(5), num(6)))]);
    let expr = record_access(rec, "x");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_missing_field() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 1, b |-> 2].c should fail (field not found)
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let expr = record_access(rec, "c");
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 1] at top level is not a scalar
    let expr = record(vec![("a", num(1))]);
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::TypeMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_many_fields() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 10, b |-> 20, c |-> 30, d |-> 40].c == 30
    let rec = record(vec![
        ("a", num(10)),
        ("b", num(20)),
        ("c", num(30)),
        ("d", num(40)),
    ]);
    let expr = record_access(rec, "c");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 30);
}

// =========================================================================
// DOMAIN tests (Part of #3798)
// =========================================================================

/// Helper to build DOMAIN expr
fn domain(func: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Domain(Box::new(func)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // DOMAIN [i \in 1..3 |-> i] at top level is a set, not scalar
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let expr = domain(f);
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::TypeMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_in_membership() {
    let mut jit = JitContext::new().unwrap();
    // 2 \in DOMAIN [i \in 1..3 |-> i * 2] == TRUE
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(2)));
    let expr = member(num(2), domain(f));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_not_in_membership() {
    let mut jit = JitContext::new().unwrap();
    // 5 \in DOMAIN [i \in 1..3 |-> i] == FALSE (5 not in 1..3)
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let expr = member(num(5), domain(f));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_with_set_enum() {
    let mut jit = JitContext::new().unwrap();
    // 10 \in DOMAIN [i \in {10, 20, 30} |-> i + 1] == TRUE
    let f = funcdef(
        "i",
        set_enum(vec![num(10), num(20), num(30)]),
        add(ident("i"), num(1)),
    );
    let expr = member(num(10), domain(f));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_domain_notin() {
    let mut jit = JitContext::new().unwrap();
    // 4 \notin DOMAIN [i \in 1..3 |-> i] == TRUE
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let expr = not_member(num(4), domain(f));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Combined expression tests (Part of #3798)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_in_comparison() {
    let mut jit = JitContext::new().unwrap();
    // [i \in 1..3 |-> i * 2][2] = 4  (should be TRUE)
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(2)));
    let apply = func_apply(f, num(2));
    let expr = spanned(Expr::Eq(Box::new(apply), Box::new(num(4))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_in_arithmetic() {
    let mut jit = JitContext::new().unwrap();
    // [a |-> 3, b |-> 7].a + [a |-> 3, b |-> 7].b == 10
    let rec1 = record(vec![("a", num(3)), ("b", num(7))]);
    let rec2 = record(vec![("a", num(3)), ("b", num(7))]);
    let expr = add(record_access(rec1, "a"), record_access(rec2, "b"));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 10);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_negative_domain() {
    let mut jit = JitContext::new().unwrap();
    // [i \in {-2, -1, 0, 1, 2} |-> i * i][-2] == 4
    let f = funcdef(
        "i",
        set_enum(vec![num(-2), num(-1), num(0), num(1), num(2)]),
        mul(ident("i"), ident("i")),
    );
    let expr = func_apply(f, num(-2));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 4);
}

// =========================================================================
// Quantifier with bound variable tests (native loop compilation)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_all_positive() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : x > 0  (all positive -> TRUE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_one_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : x > 1  (x=1 fails -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(1))));
    let expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bound_var_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3} : x = 2  (x=2 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(2))));
    let expr = exists("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bound_var_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3} : x = 5  (no such x -> FALSE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(5))));
    let expr = exists("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..10 : x >= 1  (all >= 1 -> TRUE)
    let body = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(1))));
    let expr = forall("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bound_var_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..10 : x = 7  (x=7 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(7))));
    let expr = exists("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_arithmetic_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {2, 4, 6} : x % 2 = 0  (all even -> TRUE)
    // Using TLA+ mod which is Euclidean
    let mod_expr = spanned(Expr::Mod(Box::new(ident("x")), Box::new(num(2))));
    let body = spanned(Expr::Eq(Box::new(mod_expr), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(2), num(4), num(6)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_arithmetic_body_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {2, 3, 6} : x % 2 = 0  (3 is odd -> FALSE)
    let mod_expr = spanned(Expr::Mod(Box::new(ident("x")), Box::new(num(2))));
    let body = spanned(Expr::Eq(Box::new(mod_expr), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(2), num(3), num(6)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bound_var_single_element() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {42} : x = 42  (single element, matches -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(42))));
    let expr = exists("x", set_enum(vec![num(42)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_single_element_true() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {5} : x > 0  (5 > 0 -> TRUE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(5)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_bound_var_single_element_false() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {0} : x > 0  (0 > 0 is false -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(0)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_membership_in_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : x \in {1, 2, 3, 4, 5}  (all members -> TRUE)
    let body = member(
        ident("x"),
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
    );
    let expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_with_complex_predicate() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..5 : (x > 3) /\ (x < 5)  (x=4 satisfies -> TRUE)
    let gt3 = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(3))));
    let lt5 = spanned(Expr::Lt(Box::new(ident("x")), Box::new(num(5))));
    let body = spanned(Expr::And(Box::new(gt3), Box::new(lt5)));
    let expr = exists("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_implies_in_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : (x > 2) => (x = 3)  (only 3 > 2, and 3=3 -> TRUE)
    let antecedent = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(2))));
    let consequent = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(3))));
    let body = spanned(Expr::Implies(Box::new(antecedent), Box::new(consequent)));
    let expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifier_combined_forall_and_exists() {
    let mut jit = JitContext::new().unwrap();
    // (\A x \in {1, 2, 3} : x > 0) /\ (\E y \in {1, 2, 3} : y = 2)
    let forall_body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let forall_expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), forall_body);
    let exists_body = spanned(Expr::Eq(Box::new(ident("y")), Box::new(num(2))));
    let exists_expr = exists("y", set_enum(vec![num(1), num(2), num(3)]), exists_body);
    let expr = spanned(Expr::And(Box::new(forall_expr), Box::new(exists_expr)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_negative_domain_values() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {-3, -2, -1} : x < 0  (all negative -> TRUE)
    let body = spanned(Expr::Lt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", set_enum(vec![num(-3), num(-2), num(-1)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_negative_domain_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {-3, -2, -1} : x > 0  (none positive -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = exists("x", set_enum(vec![num(-3), num(-2), num(-1)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

// =========================================================================
// Dynamic loop quantifier tests (domains > UNROLL_THRESHOLD = 4)
//
// These tests exercise the loop-based compilation path where the domain
// elements are stored in a heap array and the body is compiled once with
// the bound variable as a runtime Cranelift value loaded from memory.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_all_positive() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3, 4, 5} : x > 0  (all positive -> TRUE)
    // Domain size 5 > UNROLL_THRESHOLD, triggers loop compilation
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_one_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3, 4, 5} : x > 2  (x=1,2 fail -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(2))));
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3, 4, 5} : x = 4  (x=4 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(4))));
    let expr = exists(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3, 4, 5} : x = 99  (no match -> FALSE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(99))));
    let expr = exists(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..10 : x >= 1  (all >= 1 -> TRUE)
    // Range 1..10 = 10 elements, well above threshold
    let body = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(1))));
    let expr = forall("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_range_domain() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..10 : x = 7  (x=7 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(7))));
    let expr = exists("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_arithmetic_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {2, 4, 6, 8, 10} : x % 2 = 0  (all even -> TRUE)
    let mod_expr = spanned(Expr::Mod(Box::new(ident("x")), Box::new(num(2))));
    let body = spanned(Expr::Eq(Box::new(mod_expr), Box::new(num(0))));
    let expr = forall(
        "x",
        set_enum(vec![num(2), num(4), num(6), num(8), num(10)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_arithmetic_body_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {2, 3, 4, 6, 8} : x % 2 = 0  (3 is odd -> FALSE)
    let mod_expr = spanned(Expr::Mod(Box::new(ident("x")), Box::new(num(2))));
    let body = spanned(Expr::Eq(Box::new(mod_expr), Box::new(num(0))));
    let expr = forall(
        "x",
        set_enum(vec![num(2), num(3), num(4), num(6), num(8)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_complex_predicate() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..10 : (x > 7) /\ (x < 9)  (x=8 satisfies -> TRUE)
    let gt7 = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(7))));
    let lt9 = spanned(Expr::Lt(Box::new(ident("x")), Box::new(num(9))));
    let body = spanned(Expr::And(Box::new(gt7), Box::new(lt9)));
    let expr = exists("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_implies_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1,2,3,4,5} : (x > 3) => (x >= 4)  (TRUE for all)
    let antecedent = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(3))));
    let consequent = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(4))));
    let body = spanned(Expr::Implies(Box::new(antecedent), Box::new(consequent)));
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_negative_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {-5, -4, -3, -2, -1} : x < 0  (all negative -> TRUE)
    let body = spanned(Expr::Lt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall(
        "x",
        set_enum(vec![num(-5), num(-4), num(-3), num(-2), num(-1)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_negative_domain_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {-5, -4, -3, -2, -1} : x > 0  (none positive -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = exists(
        "x",
        set_enum(vec![num(-5), num(-4), num(-3), num(-2), num(-1)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_membership_in_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1,2,3,4,5} : x \in {1,2,3,4,5,6,7,8,9,10}  (all members -> TRUE)
    let superset = set_enum(vec![
        num(1),
        num(2),
        num(3),
        num(4),
        num(5),
        num(6),
        num(7),
        num(8),
        num(9),
        num(10),
    ]);
    let body = member(ident("x"), superset);
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_early_exit_first_element() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {42, 1, 2, 3, 4} : x = 42  (first element matches -> TRUE)
    // Verifies early exit works on the first iteration
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(42))));
    let expr = exists(
        "x",
        set_enum(vec![num(42), num(1), num(2), num(3), num(4)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_early_exit_first_element() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {0, 1, 2, 3, 4} : x > 0  (first element fails -> FALSE)
    // Verifies early exit works on the first iteration
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall(
        "x",
        set_enum(vec![num(0), num(1), num(2), num(3), num(4)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_last_element() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in {1, 2, 3, 4, 99} : x = 99  (last element matches -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(99))));
    let expr = exists(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(99)]),
        body,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_large_range() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..100 : x >= 1  (all >= 1 -> TRUE)
    // 100 elements: tests loop with a realistic domain size
    let body = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(1))));
    let expr = forall("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_loop_large_range() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..100 : x = 100  (last element -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(100))));
    let expr = exists("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_loop_large_range_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..100 : x # 50  (x=50 fails -> FALSE)
    let body = spanned(Expr::Neq(Box::new(ident("x")), Box::new(num(50))));
    let expr = forall("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combined_loop_forall_and_exists() {
    let mut jit = JitContext::new().unwrap();
    // (\A x \in 1..10 : x > 0) /\ (\E y \in 1..10 : y = 5)
    // Both use loop compilation (10 elements each)
    let forall_body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let forall_expr = forall("x", range(num(1), num(10)), forall_body);
    let exists_body = spanned(Expr::Eq(Box::new(ident("y")), Box::new(num(5))));
    let exists_expr = exists("y", range(num(1), num(10)), exists_body);
    let expr = spanned(Expr::And(Box::new(forall_expr), Box::new(exists_expr)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_loop_quantifiers() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1,2,3,4,5} : \E y \in {1,2,3,4,5} : x = y
    // Nested quantifiers — outer loop, inner loop
    let inner_body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(ident("y"))));
    let inner_exists = exists(
        "y",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        inner_body,
    );
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        inner_exists,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_loop_quantifiers_false() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1,2,3,4,5} : \E y \in {10,20,30,40,50} : x = y
    // No overlap between domains -> FALSE
    let inner_body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(ident("y"))));
    let inner_exists = exists(
        "y",
        set_enum(vec![num(10), num(20), num(30), num(40), num(50)]),
        inner_body,
    );
    let expr = forall(
        "x",
        set_enum(vec![num(1), num(2), num(3), num(4), num(5)]),
        inner_exists,
    );
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

// =========================================================================
// Runtime function application tests (Part of #3798)
//
// These tests exercise the `compile_func_apply_lookup` path where the
// function is known at compile time but the argument is a runtime bound
// variable from a quantifier loop.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_forall_identity() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..5 : [i \in 1..5 |-> i][x] = x
    // Function is identity, applied with runtime arg from quantifier
    let f = funcdef("i", range(num(1), num(5)), ident("i"));
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(ident("x"))));
    let expr = forall("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_forall_double() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..3 : [i \in 1..3 |-> i * 2][x] > 0
    // All values are positive (2, 4, 6) -> TRUE
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(2)));
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Gt(Box::new(apply), Box::new(num(0))));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_exists() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..5 : [i \in 1..5 |-> i * i][x] = 9
    // x=3 gives 3*3=9 -> TRUE
    let f = funcdef("i", range(num(1), num(5)), mul(ident("i"), ident("i")));
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(num(9))));
    let expr = exists("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_exists_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..5 : [i \in 1..5 |-> i * i][x] = 100
    // No x in 1..5 gives 100 -> FALSE
    let f = funcdef("i", range(num(1), num(5)), mul(ident("i"), ident("i")));
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(num(100))));
    let expr = exists("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_non_contiguous_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {10, 20, 30} : [i \in {10, 20, 30} |-> i + 1][x] > x
    // (11 > 10, 21 > 20, 31 > 30) -> TRUE
    // Non-contiguous domain -- uses linear scan lookup
    let dom = set_enum(vec![num(10), num(20), num(30)]);
    let f = funcdef(
        "i",
        set_enum(vec![num(10), num(20), num(30)]),
        add(ident("i"), num(1)),
    );
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Gt(Box::new(apply), Box::new(ident("x"))));
    let expr = forall("x", dom, body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_large_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..100 : [i \in 1..100 |-> i + 1][x] = x + 1
    // Uses direct indexing (contiguous range, 100 elements)
    let f = funcdef("i", range(num(1), num(100)), add(ident("i"), num(1)));
    let apply = func_apply(f, ident("x"));
    let rhs = add(ident("x"), num(1));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(rhs)));
    let expr = forall("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_oob_bounds_check() {
    let mut jit = JitContext::new().unwrap();
    // Bypass preflight so the lowering-level bounds check is exercised.
    // The preflight would reject f[x] when x is out of domain; we want to
    // verify the Cranelift-emitted code handles OOB safely.
    //
    // \A x \in 0..5 : IF x \in 1..3 THEN [i \in 1..3 |-> i * 10][x] = x * 10
    //                                ELSE TRUE
    //
    // The IF guard prevents Cranelift from evaluating f[x] when x is out of
    // domain -- but the direct-index array is still allocated for domain 1..3,
    // and the bounds check in try_compile_direct_index_lookup is exercised for
    // correctness verification. Without the bounds check, an OOB index would
    // read invalid memory.
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let apply = func_apply(f, ident("x"));
    let eq = spanned(Expr::Eq(
        Box::new(apply),
        Box::new(mul(ident("x"), num(10))),
    ));
    let true_val = spanned(Expr::Bool(true));
    let body = spanned(Expr::If(
        Box::new(member(ident("x"), range(num(1), num(3)))),
        Box::new(eq),
        Box::new(true_val),
    ));
    let expr = forall("x", range(num(0), num(5)), body);
    let func = compile_expr_no_preflight(&mut jit, &expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Runtime record field access via function application (Part of #3798)
//
// Tests for `f[x].field` where `f` is a compile-time function that maps
// integers to records and `x` is a runtime bound variable.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_field_simple() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> [val |-> i * 10]]
    // \A x \in 1..3 : f[x].val = x * 10
    let rec_body = record(vec![("val", mul(ident("i"), num(10)))]);
    let f = funcdef("i", range(num(1), num(3)), rec_body);
    let field_access = record_access(func_apply(f, ident("x")), "val");
    let rhs = mul(ident("x"), num(10));
    let body = spanned(Expr::Eq(Box::new(field_access), Box::new(rhs)));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_field_multiple_fields() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> [a |-> i, b |-> i * 2]]
    // \A x \in 1..3 : f[x].b = x * 2
    let rec_body = record(vec![("a", ident("i")), ("b", mul(ident("i"), num(2)))]);
    let f = funcdef("i", range(num(1), num(3)), rec_body);
    let field_access = record_access(func_apply(f, ident("x")), "b");
    let rhs = mul(ident("x"), num(2));
    let body = spanned(Expr::Eq(Box::new(field_access), Box::new(rhs)));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_field_exists() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..5 |-> [valid |-> IF i > 3 THEN 1 ELSE 0]]
    // \E x \in 1..5 : f[x].valid = 1
    // x=4 and x=5 satisfy -> TRUE
    let if_expr = spanned(Expr::If(
        Box::new(spanned(Expr::Gt(Box::new(ident("i")), Box::new(num(3))))),
        Box::new(num(1)),
        Box::new(num(0)),
    ));
    let rec_body = record(vec![("valid", if_expr)]);
    let f = funcdef("i", range(num(1), num(5)), rec_body);
    let field_access = record_access(func_apply(f, ident("x")), "valid");
    let body = spanned(Expr::Eq(Box::new(field_access), Box::new(num(1))));
    let expr = exists("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_field_all_valid() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> [valid |-> 1, value |-> i]]
    // \A x \in 1..3 : f[x].valid = 1
    // All records have valid=1 -> TRUE
    let rec_body = record(vec![("valid", num(1)), ("value", ident("i"))]);
    let f = funcdef("i", range(num(1), num(3)), rec_body);
    let field_access = record_access(func_apply(f, ident("x")), "valid");
    let body = spanned(Expr::Eq(Box::new(field_access), Box::new(num(1))));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_missing_field_error() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> [a |-> i]]
    // \A x \in 1..3 : f[x].nonexistent = 0
    // Should fail at compile time: field 'nonexistent' not in record
    let rec_body = record(vec![("a", ident("i"))]);
    let f = funcdef("i", range(num(1), num(3)), rec_body);
    let field_access = record_access(func_apply(f, ident("x")), "nonexistent");
    let body = spanned(Expr::Eq(Box::new(field_access), Box::new(num(0))));
    let expr = forall("x", range(num(1), num(3)), body);
    assert!(jit.compile_expr(&expr).is_err());
}

// =========================================================================
// Combined and nested access tests (Part of #3798)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_record_in_arithmetic() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> [a |-> i, b |-> i + 10]]
    // \A x \in 1..3 : f[x].a + f[x].b = x + x + 10
    // For each x: x + (x + 10) = 2x + 10
    let rec_body1 = record(vec![("a", ident("i")), ("b", add(ident("i"), num(10)))]);
    let rec_body2 = record(vec![("a", ident("i")), ("b", add(ident("i"), num(10)))]);
    let f1 = funcdef("i", range(num(1), num(3)), rec_body1);
    let f2 = funcdef("i", range(num(1), num(3)), rec_body2);
    let lhs = add(
        record_access(func_apply(f1, ident("x")), "a"),
        record_access(func_apply(f2, ident("x")), "b"),
    );
    let rhs = add(add(ident("x"), ident("x")), num(10));
    let body = spanned(Expr::Eq(Box::new(lhs), Box::new(rhs)));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_combined_with_comparison() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..5 : [i \in 1..5 |-> i * 2][x] >= 2
    // All values f(x) = 2x >= 2 for x in 1..5 -> TRUE
    let f = funcdef("i", range(num(1), num(5)), mul(ident("i"), num(2)));
    let apply = func_apply(f, ident("x"));
    let body = spanned(Expr::Geq(Box::new(apply), Box::new(num(2))));
    let expr = forall("x", range(num(1), num(5)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_apply_in_boolean_logic() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..3 : f[x] > 0 /\ f[x] < 4
    // where f = [i \in 1..3 |-> i]
    // 1..3 are all > 0 and < 4 -> TRUE
    let f1 = funcdef("i", range(num(1), num(3)), ident("i"));
    let f2 = funcdef("i", range(num(1), num(3)), ident("i"));
    let gt0 = spanned(Expr::Gt(
        Box::new(func_apply(f1, ident("x"))),
        Box::new(num(0)),
    ));
    let lt4 = spanned(Expr::Lt(
        Box::new(func_apply(f2, ident("x"))),
        Box::new(num(4)),
    ));
    let body = spanned(Expr::And(Box::new(gt0), Box::new(lt4)));
    let expr = forall("x", range(num(1), num(3)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Range-optimized membership tests (Part of #3788)
//
// These tests exercise the `x \in a..b -> x >= a && x <= b` optimization.
// The range is compiled to two comparisons instead of N equality checks.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_within() {
    let mut jit = JitContext::new().unwrap();
    // 5 \in 1..10  (within range -> TRUE)
    let expr = member(num(5), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_lo_boundary() {
    let mut jit = JitContext::new().unwrap();
    // 1 \in 1..10  (lower boundary -> TRUE)
    let expr = member(num(1), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_hi_boundary() {
    let mut jit = JitContext::new().unwrap();
    // 10 \in 1..10  (upper boundary -> TRUE)
    let expr = member(num(10), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_below() {
    let mut jit = JitContext::new().unwrap();
    // 0 \in 1..10  (below range -> FALSE)
    let expr = member(num(0), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_above() {
    let mut jit = JitContext::new().unwrap();
    // 11 \in 1..10  (above range -> FALSE)
    let expr = member(num(11), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_negative_bounds() {
    let mut jit = JitContext::new().unwrap();
    // -3 \in -5..5  (within range -> TRUE)
    let expr = member(num(-3), range(num(-5), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_negative_outside() {
    let mut jit = JitContext::new().unwrap();
    // -6 \in -5..5  (below range -> FALSE)
    let expr = member(num(-6), range(num(-5), num(5)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_empty_range() {
    let mut jit = JitContext::new().unwrap();
    // 3 \in 5..1  (empty range -> FALSE)
    let expr = member(num(3), range(num(5), num(1)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_single_element_range() {
    let mut jit = JitContext::new().unwrap();
    // 7 \in 7..7  (single element range -> TRUE)
    let expr = member(num(7), range(num(7), num(7)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_optimized_single_element_miss() {
    let mut jit = JitContext::new().unwrap();
    // 8 \in 7..7  (single element range, miss -> FALSE)
    let expr = member(num(8), range(num(7), num(7)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_range_optimized_outside() {
    let mut jit = JitContext::new().unwrap();
    // 0 \notin 1..10  (below range -> TRUE)
    let expr = not_member(num(0), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_range_optimized_inside() {
    let mut jit = JitContext::new().unwrap();
    // 5 \notin 1..10  (within range -> FALSE)
    let expr = not_member(num(5), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_range_optimized_empty_range() {
    let mut jit = JitContext::new().unwrap();
    // 3 \notin 5..1  (empty range -> TRUE)
    let expr = not_member(num(3), range(num(5), num(1)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_range_optimized_boundary() {
    let mut jit = JitContext::new().unwrap();
    // 10 \notin 1..10  (upper boundary -> FALSE)
    let expr = not_member(num(10), range(num(1), num(10)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_combined_with_and() {
    let mut jit = JitContext::new().unwrap();
    // (3 \in 1..5) /\ (7 \in 1..10)  (both true -> TRUE)
    let left = member(num(3), range(num(1), num(5)));
    let right = member(num(7), range(num(1), num(10)));
    let expr = spanned(Expr::And(Box::new(left), Box::new(right)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_combined_with_or() {
    let mut jit = JitContext::new().unwrap();
    // (0 \in 1..5) \/ (7 \in 1..10)  (first false, second true -> TRUE)
    let left = member(num(0), range(num(1), num(5)));
    let right = member(num(7), range(num(1), num(10)));
    let expr = spanned(Expr::Or(Box::new(left), Box::new(right)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// Range-optimized quantifier loop tests (Part of #3788)
//
// These tests exercise the `compile_quantifier_range_loop` path where the
// domain is a..b and the loop variable increments from a to b instead of
// loading from a heap array.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_all_positive() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..20 : x > 0  (all positive -> TRUE)
    // Domain 1..20 uses range loop (no heap array)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", range(num(1), num(20)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_one_fails() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..20 : x > 10  (x=1..10 fail -> FALSE)
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(10))));
    let expr = forall("x", range(num(1), num(20)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..20 : x = 15  (x=15 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(15))));
    let expr = exists("x", range(num(1), num(20)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_not_found() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..20 : x = 99  (no match -> FALSE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(99))));
    let expr = exists("x", range(num(1), num(20)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_negative_domain() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in -10..10 : x >= -10  (all >= -10 -> TRUE)
    let body = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(-10))));
    let expr = forall("x", range(num(-10), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_negative_domain() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in -10..-1 : x = -5  (x=-5 exists -> TRUE)
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(-5))));
    let expr = exists("x", range(num(-10), num(-1)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_arithmetic_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..50 : x * 2 >= 2  (all x*2 >= 2 for x >= 1 -> TRUE)
    let mul_expr = mul(ident("x"), num(2));
    let body = spanned(Expr::Geq(Box::new(mul_expr), Box::new(num(2))));
    let expr = forall("x", range(num(1), num(50)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_complex_predicate() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..100 : (x > 49) /\ (x < 51)  (x=50 satisfies -> TRUE)
    let gt49 = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(49))));
    let lt51 = spanned(Expr::Lt(Box::new(ident("x")), Box::new(num(51))));
    let body = spanned(Expr::And(Box::new(gt49), Box::new(lt51)));
    let expr = exists("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_implies_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..20 : (x > 15) => (x >= 16)  (TRUE for all)
    let antecedent = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(15))));
    let consequent = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(16))));
    let body = spanned(Expr::Implies(Box::new(antecedent), Box::new(consequent)));
    let expr = forall("x", range(num(1), num(20)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_membership_in_body() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..10 : x \in 1..100  (all in superset -> TRUE)
    // Tests range membership inside a range quantifier loop body
    let body = member(ident("x"), range(num(1), num(100)));
    let expr = forall("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_notin_in_body() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..10 : x \notin 1..5  (x=6..10 satisfy -> TRUE)
    // Tests range notin inside a range quantifier loop body
    let body = not_member(ident("x"), range(num(1), num(5)));
    let expr = exists("x", range(num(1), num(10)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_range_quantifiers() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..5 : \E y \in 1..5 : x = y
    // Nested range quantifier loops — both use range loop optimization
    let inner_body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(ident("y"))));
    let inner_exists = exists("y", range(num(1), num(5)), inner_body);
    let expr = forall("x", range(num(1), num(5)), inner_exists);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_range_quantifiers_false() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..5 : \E y \in 10..15 : x = y
    // No overlap between ranges -> FALSE
    let inner_body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(ident("y"))));
    let inner_exists = exists("y", range(num(10), num(15)), inner_body);
    let expr = forall("x", range(num(1), num(5)), inner_exists);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_large_range() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 1..500 : x >= 1  (all >= 1 -> TRUE)
    // Large range: 500 elements, exercises the range loop with no heap alloc
    let body = spanned(Expr::Geq(Box::new(ident("x")), Box::new(num(1))));
    let expr = forall("x", range(num(1), num(500)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_loop_early_exit_first() {
    let mut jit = JitContext::new().unwrap();
    // \E x \in 1..100 : x = 1  (first element matches -> TRUE)
    // Verifies early exit on the first iteration of range loop
    let body = spanned(Expr::Eq(Box::new(ident("x")), Box::new(num(1))));
    let expr = exists("x", range(num(1), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_loop_early_exit_first() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in 0..100 : x > 0  (x=0 fails -> FALSE)
    // Verifies early exit on the first iteration of range loop
    let body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let expr = forall("x", range(num(0), num(100)), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combined_range_forall_and_exists() {
    let mut jit = JitContext::new().unwrap();
    // (\A x \in 1..20 : x > 0) /\ (\E y \in 1..20 : y = 10)
    let forall_body = spanned(Expr::Gt(Box::new(ident("x")), Box::new(num(0))));
    let forall_expr = forall("x", range(num(1), num(20)), forall_body);
    let exists_body = spanned(Expr::Eq(Box::new(ident("y")), Box::new(num(10))));
    let exists_expr = exists("y", range(num(1), num(20)), exists_body);
    let expr = spanned(Expr::And(Box::new(forall_expr), Box::new(exists_expr)));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

// =========================================================================
// EXCEPT on functions tests (Part of #3798)
//
// Tests for [f EXCEPT ![key] = val] where f is a compile-time function.
// =========================================================================

/// Helper to build an ExceptSpec with a function index path: ![key] = val
fn except_index(key: Spanned<Expr>, val: Spanned<Expr>) -> tla_core::ast::ExceptSpec {
    use tla_core::ast::{ExceptPathElement, ExceptSpec};
    ExceptSpec {
        path: vec![ExceptPathElement::Index(key)],
        value: val,
    }
}

/// Helper to build an ExceptSpec with a record field path: !.field = val
fn except_field(field: &str, val: Spanned<Expr>) -> tla_core::ast::ExceptSpec {
    use tla_core::ast::{ExceptPathElement, ExceptSpec, RecordFieldName};
    ExceptSpec {
        path: vec![ExceptPathElement::Field(RecordFieldName::new(spanned(
            field.to_string(),
        )))],
        value: val,
    }
}

/// Helper to build an EXCEPT expression
fn except(base: Spanned<Expr>, specs: Vec<tla_core::ast::ExceptSpec>) -> Spanned<Expr> {
    spanned(Expr::Except(Box::new(base), specs))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_update_and_apply() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![2] = 99][2] == 99
    // where f = [i \in 1..3 |-> i * 10]
    // Original: f[2] = 20, after EXCEPT: f[2] = 99
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted = except(f, vec![except_index(num(2), num(99))]);
    let expr = func_apply(excepted, num(2));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 99);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_update_preserves_other_keys() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![2] = 99][1] == 10
    // where f = [i \in 1..3 |-> i * 10]
    // Only key 2 is updated; key 1 retains f[1] = 10
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted = except(f, vec![except_index(num(2), num(99))]);
    let expr = func_apply(excepted, num(1));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 10);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_update_preserves_last_key() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![1] = 0][3] == 30
    // where f = [i \in 1..3 |-> i * 10]
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted = except(f, vec![except_index(num(1), num(0))]);
    let expr = func_apply(excepted, num(3));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 30);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_multiple_updates() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![1] = 100, ![3] = 300][1] == 100
    // [f EXCEPT ![1] = 100, ![3] = 300][2] == 20
    // [f EXCEPT ![1] = 100, ![3] = 300][3] == 300
    let f1 = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted1 = except(
        f1,
        vec![
            except_index(num(1), num(100)),
            except_index(num(3), num(300)),
        ],
    );
    let expr1 = func_apply(excepted1, num(1));
    let func = jit.compile_expr(&expr1).unwrap();
    assert_eq!(func(), 100);

    let f2 = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted2 = except(
        f2,
        vec![
            except_index(num(1), num(100)),
            except_index(num(3), num(300)),
        ],
    );
    let expr2 = func_apply(excepted2, num(2));
    let func = jit.compile_expr(&expr2).unwrap();
    assert_eq!(func(), 20);

    let f3 = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted3 = except(
        f3,
        vec![
            except_index(num(1), num(100)),
            except_index(num(3), num(300)),
        ],
    );
    let expr3 = func_apply(excepted3, num(3));
    let func = jit.compile_expr(&expr3).unwrap();
    assert_eq!(func(), 300);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![2] = 99] at top level is not a scalar
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let excepted = except(f, vec![except_index(num(2), num(99))]);
    assert!(matches!(
        jit.compile_expr(&excepted),
        Err(JitError::TypeMismatch { .. })
    ));
}

// =========================================================================
// EXCEPT on records tests (Part of #3798)
//
// Tests for [r EXCEPT !.field = val] where r is a compile-time record.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_update_field() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.a = 99].a == 99
    // where r = [a |-> 1, b |-> 2]
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let excepted = except(rec, vec![except_field("a", num(99))]);
    let expr = record_access(excepted, "a");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 99);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_preserves_other_fields() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.a = 99].b == 2
    // where r = [a |-> 1, b |-> 2]
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let excepted = except(rec, vec![except_field("a", num(99))]);
    let expr = record_access(excepted, "b");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_multiple_field_updates() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.a = 10, !.c = 30].a == 10
    // [r EXCEPT !.a = 10, !.c = 30].b == 2  (unchanged)
    // [r EXCEPT !.a = 10, !.c = 30].c == 30
    let rec1 = record(vec![("a", num(1)), ("b", num(2)), ("c", num(3))]);
    let excepted1 = except(
        rec1,
        vec![except_field("a", num(10)), except_field("c", num(30))],
    );
    let expr1 = record_access(excepted1, "a");
    let func = jit.compile_expr(&expr1).unwrap();
    assert_eq!(func(), 10);

    let rec2 = record(vec![("a", num(1)), ("b", num(2)), ("c", num(3))]);
    let excepted2 = except(
        rec2,
        vec![except_field("a", num(10)), except_field("c", num(30))],
    );
    let expr2 = record_access(excepted2, "b");
    let func = jit.compile_expr(&expr2).unwrap();
    assert_eq!(func(), 2);

    let rec3 = record(vec![("a", num(1)), ("b", num(2)), ("c", num(3))]);
    let excepted3 = except(
        rec3,
        vec![except_field("a", num(10)), except_field("c", num(30))],
    );
    let expr3 = record_access(excepted3, "c");
    let func = jit.compile_expr(&expr3).unwrap();
    assert_eq!(func(), 30);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_top_level_rejected() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.a = 99] at top level is not a scalar
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let excepted = except(rec, vec![except_field("a", num(99))]);
    assert!(matches!(
        jit.compile_expr(&excepted),
        Err(JitError::TypeMismatch { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_computed_value() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.x = 3 + 4].x == 7
    let rec = record(vec![("x", num(1)), ("y", num(2))]);
    let excepted = except(rec, vec![except_field("x", add(num(3), num(4)))]);
    let expr = record_access(excepted, "x");
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 7);
}

// =========================================================================
// EXCEPT with function application (nested patterns) (Part of #3798)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_in_quantifier() {
    let mut jit = JitContext::new().unwrap();
    // f = [i \in 1..3 |-> i * 10]
    // g = [f EXCEPT ![2] = 0]
    // \A x \in {1, 3} : g[x] = x * 10  (keys 1 and 3 unchanged)
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let g = except(f, vec![except_index(num(2), num(0))]);
    let apply = func_apply(g, ident("x"));
    let rhs = mul(ident("x"), num(10));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(rhs)));
    let expr = forall("x", set_enum(vec![num(1), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_apply_at_updated_key() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![2] = 0][2] == 0
    // where f = [i \in 1..3 |-> i * 10]
    let f = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let excepted = except(f, vec![except_index(num(2), num(0))]);
    let expr = func_apply(excepted, num(2));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_in_comparison() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT !.a = 42].a = 42  (should be TRUE)
    let rec = record(vec![("a", num(1)), ("b", num(2))]);
    let excepted = except(rec, vec![except_field("a", num(42))]);
    let access = record_access(excepted, "a");
    let expr = spanned(Expr::Eq(Box::new(access), Box::new(num(42))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_in_arithmetic() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT ![1] = 100][1] + [f EXCEPT ![1] = 100][2] == 100 + 20
    // where f = [i \in 1..3 |-> i * 10]
    let f1 = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let g1 = except(f1, vec![except_index(num(1), num(100))]);
    let f2 = funcdef("i", range(num(1), num(3)), mul(ident("i"), num(10)));
    let g2 = except(f2, vec![except_index(num(1), num(100))]);
    let lhs = add(func_apply(g1, num(1)), func_apply(g2, num(2)));
    let expr = spanned(Expr::Eq(Box::new(lhs), Box::new(num(120))));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_type_mismatch_field_on_func() {
    let mut jit = JitContext::new().unwrap();
    // [f EXCEPT !.field = 1] should fail — f is a function, not a record
    let f = funcdef("i", range(num(1), num(3)), ident("i"));
    let excepted = except(f, vec![except_field("field", num(1))]);
    let expr = func_apply(excepted, num(1));
    assert!(jit.compile_expr(&expr).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_type_mismatch_index_on_record() {
    let mut jit = JitContext::new().unwrap();
    // [r EXCEPT ![1] = 99] should fail — r is a record, not a function
    let rec = record(vec![("a", num(1))]);
    let excepted = except(rec, vec![except_index(num(1), num(99))]);
    let expr = record_access(excepted, "a");
    assert!(jit.compile_expr(&expr).is_err());
}

// =========================================================================
// Substitution-based EXCEPT tests (Part of #3798)
//
// Tests for EXCEPT where the value depends on a bound variable
// from a quantifier, exercising substitute_ident support for Except.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_func_with_substituted_value() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {1, 2, 3} : [f EXCEPT ![x] = x * 100][x] = x * 100
    // where f = [i \in 1..3 |-> 0]
    // For each x, the EXCEPT updates key x to x*100, then we read key x.
    let f = funcdef("i", range(num(1), num(3)), num(0));
    let excepted = except(f, vec![except_index(ident("x"), mul(ident("x"), num(100)))]);
    let apply = func_apply(excepted, ident("x"));
    let rhs = mul(ident("x"), num(100));
    let body = spanned(Expr::Eq(Box::new(apply), Box::new(rhs)));
    let expr = forall("x", set_enum(vec![num(1), num(2), num(3)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_record_with_substituted_value() {
    let mut jit = JitContext::new().unwrap();
    // \A x \in {10, 20, 30} : [r EXCEPT !.a = x].a = x
    // where r = [a |-> 0, b |-> 0]
    let rec = record(vec![("a", num(0)), ("b", num(0))]);
    let excepted = except(rec, vec![except_field("a", ident("x"))]);
    let access = record_access(excepted, "a");
    let body = spanned(Expr::Eq(Box::new(access), Box::new(ident("x"))));
    let expr = forall("x", set_enum(vec![num(10), num(20), num(30)]), body);
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}
