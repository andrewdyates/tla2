// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use hashbrown::HashMap;
use num_bigint::BigInt;
use z4_core::term::Symbol;
use z4_core::{Sort, TermStore};

#[test]
fn test_evaluate_bv_expr_sign_extend_negative() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    // sign_extend by 4 bits: 4-bit -> 8-bit
    let sext = terms.mk_app(
        Symbol::indexed("sign_extend", vec![4]),
        vec![x],
        Sort::bitvec(8),
    );
    let mut values = HashMap::new();
    // 0b1100 = 12, but in 4-bit signed = -4
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    // sign_extend(-4, 8 bits) = 0b11111100 = 252
    assert_eq!(result, Some(BigInt::from(0b11111100u8)));
}

#[test]
fn test_evaluate_bv_expr_sign_extend_positive() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let sext = terms.mk_app(
        Symbol::indexed("sign_extend", vec![4]),
        vec![x],
        Sort::bitvec(8),
    );
    let mut values = HashMap::new();
    // 0b0101 = 5 (positive in 4-bit signed)
    values.insert(x, BigInt::from(0b0101u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    // sign_extend(5, 8 bits) = 0b00000101 = 5
    assert_eq!(result, Some(BigInt::from(0b00000101u8)));
}

#[test]
fn test_evaluate_bv_expr_sign_extend_named_symbol() {
    // The model evaluator tests use Symbol::named — verify this path works too
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let sext = terms.mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(8));
    let mut values = HashMap::new();
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    assert_eq!(result, Some(BigInt::from(0b11111100u8)));
}

#[test]
fn test_evaluate_bv_expr_zero_extend() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let zext = terms.mk_app(Symbol::named("zero_extend"), vec![x], Sort::bitvec(8));
    let mut values = HashMap::new();
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, zext, &values);
    // zero_extend(0b1100) = 0b00001100 = 12
    assert_eq!(result, Some(BigInt::from(0b00001100u8)));
}

#[test]
fn test_evaluate_bv_expr_repeat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    // repeat 3 times: 4-bit -> 12-bit
    let rep = terms.mk_app(
        Symbol::indexed("repeat", vec![3]),
        vec![x],
        Sort::bitvec(12),
    );
    let mut values = HashMap::new();
    // 0b1010
    values.insert(x, BigInt::from(0b1010u8));
    let result = Executor::evaluate_bv_expr(&terms, rep, &values);
    // repeat(0b1010, 3) = 0b1010_1010_1010 = 0xAAA = 2730
    assert_eq!(result, Some(BigInt::from(0b1010_1010_1010u16)));
}
