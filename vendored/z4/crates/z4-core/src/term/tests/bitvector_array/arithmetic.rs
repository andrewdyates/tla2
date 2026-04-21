// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =======================================================================
// Bitvector operation tests
// =======================================================================

#[test]
fn test_bvadd_constant_folding() {
    let mut store = TermStore::new();

    // #x01 + #x02 = #x03
    let a = store.mk_bitvec(BigInt::from(1), 8);
    let b = store.mk_bitvec(BigInt::from(2), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvadd(vec![a, b]);
    assert_eq!(result, expected);

    // Overflow: #xFF + #x01 = #x00 (for 8-bit)
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvadd(vec![ff, one]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvadd_identity() {
    let mut store = TermStore::new();

    // x + 0 = x
    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvadd(vec![x, zero]);
    assert_eq!(result, x);

    // 0 + x = x
    let result2 = store.mk_bvadd(vec![zero, x]);
    assert_eq!(result2, x);
}

#[test]
fn test_bvsub_constant_folding() {
    let mut store = TermStore::new();

    // #x05 - #x03 = #x02
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvsub(vec![a, b]);
    assert_eq!(result, expected);

    // Underflow: #x01 - #x02 = #xFF (for 8-bit)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let underflow_result = store.mk_bvsub(vec![one, two]);
    assert_eq!(underflow_result, ff);
}

#[test]
fn test_bvsub_identity_and_self() {
    let mut store = TermStore::new();

    // x - 0 = x
    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvsub(vec![x, zero]);
    assert_eq!(result, x);

    // x - x = 0
    let self_sub = store.mk_bvsub(vec![x, x]);
    assert_eq!(self_sub, zero);
}

#[test]
fn test_bvmul_constant_folding() {
    let mut store = TermStore::new();

    // #x03 * #x04 = #x0C
    let a = store.mk_bitvec(BigInt::from(3), 8);
    let b = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(12), 8);
    let result = store.mk_bvmul(vec![a, b]);
    assert_eq!(result, expected);

    // Overflow: #x80 * #x02 = #x00 (for 8-bit)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvmul(vec![x80, two]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvmul_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x * 0 = 0
    let result = store.mk_bvmul(vec![x, zero]);
    assert_eq!(result, zero);

    // 0 * x = 0
    let result2 = store.mk_bvmul(vec![zero, x]);
    assert_eq!(result2, zero);

    // x * 1 = x
    let result3 = store.mk_bvmul(vec![x, one]);
    assert_eq!(result3, x);

    // 1 * x = x
    let result4 = store.mk_bvmul(vec![one, x]);
    assert_eq!(result4, x);
}

#[test]
fn test_bvand_constant_folding() {
    let mut store = TermStore::new();

    // #xFF & #x0F = #x0F
    let a = store.mk_bitvec(BigInt::from(0xFF), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bvand(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvand_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);

    // x & 0 = 0
    let result = store.mk_bvand(vec![x, zero]);
    assert_eq!(result, zero);

    // x & #xFF = x (all-ones)
    let result2 = store.mk_bvand(vec![x, all_ones]);
    assert_eq!(result2, x);

    // x & x = x (idempotent)
    let result3 = store.mk_bvand(vec![x, x]);
    assert_eq!(result3, x);
}

#[test]
fn test_bvor_constant_folding() {
    let mut store = TermStore::new();

    // #xF0 | #x0F = #xFF
    let a = store.mk_bitvec(BigInt::from(0xF0), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvor(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvor_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);

    // x | 0 = x
    let result = store.mk_bvor(vec![x, zero]);
    assert_eq!(result, x);

    // x | #xFF = #xFF
    let result2 = store.mk_bvor(vec![x, all_ones]);
    assert_eq!(result2, all_ones);

    // x | x = x (idempotent)
    let result3 = store.mk_bvor(vec![x, x]);
    assert_eq!(result3, x);
}

#[test]
fn test_bvxor_constant_folding() {
    let mut store = TermStore::new();

    // #xF0 ^ #x0F = #xFF
    let a = store.mk_bitvec(BigInt::from(0xF0), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvxor(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvxor_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x ^ 0 = x
    let result = store.mk_bvxor(vec![x, zero]);
    assert_eq!(result, x);

    // x ^ x = 0
    let result2 = store.mk_bvxor(vec![x, x]);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvnot_constant_folding() {
    let mut store = TermStore::new();

    // ~#x00 = #xFF (for 8-bit)
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvnot(zero);
    assert_eq!(result, all_ones);

    // ~#xFF = #x00
    let result2 = store.mk_bvnot(all_ones);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvnot_double_negation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let not_x = store.mk_bvnot(x);
    let not_not_x = store.mk_bvnot(not_x);
    assert_eq!(not_not_x, x);
}

#[test]
fn test_bvneg_constant_folding() {
    let mut store = TermStore::new();

    // -#x01 = #xFF (for 8-bit, two's complement)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvneg(one);
    assert_eq!(result, neg_one);

    // -#x00 = #x00
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvneg(zero);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvneg_double_negation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let neg_x = store.mk_bvneg(x);
    let neg_neg_x = store.mk_bvneg(neg_x);
    assert_eq!(neg_neg_x, x);
}

#[test]
fn test_bvshl_constant_folding() {
    let mut store = TermStore::new();

    // #x01 << 4 = #x10
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0x10), 8);
    let result = store.mk_bvshl(vec![one, four]);
    assert_eq!(result, expected);

    // #x80 << 1 = #x00 (overflow)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let one_shift = store.mk_bitvec(BigInt::from(1), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvshl(vec![x80, one_shift]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvshl_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x << 0 = x
    let result = store.mk_bvshl(vec![x, zero]);
    assert_eq!(result, x);

    // 0 << x = 0
    let result2 = store.mk_bvshl(vec![zero, x]);
    assert_eq!(result2, zero);

    // x << 8 = 0 (shift >= width)
    let eight = store.mk_bitvec(BigInt::from(8), 8);
    let result3 = store.mk_bvshl(vec![x, eight]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvlshr_constant_folding() {
    let mut store = TermStore::new();

    // #xFF >> 4 = #x0F
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bvlshr(vec![ff, four]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvlshr_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x >> 0 = x
    let result = store.mk_bvlshr(vec![x, zero]);
    assert_eq!(result, x);

    // 0 >> x = 0
    let result2 = store.mk_bvlshr(vec![zero, x]);
    assert_eq!(result2, zero);

    // x >> 8 = 0 (shift >= width)
    let eight = store.mk_bitvec(BigInt::from(8), 8);
    let result3 = store.mk_bvlshr(vec![x, eight]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvashr_constant_folding() {
    let mut store = TermStore::new();

    // #x80 >>> 4 = #xF8 (sign extension, negative)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0xF8), 8);
    let result = store.mk_bvashr(vec![x80, four]);
    assert_eq!(result, expected);

    // #x70 >>> 4 = #x07 (no sign extension, positive)
    let x70 = store.mk_bitvec(BigInt::from(0x70), 8);
    let expected2 = store.mk_bitvec(BigInt::from(0x07), 8);
    let result2 = store.mk_bvashr(vec![x70, four]);
    assert_eq!(result2, expected2);
}

#[test]
fn test_bvashr_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x >>> 0 = x
    let result = store.mk_bvashr(vec![x, zero]);
    assert_eq!(result, x);

    // 0 >>> x = 0
    let result2 = store.mk_bvashr(vec![zero, x]);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvudiv_constant_folding() {
    let mut store = TermStore::new();

    // #x10 / #x04 = #x04
    let x10 = store.mk_bitvec(BigInt::from(0x10), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(4), 8);
    let result = store.mk_bvudiv(vec![x10, four]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvudiv_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x / 1 = x (valid: 1 is provably non-zero)
    let result = store.mk_bvudiv(vec![x, one]);
    assert_eq!(result, x);

    // bvudiv(0, x) must NOT simplify to 0: bvudiv(0, 0) = all_ones per SMT-LIB
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvudiv(vec![zero, x]);
    assert_ne!(
        result2, zero,
        "bvudiv(0, x) must not fold to 0 (x could be 0)"
    );

    // bvudiv(x, x) must NOT simplify to 1: bvudiv(0, 0) = all_ones per SMT-LIB
    let result3 = store.mk_bvudiv(vec![x, x]);
    assert_ne!(
        result3, one,
        "bvudiv(x, x) must not fold to 1 (x could be 0)"
    );
}

#[test]
fn test_bvudiv_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    // bvudiv(7, 0) = all_ones = 255 per SMT-LIB
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(255), 8);
    let result = store.mk_bvudiv(vec![seven, zero]);
    assert_eq!(result, all_ones);

    // bvudiv(0, 0) = all_ones = 255 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvudiv(vec![zero2, zero]);
    assert_eq!(result2, all_ones);
}

#[test]
fn test_bvurem_constant_folding() {
    let mut store = TermStore::new();

    // #x17 % #x05 = #x03 (23 % 5 = 3)
    let x17 = store.mk_bitvec(BigInt::from(0x17), 8);
    let five = store.mk_bitvec(BigInt::from(5), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvurem(vec![x17, five]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvurem_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x % 1 = 0
    let result = store.mk_bvurem(vec![x, one]);
    assert_eq!(result, zero);

    // x % 0 = x
    let result0 = store.mk_bvurem(vec![x, zero]);
    assert_eq!(result0, x);

    // 0 % x = 0
    let result2 = store.mk_bvurem(vec![zero, x]);
    assert_eq!(result2, zero);

    // x % x = 0
    let result3 = store.mk_bvurem(vec![x, x]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvurem_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    // bvurem(7, 0) = 7 per SMT-LIB
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvurem(vec![seven, zero]);
    assert_eq!(result, seven);

    // bvurem(0, 0) = 0 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvurem(vec![zero2, zero]);
    assert_eq!(result2, zero);

    // bvurem(255, 0) = 255 per SMT-LIB
    let ff = store.mk_bitvec(BigInt::from(255), 8);
    let result3 = store.mk_bvurem(vec![ff, zero]);
    assert_eq!(result3, ff);
}
