// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector operations.

use std::hash::Hash;

use z4_dpll::api::Term;

use super::expect_result;
use crate::TranslationHost;

/// Bitvector binary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

/// Bitvector unary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Bitvector comparison type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    ULt,
    ULe,
    UGt,
    UGe,
    SLt,
    SLe,
    SGt,
    SGe,
}

/// Bitvector binary operation.
pub fn binop<V>(ctx: &mut impl TranslationHost<V>, op: BinOp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match op {
        BinOp::Add => expect_result(ctx.solver().try_bvadd(a, b), "bv.add"),
        BinOp::Sub => expect_result(ctx.solver().try_bvsub(a, b), "bv.sub"),
        BinOp::Mul => expect_result(ctx.solver().try_bvmul(a, b), "bv.mul"),
        BinOp::UDiv => expect_result(ctx.solver().try_bvudiv(a, b), "bv.udiv"),
        BinOp::SDiv => expect_result(ctx.solver().try_bvsdiv(a, b), "bv.sdiv"),
        BinOp::URem => expect_result(ctx.solver().try_bvurem(a, b), "bv.urem"),
        BinOp::SRem => expect_result(ctx.solver().try_bvsrem(a, b), "bv.srem"),
        BinOp::And => expect_result(ctx.solver().try_bvand(a, b), "bv.and"),
        BinOp::Or => expect_result(ctx.solver().try_bvor(a, b), "bv.or"),
        BinOp::Xor => expect_result(ctx.solver().try_bvxor(a, b), "bv.xor"),
        BinOp::Shl => expect_result(ctx.solver().try_bvshl(a, b), "bv.shl"),
        BinOp::LShr => expect_result(ctx.solver().try_bvlshr(a, b), "bv.lshr"),
        BinOp::AShr => expect_result(ctx.solver().try_bvashr(a, b), "bv.ashr"),
    }
}

/// Bitvector unary operation.
pub fn unary<V>(ctx: &mut impl TranslationHost<V>, op: UnaryOp, a: Term) -> Term
where
    V: Eq + Hash,
{
    match op {
        UnaryOp::Not => expect_result(ctx.solver().try_bvnot(a), "bv.not"),
        UnaryOp::Neg => expect_result(ctx.solver().try_bvneg(a), "bv.neg"),
    }
}

/// Bitvector comparison.
pub fn cmp<V>(ctx: &mut impl TranslationHost<V>, cmp: Cmp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match cmp {
        Cmp::ULt => expect_result(ctx.solver().try_bvult(a, b), "bv.cmp.ult"),
        Cmp::ULe => expect_result(ctx.solver().try_bvule(a, b), "bv.cmp.ule"),
        Cmp::UGt => expect_result(ctx.solver().try_bvugt(a, b), "bv.cmp.ugt"),
        Cmp::UGe => expect_result(ctx.solver().try_bvuge(a, b), "bv.cmp.uge"),
        Cmp::SLt => expect_result(ctx.solver().try_bvslt(a, b), "bv.cmp.slt"),
        Cmp::SLe => expect_result(ctx.solver().try_bvsle(a, b), "bv.cmp.sle"),
        Cmp::SGt => expect_result(ctx.solver().try_bvsgt(a, b), "bv.cmp.sgt"),
        Cmp::SGe => expect_result(ctx.solver().try_bvsge(a, b), "bv.cmp.sge"),
    }
}

/// Bitvector addition.
pub fn add<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Add, a, b)
}

/// Bitvector subtraction.
pub fn sub<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Sub, a, b)
}

/// Bitvector bitwise AND.
pub fn and<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::And, a, b)
}

/// Bitvector bitwise OR.
pub fn or<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Or, a, b)
}

/// Bitvector bitwise NOT.
pub fn not<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Not, a)
}

/// Extract bits `[hi:lo]`.
pub fn extract<V>(ctx: &mut impl TranslationHost<V>, hi: u32, lo: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_bvextract(t, hi, lo), "bv.extract")
}

/// Concatenate two bitvectors.
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_bvconcat(a, b), "bv.concat")
}

/// Extend a bitvector.
pub fn extend<V>(ctx: &mut impl TranslationHost<V>, sign: bool, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    if sign {
        expect_result(ctx.solver().try_bvsignext(t, bits), "bv.signext")
    } else {
        expect_result(ctx.solver().try_bvzeroext(t, bits), "bv.zeroext")
    }
}

/// Zero extension.
pub fn zext<V>(ctx: &mut impl TranslationHost<V>, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    extend(ctx, false, bits, t)
}

/// Sign extension.
pub fn sext<V>(ctx: &mut impl TranslationHost<V>, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    extend(ctx, true, bits, t)
}

// Overflow detection operations

/// Check that a + b does not overflow.
pub fn add_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term, signed: bool) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvadd_no_overflow(a, b, signed),
        "bv.add_no_overflow",
    )
}

/// Check that a + b does not underflow.
pub fn add_no_underflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvadd_no_underflow(a, b),
        "bv.add_no_underflow",
    )
}

/// Check that a - b does not overflow.
pub fn sub_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvsub_no_overflow(a, b),
        "bv.sub_no_overflow",
    )
}

/// Check that a - b does not underflow.
pub fn sub_no_underflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
    signed: bool,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvsub_no_underflow(a, b, signed),
        "bv.sub_no_underflow",
    )
}

/// Check that a * b does not overflow.
pub fn mul_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term, signed: bool) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvmul_no_overflow(a, b, signed),
        "bv.mul_no_overflow",
    )
}

/// Check that a * b does not underflow.
pub fn mul_no_underflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvmul_no_underflow(a, b),
        "bv.mul_no_underflow",
    )
}

/// Check that -a does not overflow.
pub fn neg_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_bvneg_no_overflow(a), "bv.neg_no_overflow")
}

/// Check that a / b does not overflow.
pub fn sdiv_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_bvsdiv_no_overflow(a, b),
        "bv.sdiv_no_overflow",
    )
}
