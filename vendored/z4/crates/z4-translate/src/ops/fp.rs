// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point operations.

use std::hash::Hash;

use z4_dpll::api::Term;

use super::expect_result;
use crate::TranslationHost;

/// FP rounding mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundingMode {
    /// Round to nearest, ties to even.
    Rne,
    /// Round to nearest, ties away from zero.
    Rna,
    /// Round toward positive infinity.
    Rtp,
    /// Round toward negative infinity.
    Rtn,
    /// Round toward zero.
    Rtz,
}

impl RoundingMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Rne => "RNE",
            Self::Rna => "RNA",
            Self::Rtp => "RTP",
            Self::Rtn => "RTN",
            Self::Rtz => "RTZ",
        }
    }
}

/// FP binary arithmetic operation (requires rounding mode).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// FP comparison predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// FP classification predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassPred {
    IsNaN,
    IsInfinite,
    IsZero,
    IsNormal,
    IsSubnormal,
    IsPositive,
    IsNegative,
}

/// Create a rounding mode term.
pub fn rounding_mode<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.rounding_mode",
    )
}

/// FP binary arithmetic with rounding mode.
pub fn binop<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    op: BinOp,
    a: Term,
    b: Term,
) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.binop.rounding_mode",
    );
    match op {
        BinOp::Add => expect_result(ctx.solver().try_fp_add(rm_term, a, b), "fp.add"),
        BinOp::Sub => expect_result(ctx.solver().try_fp_sub(rm_term, a, b), "fp.sub"),
        BinOp::Mul => expect_result(ctx.solver().try_fp_mul(rm_term, a, b), "fp.mul"),
        BinOp::Div => expect_result(ctx.solver().try_fp_div(rm_term, a, b), "fp.div"),
    }
}

/// FP addition with rounding mode.
pub fn add<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Add, a, b)
}

/// FP subtraction with rounding mode.
pub fn sub<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Sub, a, b)
}

/// FP multiplication with rounding mode.
pub fn mul<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Mul, a, b)
}

/// FP division with rounding mode.
pub fn div<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Div, a, b)
}

/// FP square root with rounding mode.
pub fn sqrt<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.sqrt.rounding_mode",
    );
    expect_result(ctx.solver().try_fp_sqrt(rm_term, a), "fp.sqrt")
}

/// FP fused multiply-add with rounding mode: `a * b + c` with single rounding.
pub fn fma<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    a: Term,
    b: Term,
    c: Term,
) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.fma.rounding_mode",
    );
    expect_result(ctx.solver().try_fp_fma(rm_term, a, b, c), "fp.fma")
}

/// FP IEEE 754 remainder (no rounding mode).
pub fn rem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_rem(a, b), "fp.rem")
}

/// FP round-to-integral with rounding mode.
pub fn round_to_integral<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.round_to_integral.rounding_mode",
    );
    expect_result(
        ctx.solver().try_fp_round_to_integral(rm_term, a),
        "fp.round_to_integral",
    )
}

/// FP absolute value.
pub fn abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_abs(a), "fp.abs")
}

/// FP negation.
pub fn neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_neg(a), "fp.neg")
}

/// FP comparison predicate.
pub fn cmp<V>(ctx: &mut impl TranslationHost<V>, cmp: Cmp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match cmp {
        Cmp::Eq => expect_result(ctx.solver().try_fp_eq(a, b), "fp.cmp.eq"),
        Cmp::Lt => expect_result(ctx.solver().try_fp_lt(a, b), "fp.cmp.lt"),
        Cmp::Le => expect_result(ctx.solver().try_fp_le(a, b), "fp.cmp.le"),
        Cmp::Gt => expect_result(ctx.solver().try_fp_gt(a, b), "fp.cmp.gt"),
        Cmp::Ge => expect_result(ctx.solver().try_fp_ge(a, b), "fp.cmp.ge"),
    }
}

/// FP classification predicate.
pub fn classify<V>(ctx: &mut impl TranslationHost<V>, pred: ClassPred, a: Term) -> Term
where
    V: Eq + Hash,
{
    match pred {
        ClassPred::IsNaN => expect_result(ctx.solver().try_fp_is_nan(a), "fp.classify.is_nan"),
        ClassPred::IsInfinite => expect_result(
            ctx.solver().try_fp_is_infinite(a),
            "fp.classify.is_infinite",
        ),
        ClassPred::IsZero => expect_result(ctx.solver().try_fp_is_zero(a), "fp.classify.is_zero"),
        ClassPred::IsNormal => {
            expect_result(ctx.solver().try_fp_is_normal(a), "fp.classify.is_normal")
        }
        ClassPred::IsSubnormal => expect_result(
            ctx.solver().try_fp_is_subnormal(a),
            "fp.classify.is_subnormal",
        ),
        ClassPred::IsPositive => expect_result(
            ctx.solver().try_fp_is_positive(a),
            "fp.classify.is_positive",
        ),
        ClassPred::IsNegative => expect_result(
            ctx.solver().try_fp_is_negative(a),
            "fp.classify.is_negative",
        ),
    }
}

/// FP minimum.
pub fn min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_min(a, b), "fp.min")
}

/// FP maximum.
pub fn max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_max(a, b), "fp.max")
}

/// FP +infinity constant.
pub fn plus_infinity<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_plus_infinity(eb, sb)
}

/// FP -infinity constant.
pub fn minus_infinity<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_minus_infinity(eb, sb)
}

/// FP NaN constant.
pub fn nan<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_nan(eb, sb)
}

/// FP +zero constant.
pub fn plus_zero<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_plus_zero(eb, sb)
}

/// FP -zero constant.
pub fn minus_zero<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_minus_zero(eb, sb)
}

/// Convert FP to signed bitvector.
pub fn to_sbv<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, x: Term, width: u32) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.to_sbv.rounding_mode",
    );
    expect_result(ctx.solver().try_fp_to_sbv(rm_term, x, width), "fp.to_sbv")
}

/// Convert FP to unsigned bitvector.
pub fn to_ubv<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, x: Term, width: u32) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.to_ubv.rounding_mode",
    );
    expect_result(ctx.solver().try_fp_to_ubv(rm_term, x, width), "fp.to_ubv")
}

/// Convert FP to real.
pub fn to_real<V>(ctx: &mut impl TranslationHost<V>, x: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_fp_to_real(x), "fp.to_real")
}

/// Convert bitvector to FP.
pub fn from_bv<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    bv: Term,
    eb: u32,
    sb: u32,
) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.from_bv.rounding_mode",
    );
    expect_result(ctx.solver().try_bv_to_fp(rm_term, bv, eb, sb), "fp.from_bv")
}

/// Convert FP to different precision.
pub fn to_fp<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    fp: Term,
    eb: u32,
    sb: u32,
) -> Term
where
    V: Eq + Hash,
{
    let rm_term = expect_result(
        ctx.solver().try_fp_rounding_mode(rm.as_str()),
        "fp.to_fp.rounding_mode",
    );
    expect_result(ctx.solver().try_fp_to_fp(rm_term, fp, eb, sb), "fp.to_fp")
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "fp_tests.rs"]
mod tests;
