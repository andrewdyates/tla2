// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator builder modules.

use std::hash::Hash;

use z4_dpll::api::{SolverError, Term};

use crate::TranslationHost;

pub mod arith;
pub mod array;
pub mod bv;
pub mod dt;
pub mod fp;
pub mod seq;
pub mod string;
pub mod uf;

pub(crate) fn expect_result<T>(result: Result<T, SolverError>, operation: &'static str) -> T {
    result.unwrap_or_else(|e| panic!("z4-translate {operation} failed: {e}"))
}

/// N-ary boolean operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaryBoolOp {
    And,
    Or,
}

/// Comparison operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comparison {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// N-ary boolean builder.
pub fn bool_nary<V>(ctx: &mut impl TranslationHost<V>, op: NaryBoolOp, terms: &[Term]) -> Term
where
    V: Eq + Hash,
{
    match op {
        NaryBoolOp::And => expect_result(ctx.solver().try_and_many(terms), "bool_nary.and"),
        NaryBoolOp::Or => expect_result(ctx.solver().try_or_many(terms), "bool_nary.or"),
    }
}

/// Boolean negation.
pub fn bool_not<V>(ctx: &mut impl TranslationHost<V>, t: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_not(t), "bool_not")
}

/// Boolean implication.
pub fn implies<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_implies(a, b), "implies")
}

/// If-then-else.
pub fn ite<V>(ctx: &mut impl TranslationHost<V>, cond: Term, then_: Term, else_: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_ite(cond, then_, else_), "ite")
}

/// Boolean exclusive-or.
pub fn xor<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_xor(a, b), "xor")
}

/// Comparison builder.
pub fn compare<V>(
    ctx: &mut impl TranslationHost<V>,
    cmp: Comparison,
    left: Term,
    right: Term,
) -> Term
where
    V: Eq + Hash,
{
    match cmp {
        Comparison::Lt => expect_result(ctx.solver().try_lt(left, right), "compare.lt"),
        Comparison::Le => expect_result(ctx.solver().try_le(left, right), "compare.le"),
        Comparison::Gt => expect_result(ctx.solver().try_gt(left, right), "compare.gt"),
        Comparison::Ge => expect_result(ctx.solver().try_ge(left, right), "compare.ge"),
        Comparison::Eq => expect_result(ctx.solver().try_eq(left, right), "compare.eq"),
        Comparison::Ne => expect_result(ctx.solver().try_neq(left, right), "compare.ne"),
    }
}

/// Distinct (pairwise disequality) builder.
pub fn distinct<V>(ctx: &mut impl TranslationHost<V>, terms: &[Term]) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_distinct(terms), "distinct")
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "ops_tests.rs"]
mod tests;
