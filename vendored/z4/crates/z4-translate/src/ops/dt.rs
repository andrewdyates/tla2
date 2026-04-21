// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype operations.
//!
//! Provides constructor application, field selection, and constructor testing
//! for algebraic datatypes (structs and enums).

use std::hash::Hash;

use z4_dpll::api::{DatatypeSort, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Declare a datatype with the solver.
pub fn declare<V>(ctx: &mut impl TranslationHost<V>, dt: &DatatypeSort)
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_declare_datatype(dt), "dt.declare");
}

/// Apply a datatype constructor.
///
/// Requires the datatype to have been previously declared via [`declare`].
pub fn constructor<V>(
    ctx: &mut impl TranslationHost<V>,
    dt: &DatatypeSort,
    ctor_name: &str,
    args: &[Term],
) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_datatype_constructor(dt, ctor_name, args),
        "dt.constructor",
    )
}

/// Select a field from a datatype expression.
///
/// The `selector_name` must match a field name from the datatype declaration.
pub fn selector<V>(
    ctx: &mut impl TranslationHost<V>,
    selector_name: &str,
    expr: Term,
    result_sort: Sort,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver()
            .try_datatype_selector(selector_name, expr, result_sort),
        "dt.selector",
    )
}

/// Test if an expression was constructed with a specific constructor.
///
/// Returns a Bool term that is true iff `expr` matches `ctor_name`.
pub fn tester<V>(ctx: &mut impl TranslationHost<V>, ctor_name: &str, expr: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_datatype_tester(ctor_name, expr),
        "dt.tester",
    )
}

#[cfg(test)]
#[path = "dt_tests.rs"]
mod tests;
