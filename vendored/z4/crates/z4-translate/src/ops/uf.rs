// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Uninterpreted function operations.

use std::hash::Hash;

use z4_dpll::api::{FuncDecl, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Declare or retrieve an uninterpreted function.
///
/// Uses the context's function declaration cache so repeated calls
/// with the same name return the same `FuncDecl` without re-declaring.
///
/// # Arguments
/// * `ctx` - Translation context
/// * `name` - Function name
/// * `domain` - Argument sorts
/// * `range` - Return sort
///
/// # Returns
/// A function declaration that can be applied to arguments.
pub fn declare<V>(
    ctx: &mut impl TranslationHost<V>,
    name: &str,
    domain: &[Sort],
    range: Sort,
) -> FuncDecl
where
    V: Eq + Hash,
{
    ctx.declare_or_get_fun(name, domain, range)
}

/// Apply an uninterpreted function to arguments.
///
/// # Arguments
/// * `ctx` - Translation context
/// * `func` - The function declaration
/// * `args` - Arguments to apply
///
/// # Returns
/// The function application term.
pub fn apply<V>(ctx: &mut impl TranslationHost<V>, func: &FuncDecl, args: &[Term]) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_apply(func, args), "uf.apply")
}

#[cfg(test)]
#[path = "uf_tests.rs"]
mod tests;
