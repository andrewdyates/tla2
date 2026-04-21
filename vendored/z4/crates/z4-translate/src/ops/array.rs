// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array operations.

use std::hash::Hash;

use z4_dpll::api::{Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Read from array at index (select).
pub fn select<V>(ctx: &mut impl TranslationHost<V>, arr: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_select(arr, idx), "array.select")
}

/// Write to array at index (store).
pub fn store<V>(ctx: &mut impl TranslationHost<V>, arr: Term, idx: Term, val: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_store(arr, idx, val), "array.store")
}

/// Create a constant array.
pub fn const_array<V>(ctx: &mut impl TranslationHost<V>, idx_sort: Sort, val: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        ctx.solver().try_const_array(idx_sort, val),
        "array.const_array",
    )
}
