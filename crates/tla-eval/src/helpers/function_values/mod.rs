// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function definition, application, and EXCEPT evaluation.
//!
//! Handles `[x \in S |-> expr]`, `f[x]`, and `[f EXCEPT ![x] = y]` forms
//! including lazy functions over infinite domains (Nat, Int, Real).
//!
//! Split into sub-modules by responsibility (Part of #3423):
//! - `def` — function definition and eager materialization
//! - `lazy` — shared lazy-function binding helpers
//! - `apply` — function application (`f[x]`) including borrowed read fast path
//! - `except` — EXCEPT evaluation and lazy-function EXCEPT handlers

mod apply;
mod def;
mod except;
mod lazy;

// Re-export the crate-facing API surface unchanged.
#[cfg(test)]
pub(crate) use apply::apply_resolved_func_value;
pub(crate) use apply::{apply_func_value_eager, eval_func_apply, try_borrow_materialized_read};
pub(crate) use def::eval_func_def;
pub(crate) use except::{
    apply_resolved_except_spec, eval_except, ResolvedExceptPathElement, TirLazyExceptHandler,
};
