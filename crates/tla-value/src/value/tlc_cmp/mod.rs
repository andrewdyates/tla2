// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core directional TLC comparison (`tlc_cmp`) for `Value`.
//!
//! Implements TLC's `compareTo` rules faithfully, including direction-observable
//! behavior and type-specific error handling. Sort helpers are in `tlc_sort`,
//! iteration APIs are in `tlc_iter`. Split from original `tlc_cmp.rs` as part
//! of #3309, decomposed into family helpers as part of #3336.

mod functions;
mod model_values;
mod scalars;
mod sets;
mod structured;

use super::Value;
use crate::error::EvalResult;
use std::cmp::Ordering;

impl Value {
    /// Directional TLC comparison `a.compareTo(b)`.
    pub(super) fn tlc_cmp(a: &Value, b: &Value) -> EvalResult<Ordering> {
        // Model values first — early return for all model-value rules.
        if let Some(ord) = model_values::cmp_model_values(a, b)? {
            return Ok(ord);
        }

        // Dispatch by value family.
        match a {
            Value::Bool(_) => scalars::cmp_bool(a, b),
            Value::SmallInt(_) | Value::Int(_) => scalars::cmp_int(a, b),
            Value::String(_) => scalars::cmp_string(a, b),
            Value::Tuple(_) | Value::Seq(_) => structured::cmp_tuple_seq(a, b),
            Value::Record(_) => structured::cmp_record(a, b),
            Value::Func(_) | Value::IntFunc(_) => functions::cmp_functions(a, b),
            Value::Interval(_) => sets::cmp_interval(a, b),
            _ if a.is_set() => sets::cmp_sets(a, b),
            _ => Err(Self::tlc_cmp_err(format!(
                "Attempted to compare incompatible values {a:?} and {b:?}"
            ))),
        }
    }
}
