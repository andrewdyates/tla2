// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::collections::HashMap;

use z4_dpll::api::SolverError;

use super::context::ExecutionContext;
use super::ModelValue;

pub(super) fn render_model_values(values: HashMap<String, ModelValue>) -> HashMap<String, String> {
    values
        .into_iter()
        .map(|(name, value)| (name, value.to_string()))
        .collect()
}

/// Extract model from solver after SAT result.
pub(super) fn extract_model_typed(
    ctx: &ExecutionContext,
) -> Result<HashMap<String, ModelValue>, SolverError> {
    ctx.solver.try_get_model_map()
}

/// Extract get-value results from solver after SAT (#1977).
///
/// Evaluates all terms collected from GetValue constraints and returns
/// typed values keyed by expression string.
pub(super) fn extract_get_values_typed(
    ctx: &ExecutionContext,
) -> Result<HashMap<String, ModelValue>, SolverError> {
    if ctx.get_value_terms.is_empty() {
        return Ok(HashMap::new());
    }

    // Collect just the terms for batch evaluation
    let terms = ctx
        .get_value_terms
        .iter()
        .map(|(_, t)| t.clone())
        .collect::<Vec<_>>();

    let model_values = ctx.solver.try_get_values(&terms)?;
    let mut values = HashMap::with_capacity(model_values.len());
    for ((expr_str, _), model_value) in ctx.get_value_terms.iter().zip(model_values.into_iter()) {
        values.insert(expr_str.clone(), model_value);
    }
    Ok(values)
}
