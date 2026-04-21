// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "z4")]
use std::collections::HashMap;
#[cfg(feature = "z4")]
use std::sync::Arc;

#[cfg(feature = "z4")]
use num_traits::ToPrimitive;
#[cfg(feature = "z4")]
use tla_core::ast::Expr;
#[cfg(feature = "z4")]
use tla_core::Spanned;

#[cfg(feature = "z4")]
use super::{VarInfo, VarSort, Z4EnumError, Z4EnumResult};
#[cfg(feature = "z4")]
use crate::state::State;
#[cfg(feature = "z4")]
use crate::value::intern_string;
#[cfg(feature = "z4")]
use crate::Value;

/// Read a scalar (Bool, Int, or String) value from a z4 model.
/// Returns an error for compound types (Function, Tuple, Heterogeneous).
#[cfg(feature = "z4")]
fn model_get_scalar(
    model: &tla_z4::Model,
    var_name: &str,
    sort: &VarSort,
    string_reverse_map: &HashMap<i64, String>,
) -> Z4EnumResult<Value> {
    match sort {
        VarSort::Bool => {
            let b = model.bool_val(var_name).ok_or_else(|| {
                Z4EnumError::InvalidModel(format!("missing bool value for {}", var_name))
            })?;
            Ok(Value::Bool(b))
        }
        VarSort::Int => {
            let n = model.int_val(var_name).ok_or_else(|| {
                Z4EnumError::InvalidModel(format!("missing int value for {}", var_name))
            })?;
            Ok(Value::Int(n.clone().into()))
        }
        VarSort::String { .. } => {
            let id = model.int_val(var_name).ok_or_else(|| {
                Z4EnumError::InvalidModel(format!("missing string value for {}", var_name))
            })?;
            let id = id.to_i64().ok_or_else(|| {
                Z4EnumError::InvalidModel(format!(
                    "string ID for {} does not fit in i64: {}",
                    var_name, id
                ))
            })?;
            let s = string_reverse_map.get(&id).ok_or_else(|| {
                Z4EnumError::InvalidModel(format!("unknown string ID {} for {}", id, var_name))
            })?;
            // Part of #3287: Route through intern_string() for eager TLC
            // token assignment, matching TLC's UniqueString.uniqueStringOf().
            Ok(Value::String(intern_string(s.as_str())))
        }
        VarSort::Function { .. } | VarSort::Tuple { .. } | VarSort::Heterogeneous { .. } => {
            Err(Z4EnumError::UnsupportedVarType {
                var: var_name.to_string(),
                reason: format!("compound type {:?} not supported as scalar", sort),
            })
        }
    }
}

/// Convert z4 model to TLA2 State
#[cfg(feature = "z4")]
pub(super) fn model_to_state(
    model: &tla_z4::Model,
    var_infos: &HashMap<String, VarInfo>,
    string_reverse_map: &HashMap<i64, String>,
) -> Z4EnumResult<State> {
    use crate::value::FuncValue;
    use num_bigint::BigInt;

    let mut state_pairs: Vec<(Arc<str>, Value)> = Vec::new();

    for (name, info) in var_infos {
        let value = match &info.sort {
            VarSort::Bool | VarSort::Int | VarSort::String { .. } => {
                model_get_scalar(model, name, &info.sort, string_reverse_map)?
            }
            VarSort::Function { domain_keys, range } => {
                // Build function value from per-element variables
                let mut entries: Vec<(Value, Value)> = Vec::new();
                for key in domain_keys {
                    let var_name = format!("{}__{}", name, key);
                    let elem_value = model_get_scalar(model, &var_name, range, string_reverse_map)?;
                    // Convert key to Value for the domain
                    let key_value = if let Ok(n) = key.parse::<i64>() {
                        Value::Int(BigInt::from(n).into())
                    } else if key == "true" {
                        Value::Bool(true)
                    } else if key == "false" {
                        Value::Bool(false)
                    } else {
                        // Part of #3287: eager token assignment for z4 model strings.
                        Value::String(intern_string(key.as_str()))
                    };
                    entries.push((key_value, elem_value));
                }
                // Sort entries by key for FuncValue constructor
                entries.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
                Value::Func(FuncValue::from_sorted_entries(entries).into())
            }
            VarSort::Tuple { element_sorts } => {
                // Build tuple value from per-element variables (1-indexed)
                let mut elements: Vec<Value> = Vec::new();
                for (i, elem_sort) in element_sorts.iter().enumerate() {
                    let var_name = format!("{}__{}", name, i + 1);
                    let elem_value =
                        model_get_scalar(model, &var_name, elem_sort, string_reverse_map)?;
                    elements.push(elem_value);
                }
                Value::Tuple(elements.into())
            }
            // Heterogeneous vars should never reach model_to_state - early error return
            VarSort::Heterogeneous { reason } => {
                return Err(Z4EnumError::UnsupportedVarType {
                    var: name.clone(),
                    reason: format!("heterogeneous type in model: {}", reason),
                });
            }
        };
        state_pairs.push((info.name.clone(), value));
    }

    Ok(State::from_pairs(state_pairs))
}

/// Add blocking clause to exclude the current model
#[cfg(feature = "z4")]
pub(super) fn add_blocking_clause(
    translator: &mut tla_z4::Z4Translator,
    model: &tla_z4::Model,
    var_infos: &HashMap<String, VarInfo>,
    string_reverse_map: &HashMap<i64, String>,
) -> Z4EnumResult<()> {
    use tla_core::{FileId, Span};

    // Build NOT(current_assignment) as a blocking clause
    // For scalar variables: NOT(x = v1 /\\ y = v2 /\\ ...) = (x != v1) \/ (y != v2) \/ ...
    // We assert this as a new constraint

    let span = Span::new(FileId(0), 0, 0);
    let mut disequality_exprs = Vec::new();

    for (name, info) in var_infos {
        match &info.sort {
            VarSort::Bool => {
                if let Some(b) = model.bool_val(name) {
                    // x != b
                    let var_expr = Spanned::new(
                        Expr::Ident(name.clone(), tla_core::name_intern::NameId::INVALID),
                        span,
                    );
                    let val_expr = Spanned::new(Expr::Bool(b), span);
                    let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                    disequality_exprs.push(Spanned::new(neq_expr, span));
                }
            }
            VarSort::Int => {
                if let Some(n) = model.int_val(name) {
                    // x != n
                    let var_expr = Spanned::new(
                        Expr::Ident(name.clone(), tla_core::name_intern::NameId::INVALID),
                        span,
                    );
                    let val_expr = Spanned::new(Expr::Int(n.clone()), span);
                    let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                    disequality_exprs.push(Spanned::new(neq_expr, span));
                }
            }
            VarSort::String { .. } => {
                if let Some(id) = model.int_val(name) {
                    let Some(id) = id.to_i64() else {
                        continue;
                    };
                    // x != "s" (use string literal for semantic correctness)
                    if let Some(s) = string_reverse_map.get(&id) {
                        let var_expr = Spanned::new(
                            Expr::Ident(name.clone(), tla_core::name_intern::NameId::INVALID),
                            span,
                        );
                        let val_expr = Spanned::new(Expr::String(s.clone()), span);
                        let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                        disequality_exprs.push(Spanned::new(neq_expr, span));
                    }
                }
            }
            VarSort::Function { domain_keys, range } => {
                // For functions, add disequality for each element
                for key in domain_keys {
                    let var_name = format!("{}__{}", name, key);
                    match range.as_ref() {
                        VarSort::Bool => {
                            if let Some(b) = model.bool_val(&var_name) {
                                // f__key != b
                                let var_expr = Spanned::new(
                                    Expr::Ident(
                                        var_name.clone(),
                                        tla_core::name_intern::NameId::INVALID,
                                    ),
                                    span,
                                );
                                let val_expr = Spanned::new(Expr::Bool(b), span);
                                let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                disequality_exprs.push(Spanned::new(neq_expr, span));
                            }
                        }
                        VarSort::Int => {
                            if let Some(n) = model.int_val(&var_name) {
                                let var_expr = Spanned::new(
                                    Expr::Ident(
                                        var_name.clone(),
                                        tla_core::name_intern::NameId::INVALID,
                                    ),
                                    span,
                                );
                                let val_expr = Spanned::new(Expr::Int(n.clone()), span);
                                let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                disequality_exprs.push(Spanned::new(neq_expr, span));
                            }
                        }
                        VarSort::String { .. } => {
                            if let Some(id) = model.int_val(&var_name) {
                                let Some(id) = id.to_i64() else {
                                    continue;
                                };
                                if let Some(s) = string_reverse_map.get(&id) {
                                    let var_expr = Spanned::new(
                                        Expr::Ident(
                                            var_name.clone(),
                                            tla_core::name_intern::NameId::INVALID,
                                        ),
                                        span,
                                    );
                                    let val_expr = Spanned::new(Expr::String(s.clone()), span);
                                    let neq_expr =
                                        Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                    disequality_exprs.push(Spanned::new(neq_expr, span));
                                }
                            }
                        }
                        VarSort::Function { .. }
                        | VarSort::Tuple { .. }
                        | VarSort::Heterogeneous { .. } => {
                            // Nested functions/tuples/heterogeneous not supported, skip
                        }
                    }
                }
            }
            VarSort::Tuple { element_sorts } => {
                // For tuples, add disequality for each element (1-indexed)
                for (i, elem_sort) in element_sorts.iter().enumerate() {
                    let idx = i + 1;
                    let var_name = format!("{}__{}", name, idx);
                    match elem_sort {
                        VarSort::Bool => {
                            if let Some(b) = model.bool_val(&var_name) {
                                let var_expr = Spanned::new(
                                    Expr::Ident(
                                        var_name.clone(),
                                        tla_core::name_intern::NameId::INVALID,
                                    ),
                                    span,
                                );
                                let val_expr = Spanned::new(Expr::Bool(b), span);
                                let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                disequality_exprs.push(Spanned::new(neq_expr, span));
                            }
                        }
                        VarSort::Int => {
                            if let Some(n) = model.int_val(&var_name) {
                                let var_expr = Spanned::new(
                                    Expr::Ident(
                                        var_name.clone(),
                                        tla_core::name_intern::NameId::INVALID,
                                    ),
                                    span,
                                );
                                let val_expr = Spanned::new(Expr::Int(n.clone()), span);
                                let neq_expr = Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                disequality_exprs.push(Spanned::new(neq_expr, span));
                            }
                        }
                        VarSort::String { .. } => {
                            if let Some(id) = model.int_val(&var_name) {
                                let Some(id) = id.to_i64() else {
                                    continue;
                                };
                                if let Some(s) = string_reverse_map.get(&id) {
                                    let var_expr = Spanned::new(
                                        Expr::Ident(
                                            var_name.clone(),
                                            tla_core::name_intern::NameId::INVALID,
                                        ),
                                        span,
                                    );
                                    let val_expr = Spanned::new(Expr::String(s.clone()), span);
                                    let neq_expr =
                                        Expr::Neq(Box::new(var_expr), Box::new(val_expr));
                                    disequality_exprs.push(Spanned::new(neq_expr, span));
                                }
                            }
                        }
                        VarSort::Function { .. }
                        | VarSort::Tuple { .. }
                        | VarSort::Heterogeneous { .. } => {
                            // Nested functions/tuples/heterogeneous not supported, skip
                        }
                    }
                }
            }
            // Heterogeneous vars should never reach add_blocking_clause - early error return
            VarSort::Heterogeneous { .. } => {
                // Skip - heterogeneous vars should have caused an early error
            }
        }
    }

    if disequality_exprs.is_empty() {
        return Err(Z4EnumError::TranslationFailed(
            "cannot build blocking clause: all variables are compound types".to_string(),
        ));
    }

    // Build disjunction: (x != v1) \/ (y != v2) \/ ...
    let mut blocking_expr = disequality_exprs
        .pop()
        .expect("disequality_exprs non-empty after early return");
    while let Some(expr) = disequality_exprs.pop() {
        blocking_expr = Spanned::new(Expr::Or(Box::new(expr), Box::new(blocking_expr)), span);
    }

    // Translate and assert the blocking clause
    let blocking_term = translator
        .translate_bool(&blocking_expr)
        .map_err(|e| Z4EnumError::TranslationFailed(format!("blocking clause failed: {}", e)))?;
    translator.assert(blocking_term);

    Ok(())
}
