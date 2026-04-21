// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod csv;
mod io_utils;
mod json;
mod randomization;
#[cfg(test)]
mod tests;

// Security gate for IOExec command execution (Part of #3965).
// Re-exported as `pub` from lib.rs for tla-check/tla-cli consumption.
pub use io_utils::{is_io_exec_allowed, set_io_exec_allowed};

use super::{EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value};

pub(super) fn eval_builtin_io(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    if let Some(value) = randomization::eval(ctx, name, args, span)? {
        return Ok(Some(value));
    }
    if let Some(value) = csv::eval(ctx, name, args, span)? {
        return Ok(Some(value));
    }
    if let Some(value) = json::eval(ctx, name, args, span)? {
        return Ok(Some(value));
    }
    io_utils::eval(ctx, name, args, span)
}

pub(super) fn select_clock_component(
    clock: &Value,
    host: &Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    match clock {
        Value::Func(func) => func
            .apply(host)
            .cloned()
            .ok_or_else(|| EvalError::NotInDomain {
                arg: format!("{host}"),
                func_display: Some(format!("{clock}")),
                span,
            }),
        Value::IntFunc(func) => func
            .apply(host)
            .cloned()
            .ok_or_else(|| EvalError::NotInDomain {
                arg: format!("{host}"),
                func_display: Some(format!("{clock}")),
                span,
            }),
        Value::Record(record) => {
            let field = host
                .as_string()
                .ok_or_else(|| EvalError::type_error("STRING", host, span))?;
            record
                .get(field)
                .cloned()
                .ok_or_else(|| EvalError::NoSuchField {
                    field: field.to_string(),
                    record_display: Some(format!("{clock}")),
                    span,
                })
        }
        _ => Err(EvalError::type_error("Function/Record", clock, span)),
    }
}

pub(super) fn resolve_input_path(ctx: &EvalCtx, filename: &str) -> std::path::PathBuf {
    let path = std::path::PathBuf::from(filename);
    if path.is_absolute() {
        return path;
    }
    if path.exists() {
        return path;
    }

    if let Some(base_dir) = ctx.input_base_dir() {
        let base_joined = base_dir.join(&path);
        if base_joined.exists() {
            return base_joined;
        }
        // Specs sometimes store filenames relative to a repository root
        // (e.g., "specifications/...") rather than spec directory.
        for ancestor in base_dir.ancestors() {
            let candidate = ancestor.join(&path);
            if candidate.exists() {
                return candidate;
            }
        }
        return base_joined;
    }

    if let Ok(cwd) = std::env::current_dir() {
        let cwd_joined = cwd.join(&path);
        if cwd_joined.exists() {
            return cwd_joined;
        }
        // Some tlaplus-examples specs refer to files from repository root
        // (e.g., "specifications/...") while model checking runs in a subdirectory.
        for ancestor in cwd.ancestors() {
            let candidate = ancestor.join(&path);
            if candidate.exists() {
                return candidate;
            }
        }
        return cwd_joined;
    }

    path
}

pub(super) fn json_to_tla_value(json: &serde_json::Value, span: Option<Span>) -> EvalResult<Value> {
    json::json_to_tla_value(json, span)
}

/// Check if vector clock v1 strictly happened-before v2.
/// Both must be records with string keys mapping to integer values.
/// v1 < v2 iff: all components v1[k] <= v2[k], and at least one v1[k] < v2[k].
pub(super) fn vc_happened_before(v1: &Value, v2: &Value) -> bool {
    let (r1, r2) = match (v1.as_record(), v2.as_record()) {
        (Some(a), Some(b)) => (a, b),
        _ => return false,
    };
    let mut all_leq = true;
    let mut any_lt = false;
    // Collect all NameId keys from both clocks (missing = 0)
    let mut keys: Vec<tla_core::NameId> = Vec::new();
    for k in r1.keys() {
        keys.push(k);
    }
    for k in r2.keys() {
        if !keys.contains(&k) {
            keys.push(k);
        }
    }
    for key in &keys {
        let a = r1
            .get_by_id(*key)
            .and_then(tla_value::Value::as_i64)
            .unwrap_or(0);
        let b = r2
            .get_by_id(*key)
            .and_then(tla_value::Value::as_i64)
            .unwrap_or(0);
        if a > b {
            all_leq = false;
            break;
        }
        if a < b {
            any_lt = true;
        }
    }
    all_leq && any_lt
}
