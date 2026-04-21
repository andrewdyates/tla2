// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLCGet/TLCSet string-key handlers, extracted from builtin_tlc.rs (#3073 file split).

use super::{
    eval, process_start_time, tlc_register_get, tlc_register_set, tlc_registers_get_all, EvalCtx,
    EvalError, EvalResult, Expr, FuncValue, Span, Spanned, Value,
};

use num_traits::ToPrimitive;
use std::sync::Arc;

// Part of #3962 Wave 25: PROCESS_START_TIME thread_local has been consolidated
// into EVAL_DEBUG_STATE in eval_debug.rs. Access via process_start_time() accessor.

/// Simple date string without chrono dependency (YYYY-MM-DD format).
fn chrono_lite_date() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let days = (secs / 86400) as i64;
    let (year, month, day) = days_to_ymd(days);
    format!("{year:04}-{month:02}-{day:02}")
}

/// Convert days since Unix epoch to (year, month, day).
/// Algorithm from http://howardhinnant.github.io/date_algorithms.html
fn days_to_ymd(days: i64) -> (i64, u32, u32) {
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u32;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d)
}

fn current_duration_seconds() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    let start = process_start_time();
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|now| now.as_secs() as i64 - start)
        .unwrap_or(0)
}

/// Evaluate TLCGet(key) for string keys (config, level, all, stats, etc.)
pub(super) fn eval_tlcget(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let idx = eval(ctx, &args[0])?;

    if let Some(key) = idx.as_string() {
        match key {
            "config" => {
                let config = &ctx.shared.tlc_config;
                let install_path = std::env::current_exe()
                    .map(|p| p.display().to_string())
                    .unwrap_or_default();
                return Ok(Some(Value::record([
                    ("mode", Value::string(&*config.mode)),
                    ("depth", Value::int(config.depth)),
                    ("deadlock", Value::Bool(config.deadlock)),
                    ("traces", Value::int(config.traces)),
                    ("seed", Value::int(config.seed)),
                    ("worker", Value::int(config.worker)),
                    ("install", Value::string(&install_path)),
                ])));
            }
            "level" => {
                crate::cache::dep_tracking::record_tlc_level_read(ctx);
                return Ok(Some(Value::int(ctx.tlc_level as i64)));
            }
            "all" => {
                let regs = tlc_registers_get_all();
                if regs.is_empty() {
                    return Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                        Vec::new(),
                    )))));
                }
                // Phase 1A (#3073): Vec+from_sorted_entries replaces OrdSet/OrdMap.
                let mut entries: Vec<(Value, Value)> = regs
                    .into_iter()
                    .map(|(k, v)| (Value::int(k), Value::seq(vec![v])))
                    .collect();
                entries.sort_by(|(a, _), (b, _)| a.cmp(b));
                return Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                    entries,
                )))));
            }
            "stats" => {
                if let Some(stats) = ctx.tlc_runtime_stats() {
                    crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
                    return Ok(Some(Value::record([
                        ("diameter", Value::int(stats.diameter)),
                        ("generated", Value::int(stats.generated)),
                        ("distinct", Value::int(stats.distinct)),
                        ("queue", Value::int(stats.queue)),
                        ("traces", Value::int(stats.traces)),
                    ])));
                }
                crate::cache::dep_tracking::record_tlc_level_read(ctx);
                return Ok(Some(Value::record([
                    ("diameter", Value::int(ctx.tlc_level as i64)),
                    ("generated", Value::int(0)),
                    ("distinct", Value::int(0)),
                    ("queue", Value::int(0)),
                    ("traces", Value::int(0)),
                ])));
            }
            "action" => {
                crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
                if let Some(action) = ctx.tlc_action_context() {
                    let context = Value::record(action.params.iter().filter_map(|name| {
                        ctx.lookup(name.as_ref()).map(|value| (name.clone(), value))
                    }));
                    return Ok(Some(Value::record([
                        ("name", Value::string(&*action.name)),
                        ("context", context),
                    ])));
                }
                return Ok(Some(Value::record([
                    ("name", Value::string("")),
                    ("context", Value::record(Vec::<(&str, Value)>::new())),
                ])));
            }
            "revision" => {
                use std::time::{SystemTime, UNIX_EPOCH};
                let ts = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|d| d.as_secs() as i64)
                    .unwrap_or(0);
                return Ok(Some(Value::record([
                    ("tag", Value::string("tla2")),
                    ("timestamp", Value::int(ts)),
                    ("date", Value::string(chrono_lite_date())),
                    ("count", Value::int(0)),
                ])));
            }
            "duration" => {
                crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
                return Ok(Some(Value::int(current_duration_seconds())));
            }
            "diameter" => {
                if let Some(stats) = ctx.tlc_runtime_stats() {
                    crate::cache::dep_tracking::mark_runtime_nondeterministic(ctx);
                    return Ok(Some(Value::int(stats.diameter)));
                }
                crate::cache::dep_tracking::record_tlc_level_read(ctx);
                return Ok(Some(Value::int(ctx.tlc_level as i64)));
            }
            _ if key.starts_with("-D") => {
                return Ok(Some(Value::string("")));
            }
            _ => {
                return Err(EvalError::Internal {
                    message: format!("TLCGet: unknown key \"{key}\""),
                    span,
                });
            }
        }
    }

    // Handle integer register access
    if let Some(i) = idx.to_bigint().and_then(|n| n.to_i64()) {
        if i < 0 {
            return Err(EvalError::Internal {
                message: format!("TLCGet: register index must be non-negative, got {i}"),
                span,
            });
        }
        match tlc_register_get(i) {
            Some(val) => return Ok(Some(val)),
            None => {
                return Err(EvalError::Internal {
                    message: format!("TLCGet: register {i} not set"),
                    span,
                });
            }
        }
    }

    Err(EvalError::type_error(
        "String or Int",
        &idx,
        Some(args[0].span),
    ))
}

/// Evaluate TLCSet(key, val) for string and integer keys.
pub(super) fn eval_tlcset(
    ctx: &EvalCtx,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let idx = eval(ctx, &args[0])?;
    let val = eval(ctx, &args[1])?;

    if let Some(key) = idx.as_string() {
        match key {
            "exit" => {
                if matches!(val, Value::Bool(true)) {
                    return Err(EvalError::ExitRequested { span });
                }
                return Ok(Some(Value::Bool(true)));
            }
            _ => {
                return Err(EvalError::Internal {
                    message: format!("TLCSet: unknown key \"{key}\""),
                    span,
                });
            }
        }
    }

    if let Some(i) = idx.to_bigint().and_then(|n| n.to_i64()) {
        if i < 0 {
            return Err(EvalError::Internal {
                message: format!("TLCSet: register index must be non-negative, got {i}"),
                span,
            });
        }
        tlc_register_set(i, val);
        return Ok(Some(Value::Bool(true)));
    }

    Err(EvalError::type_error(
        "String or Int",
        &idx,
        Some(args[0].span),
    ))
}
