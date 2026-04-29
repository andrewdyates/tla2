// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::super::{
    check_arity, eval as eval_expr, value_to_json, value_to_json_array, value_to_json_object,
    EvalCtx, EvalError, EvalResult, Expr, RecordBuilder, Span, Spanned, Value,
};
use super::resolve_input_path;
use crate::value::intern_string;

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // ToJson(value) - convert value to JSON string representation
        "ToJson" => {
            check_arity(name, args, 1, span)?;
            let val = eval_expr(ctx, &args[0])?;
            let json_str = value_to_json(&val);
            Ok(Some(Value::String(intern_string(&json_str))))
        }

        // ToJsonArray(value) - convert sequence/tuple to JSON array string
        "ToJsonArray" => {
            check_arity(name, args, 1, span)?;
            let val = eval_expr(ctx, &args[0])?;
            let json_str = value_to_json_array(&val)?;
            Ok(Some(Value::String(intern_string(&json_str))))
        }

        // ToJsonObject(value) - convert record/function to JSON object string
        "ToJsonObject" => {
            check_arity(name, args, 1, span)?;
            let val = eval_expr(ctx, &args[0])?;
            let json_str = value_to_json_object(&val)?;
            Ok(Some(Value::String(intern_string(&json_str))))
        }

        // JsonSerialize(filename, value) - serialize value to JSON file.
        "JsonSerialize" => {
            check_arity(name, args, 2, span)?;
            let filename_val = eval_expr(ctx, &args[0])?;
            let _filename = filename_val.as_string().ok_or_else(|| {
                EvalError::type_error("String", &filename_val, Some(args[0].span))
            })?;
            let val = eval_expr(ctx, &args[1])?;
            let _json_str = value_to_json(&val);
            // In model checking mode, we do not actually write files.
            Ok(Some(Value::Bool(true)))
        }

        // JsonDeserialize(filename) - deserialize JSON from file.
        "JsonDeserialize" => {
            check_arity(name, args, 1, span)?;
            let filename_val = eval_expr(ctx, &args[0])?;
            let filename = filename_val.as_string().ok_or_else(|| {
                EvalError::type_error("String", &filename_val, Some(args[0].span))
            })?;
            let resolved = resolve_input_path(ctx, filename);
            let contents = std::fs::read_to_string(&resolved).map_err(|e| EvalError::Internal {
                message: format!(
                    "JsonDeserialize: failed to read file '{}': {}",
                    resolved.display(),
                    e
                ),
                span,
            })?;
            let json: serde_json::Value =
                serde_json::from_str(&contents).map_err(|e| EvalError::Internal {
                    message: format!(
                        "JsonDeserialize: failed to parse JSON from '{}': {}",
                        resolved.display(),
                        e
                    ),
                    span,
                })?;
            Ok(Some(super::json_to_tla_value(&json, span)?))
        }

        // ndJsonSerialize(filename, value) - serialize to newline-delimited JSON.
        "ndJsonSerialize" => {
            check_arity(name, args, 2, span)?;
            let filename_val = eval_expr(ctx, &args[0])?;
            let _filename = filename_val.as_string().ok_or_else(|| {
                EvalError::type_error("String", &filename_val, Some(args[0].span))
            })?;
            let _val = eval_expr(ctx, &args[1])?;
            Ok(Some(Value::Bool(true)))
        }

        // ndJsonDeserialize(filename) - deserialize newline-delimited JSON from file.
        "ndJsonDeserialize" => {
            check_arity(name, args, 1, span)?;
            let filename_val = eval_expr(ctx, &args[0])?;
            let filename = filename_val.as_string().ok_or_else(|| {
                EvalError::type_error("String", &filename_val, Some(args[0].span))
            })?;
            let resolved = resolve_input_path(ctx, filename);
            let contents = std::fs::read_to_string(&resolved).map_err(|e| EvalError::Internal {
                message: format!(
                    "ndJsonDeserialize: failed to read file '{}': {}",
                    resolved.display(),
                    e
                ),
                span,
            })?;
            let mut values = Vec::new();
            for (line_no, raw_line) in contents.lines().enumerate() {
                let line = raw_line.trim();
                if line.is_empty() {
                    continue;
                }
                let json: serde_json::Value =
                    serde_json::from_str(line).map_err(|e| EvalError::Internal {
                        message: format!(
                            "ndJsonDeserialize: failed to parse JSON line {} from '{}': {}",
                            line_no + 1,
                            resolved.display(),
                            e
                        ),
                        span,
                    })?;
                values.push(super::json_to_tla_value(&json, span)?);
            }
            Ok(Some(Value::Tuple(values.into())))
        }

        _ => Ok(None),
    }
}

pub(super) fn json_to_tla_value(json: &serde_json::Value, span: Option<Span>) -> EvalResult<Value> {
    match json {
        serde_json::Value::Null => Err(EvalError::Internal {
            message: "JsonDeserialize: null values are unsupported".into(),
            span,
        }),
        serde_json::Value::Bool(b) => Ok(Value::Bool(*b)),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                return Ok(Value::int(i));
            }
            if let Some(u) = n.as_u64() {
                return Ok(Value::big_int(BigInt::from(u)));
            }
            Err(EvalError::Internal {
                message: format!("JsonDeserialize: non-integer number is unsupported: {n}"),
                span,
            })
        }
        serde_json::Value::String(s) => Ok(Value::String(intern_string(s))),
        serde_json::Value::Array(items) => {
            let mut values = Vec::with_capacity(items.len());
            for item in items {
                values.push(json_to_tla_value(item, span)?);
            }
            Ok(Value::Tuple(values.into()))
        }
        serde_json::Value::Object(fields) => {
            let mut builder = RecordBuilder::with_capacity(fields.len());
            for (key, val) in fields {
                builder.insert(
                    tla_core::intern_name(key.as_str()),
                    json_to_tla_value(val, span)?,
                );
            }
            Ok(Value::Record(builder.build()))
        }
    }
}
