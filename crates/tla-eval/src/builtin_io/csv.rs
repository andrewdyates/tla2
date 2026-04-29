// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;
use std::sync::Arc;

use super::super::{
    check_arity, eval as eval_expr, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use super::io_utils::format_community_modules_template;
use super::resolve_input_path;
use crate::value::intern_string;

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // CSVWrite(template, tuple, file) - format template with tuple values and append to file.
        // CommunityModules routes this through Java's String.format.
        // Part of #3311: Real implementation replacing #3284 error stub.
        "CSVWrite" => {
            check_arity(name, args, 3, span)?;
            let template_val = eval_expr(ctx, &args[0])?;
            let template = template_val.as_string().ok_or_else(|| {
                EvalError::type_error("String", &template_val, Some(args[0].span))
            })?;
            let tuple_val = eval_expr(ctx, &args[1])?;
            let file_val = eval_expr(ctx, &args[2])?;
            let file_path = file_val
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &file_val, Some(args[2].span)))?;
            let formatted = format_csv_write_line(template, &tuple_val, span)?;

            // Resolve path relative to spec directory and append.
            let resolved = resolve_input_path(ctx, file_path);
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&resolved)
                .map_err(|e| EvalError::Internal {
                    message: format!("CSVWrite: failed to open '{}': {}", resolved.display(), e),
                    span,
                })?;
            writeln!(file, "{formatted}").map_err(|e| EvalError::Internal {
                message: format!(
                    "CSVWrite: failed to write to '{}': {}",
                    resolved.display(),
                    e
                ),
                span,
            })?;

            Ok(Some(Value::Bool(true)))
        }

        // CSVRead(path, header, delim) - read CSV file into sequence of records.
        // Stub: Returns empty sequence (no actual file reading during model checking).
        "CSVRead" => {
            check_arity(name, args, 3, span)?;
            let _path = eval_expr(ctx, &args[0])?;
            let _header = eval_expr(ctx, &args[1])?;
            let _delim = eval_expr(ctx, &args[2])?;
            Ok(Some(Value::Seq(Arc::new(Vec::new().into()))))
        }

        // CSVRecords(path) - read CSV file with default settings.
        // TLC returns integer 0 when the CSV file does not exist (common in
        // simulation specs that check for prior run data). Matching that
        // behaviour lets SimTokenRing and similar specs proceed correctly.
        "CSVRecords" => {
            check_arity(name, args, 1, span)?;
            let path_val = eval_expr(ctx, &args[0])?;
            let path_str = path_val
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &path_val, Some(args[0].span)))?;
            let resolved = resolve_input_path(ctx, path_str);
            if resolved.is_file() {
                let contents =
                    std::fs::read_to_string(&resolved).map_err(|e| EvalError::Internal {
                        message: format!(
                            "CSVRecords: failed to read '{}': {}",
                            resolved.display(),
                            e
                        ),
                        span,
                    })?;
                let mut records = Vec::new();
                let mut lines = contents.lines();
                let header: Vec<&str> = match lines.next() {
                    Some(h) if !h.trim().is_empty() => h.split(',').map(|s| s.trim()).collect(),
                    _ => return Ok(Some(Value::Tuple(Vec::new().into()))),
                };
                for line in lines {
                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }
                    let fields: Vec<&str> = line.split(',').map(|s| s.trim()).collect();
                    let record = Value::record(
                        header
                            .iter()
                            .zip(fields.iter())
                            .map(|(k, v)| (k.to_string(), Value::String(intern_string(v)))),
                    );
                    records.push(record);
                }
                Ok(Some(Value::Tuple(records.into())))
            } else {
                // File does not exist — TLC returns integer 0.
                Ok(Some(Value::int(0)))
            }
        }

        _ => Ok(None),
    }
}

pub(super) fn format_csv_write_line(
    template: &str,
    tuple_val: &Value,
    span: Option<Span>,
) -> EvalResult<String> {
    let tuple = sequence_like_elements(tuple_val, span)?;
    let fields = tuple.iter().map(ToString::to_string).collect::<Vec<_>>();
    format_community_modules_template(template, &fields, "CSVWrite", span)
}

fn sequence_like_elements<'a>(
    value: &'a Value,
    span: Option<Span>,
) -> EvalResult<Cow<'a, [Value]>> {
    value
        .as_seq_or_tuple_elements()
        .ok_or_else(|| EvalError::type_error("Sequence", value, span))
}
