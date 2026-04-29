// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Built-in Apalache Variants module operators.
//!
//! Implements tagged union (variant) values as records with `tag` and `value`
//! fields, following Apalache's Variants module specification.
//!
//! - `Variant(tag, value)` creates `[tag |-> tag, value |-> value]`
//! - `VariantTag(v)` extracts the tag string from a variant record
//! - `VariantGetUnsafe(tag, v)` extracts value if tag matches, errors otherwise
//! - `VariantGetOrElse(tag, v, default)` extracts value if tag matches, else default
//! - `VariantFilter(tag, S)` filters a set of variants by tag
//!
//! Reference: <https://apalache-mc.org/docs/lang/apalache-operators.html#variants>

use super::{
    check_arity, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use crate::value::intern_string;

pub(super) fn eval_builtin_variants(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // Variant(tag, value) - Create a tagged union value.
        // Represented as a record [tag |-> tag, value |-> value].
        "Variant" => {
            check_arity(name, args, 2, span)?;
            let tag = eval(ctx, &args[0])?;
            let tag_str = tag
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &tag, Some(args[0].span)))?;
            let value = eval(ctx, &args[1])?;

            let rec: tla_value::RecordValue = vec![
                ("tag".to_string(), Value::String(intern_string(tag_str))),
                ("value".to_string(), value),
            ]
            .into();
            Ok(Some(Value::Record(rec)))
        }

        // VariantTag(v) - Extract the tag string from a variant record.
        "VariantTag" => {
            check_arity(name, args, 1, span)?;
            let v = eval(ctx, &args[0])?;
            let rec = v.as_record().ok_or_else(|| {
                EvalError::type_error("Variant (record with tag field)", &v, Some(args[0].span))
            })?;
            let tag = rec.get("tag").ok_or_else(|| EvalError::Internal {
                message: "VariantTag: record has no 'tag' field".into(),
                span,
            })?;
            Ok(Some(tag.clone()))
        }

        // VariantGetUnsafe(tag, v) - Extract value from variant if tag matches.
        // Errors if the variant's tag does not match the expected tag.
        "VariantGetUnsafe" => {
            check_arity(name, args, 2, span)?;
            let expected_tag = eval(ctx, &args[0])?;
            let expected_str = expected_tag.as_string().ok_or_else(|| {
                EvalError::type_error("String", &expected_tag, Some(args[0].span))
            })?;
            let v = eval(ctx, &args[1])?;
            let rec = v.as_record().ok_or_else(|| {
                EvalError::type_error("Variant (record with tag field)", &v, Some(args[1].span))
            })?;
            let actual_tag = rec.get("tag").ok_or_else(|| EvalError::Internal {
                message: "VariantGetUnsafe: record has no 'tag' field".into(),
                span,
            })?;
            let actual_str = actual_tag
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", actual_tag, span))?;
            if actual_str != expected_str {
                return Err(EvalError::Internal {
                    message: format!(
                        "VariantGetUnsafe: expected tag \"{}\", got \"{}\"",
                        expected_str, actual_str
                    ),
                    span,
                });
            }
            let value = rec.get("value").ok_or_else(|| EvalError::Internal {
                message: "VariantGetUnsafe: record has no 'value' field".into(),
                span,
            })?;
            Ok(Some(value.clone()))
        }

        // VariantGetOrElse(tag, v, default) - Extract value if tag matches, else default.
        "VariantGetOrElse" => {
            check_arity(name, args, 3, span)?;
            let expected_tag = eval(ctx, &args[0])?;
            let expected_str = expected_tag.as_string().ok_or_else(|| {
                EvalError::type_error("String", &expected_tag, Some(args[0].span))
            })?;
            let v = eval(ctx, &args[1])?;
            let default = eval(ctx, &args[2])?;
            let rec = match v.as_record() {
                Some(r) => r,
                None => return Ok(Some(default)),
            };
            let actual_tag = match rec.get("tag") {
                Some(t) => t,
                None => return Ok(Some(default)),
            };
            let actual_str = match actual_tag.as_string() {
                Some(s) => s,
                None => return Ok(Some(default)),
            };
            if actual_str != expected_str {
                return Ok(Some(default));
            }
            match rec.get("value") {
                Some(val) => Ok(Some(val.clone())),
                None => Ok(Some(default)),
            }
        }

        // VariantFilter(tag, S) - Filter a set of variants by tag.
        // Returns the set of values whose tag matches.
        "VariantFilter" => {
            check_arity(name, args, 2, span)?;
            let expected_tag = eval(ctx, &args[0])?;
            let expected_str = expected_tag.as_string().ok_or_else(|| {
                EvalError::type_error("String", &expected_tag, Some(args[0].span))
            })?;
            let sv = eval(ctx, &args[1])?;
            let mut result = Vec::new();
            for elem in eval_iter_set(ctx, &sv, Some(args[1].span))? {
                if let Some(rec) = elem.as_record() {
                    if let Some(tag) = rec.get("tag") {
                        if let Some(tag_str) = tag.as_string() {
                            if tag_str == expected_str {
                                result.push(elem);
                            }
                        }
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
