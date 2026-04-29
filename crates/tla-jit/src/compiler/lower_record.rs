// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Record access compilation for the JIT lowerer.
//!
//! Handles `r.field` where the record may be fully constant or derived from
//! a function application (`f[x].field` with runtime argument `x`).

use crate::error::JitError;
use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use tla_core::ast::{Expr, RecordFieldName};
use tla_core::span::Spanned;

use super::lower::{compile_expr_bound, Bindings};
use super::lower_func::compile_func_apply_lookup;
use super::preflight::{expect_set, preflight_const_value, PreflightValue};
use super::preflight_funcdef::substitute_ident;

/// Compile a record field access where the record is not fully constant.
///
/// The most common runtime case is `f[x].field` where `f` is a compile-time
/// known function mapping integers to records and `x` is a runtime bound
/// variable. This function detects that pattern and compiles it as:
///
/// 1. Evaluate `f` at compile time to get its full mapping.
/// 2. For each domain element, extract the target field's value from the record.
/// 3. Build a lookup table of `(key, field_value)` pairs.
/// 4. Compile the argument `x` to a runtime value.
/// 5. Emit a native lookup loop (or direct index) to find the field value.
pub(crate) fn compile_record_access_runtime(
    builder: &mut FunctionBuilder,
    record: &Spanned<Expr>,
    field_name: &RecordFieldName,
    bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    // Pattern match: is the record a FuncApply? (handles `f[x].field`)
    if let Expr::FuncApply(func, arg) = &record.node {
        // Try the field-projection approach: evaluate the function definition
        // for each domain element, extract the target field, build a flat lookup.
        if let Ok(projected_pairs) =
            preflight_funcdef_field_projection(&func.node, &field_name.name.node)
        {
            let arg_val = compile_expr_bound(builder, arg.as_ref(), bindings)?;
            return compile_func_apply_lookup(builder, &projected_pairs, arg_val);
        }

        // If the function is a compile-time Function (int -> int), the field
        // access on the result is a type error.
        if let Ok(func_val) = preflight_const_value(&func.node) {
            return compile_func_record_field_lookup(builder, &func_val, arg, field_name, bindings);
        }
    }

    // Fallback: try to evaluate the record at compile time as a whole
    // (this handles cases where the record is constant but preflight_const_i64
    // failed because record is not an i64)
    match preflight_const_value(&record.node) {
        Ok(PreflightValue::Record(pairs)) => {
            let target = &field_name.name.node;
            for (k, v) in &pairs {
                if k == target {
                    return Ok(builder.ins().iconst(types::I64, *v));
                }
            }
            Err(JitError::CompileError(format!(
                "record field access: field '{}' not found",
                target
            )))
        }
        Ok(other) => Err(JitError::TypeMismatch {
            expected: "record".to_string(),
            actual: other.ty_name().to_string(),
        }),
        Err(e) => Err(e),
    }
}

/// Compile `f[x].field` where `f` is a compile-time function definition
/// that returns records and `x` is a runtime value.
///
/// This works by evaluating the combined expression `(f[key]).field` at
/// compile time for each domain element `key`, building a flat
/// `(key, field_value)` lookup table. The runtime argument drives a native
/// lookup to retrieve the field value.
///
/// This approach avoids extending `PreflightValue` with nested compound types:
/// instead of storing functions-of-records, we "project" the record field
/// at compile time and store a simple integer-to-integer mapping.
fn compile_func_record_field_lookup(
    builder: &mut FunctionBuilder,
    func_val: &PreflightValue,
    arg: &Spanned<Expr>,
    field_name: &RecordFieldName,
    bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    match func_val {
        PreflightValue::RecordFunction(pairs) => {
            // Extract the target field from each record, building a flat
            // (key, field_value) lookup table for the runtime argument.
            let target = &field_name.name.node;
            let mut flat_pairs = Vec::with_capacity(pairs.len());
            for (key, fields) in pairs {
                let field_val = fields
                    .iter()
                    .find(|(k, _)| k == target)
                    .map(|(_, v)| *v)
                    .ok_or_else(|| {
                        JitError::CompileError(format!(
                            "field '{}' not found in record-function body",
                            target
                        ))
                    })?;
                flat_pairs.push((*key, field_val));
            }
            let arg_val = compile_expr_bound(builder, arg, bindings)?;
            compile_func_apply_lookup(builder, &flat_pairs, arg_val)
        }
        PreflightValue::Function(pairs) => {
            // Function maps integers to integers — not records.
            // The caller wants field access on the result, which is a type error.
            let _ = pairs;
            Err(JitError::TypeMismatch {
                expected: "record (from function application)".to_string(),
                actual: "integer".to_string(),
            })
        }
        _ => Err(JitError::TypeMismatch {
            expected: "function or record-function".to_string(),
            actual: func_val.ty_name().to_string(),
        }),
    }
}

/// Evaluate a `FuncDef` body for each domain element, apply a record field
/// access, and return a `(key, field_value)` lookup table.
///
/// For a function `[x \in S |-> [a |-> expr1, b |-> expr2]]` and field `a`,
/// this substitutes each domain element for `x`, evaluates the resulting
/// record, extracts field `a`, and returns `(x_val, a_val)` pairs.
pub(crate) fn preflight_funcdef_field_projection(
    func_expr: &Expr,
    field_name: &str,
) -> Result<Vec<(i64, i64)>, JitError> {
    use tla_core::ast::BoundVar;

    match func_expr {
        Expr::FuncDef(bounds, body) => {
            if bounds.len() != 1 {
                return Err(JitError::UnsupportedExpr(
                    "multi-variable function not supported for field projection in JIT".to_string(),
                ));
            }

            let BoundVar {
                name,
                domain,
                pattern,
            } = &bounds[0];

            if pattern.is_some() {
                return Err(JitError::UnsupportedExpr(
                    "pattern in function definition not supported for field projection in JIT"
                        .to_string(),
                ));
            }

            let domain_expr = domain.as_ref().ok_or_else(|| {
                JitError::UnsupportedExpr(
                    "function without domain not supported for field projection in JIT".to_string(),
                )
            })?;

            let domain_val = preflight_const_value(&domain_expr.node)?;
            let set = expect_set(domain_val)?;

            if set.len() > 1024 {
                return Err(JitError::CompileError(
                    "function domain too large for JIT field projection (>1024 elements)"
                        .to_string(),
                ));
            }

            let var_name = &name.node;
            let mut pairs = Vec::with_capacity(set.len());

            for &key in &set {
                // Substitute domain element for bound variable in body
                let substituted = substitute_ident(&body.node, var_name, key);
                // Evaluate the substituted body — should produce a Record
                let val = preflight_const_value(&substituted)?;
                match val {
                    PreflightValue::Record(fields) => {
                        let field_val = fields
                            .iter()
                            .find(|(k, _)| k == field_name)
                            .map(|(_, v)| *v)
                            .ok_or_else(|| {
                                JitError::CompileError(format!(
                                    "field '{}' not found in function body record",
                                    field_name
                                ))
                            })?;
                        pairs.push((key, field_val));
                    }
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "record".to_string(),
                            actual: other.ty_name().to_string(),
                        });
                    }
                }
            }

            Ok(pairs)
        }
        _ => Err(JitError::UnsupportedExpr(
            "field projection requires a FuncDef expression".to_string(),
        )),
    }
}
