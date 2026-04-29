// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State value materialization for TLC-compatible fingerprinting.
//!
//! TLC always materializes lazy values before fingerprinting:
//! - `FcnLambdaValue.fingerPrint()` calls `toFcnRcd()` (enumerate domain, evaluate body)
//! - `SetPredValue.fingerPrint()` calls `toSetEnum()` (enumerate source, filter by predicate)
//! - `OpLambdaValue.fingerPrint()` calls `Assert.fail()` (forbidden in state variables)
//!
//! TLA2 must match this behavior to produce deterministic, content-based fingerprints.
//! Without materialization, lazy values use process-local IDs or structural hashes
//! that cause non-determinism (#1989), state space expansion (#1865), and false-unique
//! states (#1914).
//!
//! Part of #2018: Materialize before fingerprinting.

use crate::error::{EvalError, EvalResult};
use crate::state::{ArrayState, DiffChanges};
use crate::value::IntIntervalFunc;
use crate::var_index::VarIndex;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{walk_expr, ExprVisitor};
use tla_eval::EvalCtx;
use tla_eval::{materialize_lazy_func_to_func, materialize_setpred_to_vec};

/// AST visitor that detects expressions which produce lazy values at runtime.
///
/// Returns `true` (short-circuiting) when `FuncDef`, `SetFilter`, or `Lambda`
/// is found. These are the only AST nodes that produce `LazyFunc`, `SetPred`,
/// or `Closure` values respectively.
struct ContainsLazyProducers;

impl ExprVisitor for ContainsLazyProducers {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::FuncDef(_, _) | Expr::SetFilter(_, _) | Expr::Lambda(_, _) => Some(true),
            _ => None,
        }
    }
}

/// Determine whether a spec's AST contains any expressions that can produce
/// lazy values at runtime (`LazyFunc`, `SetPred`, `Closure`).
///
/// Scans all operator definitions in the module and its extensions for
/// `FuncDef` (`[x \in S |-> e]`), `SetFilter` (`{x \in S : P(x)}`), and
/// `Lambda` expressions. When none are present, materialization can be
/// skipped entirely during BFS because no lazy values will ever appear
/// in state variables.
///
/// Part of #4053: Skip per-successor `has_lazy_state_value` when the spec
/// cannot produce lazy values.
pub(crate) fn spec_may_produce_lazy_values(module: &Module, extended_modules: &[&Module]) -> bool {
    let modules = std::iter::once(module).chain(extended_modules.iter().copied());
    for m in modules {
        for unit in &m.units {
            if let Unit::Operator(op_def) = &unit.node {
                if walk_expr(&mut ContainsLazyProducers, &op_def.body.node) {
                    return true;
                }
            }
        }
    }
    false
}

/// Check whether a value (or any nested child) contains lazy types that
/// need materialization before fingerprinting.
///
/// Lazy types: `LazyFunc`, `SetPred`, `Closure`.
pub(crate) fn has_lazy_state_value(value: &Value) -> bool {
    match value {
        Value::LazyFunc(_) | Value::SetPred(_) | Value::Closure(_) => true,
        Value::Tuple(elems) => elems.iter().any(has_lazy_state_value),
        Value::Seq(seq) => seq.iter().any(has_lazy_state_value),
        Value::Record(rec) => rec.iter().any(|(_, v)| has_lazy_state_value(v)),
        Value::Func(func) => func
            .mapping_iter()
            .any(|(k, v)| has_lazy_state_value(k) || has_lazy_state_value(v)),
        Value::IntFunc(func) => func.values().iter().any(has_lazy_state_value),
        Value::Set(set) => set.iter().any(has_lazy_state_value),
        _ => false,
    }
}

/// Materialize a single value: convert lazy representations to concrete data.
///
/// - `SetPred` → `Value::Set` (via predicate evaluation, matching TLC's `toSetEnum()`)
/// - `LazyFunc` → `Value::Func` (via domain enumeration + body evaluation,
///   matching TLC's `toFcnRcd()`). Returns error for non-enumerable domains.
/// - `Closure` → error (TLC forbids operator lambdas in state variables)
///
/// Recursively materializes nested lazy values within compound types
/// (tuples, sequences, records, functions, sets).
///
/// Part of #2018: Materialize before fingerprinting.
pub(crate) fn materialize_value(ctx: &EvalCtx, value: &Value) -> EvalResult<Value> {
    match value {
        Value::SetPred(spv) => {
            // TLC: SetPredValue.fingerPrint() → toSetEnum()
            let elements = materialize_setpred_to_vec(ctx, spv)?;
            Ok(Value::set(elements))
        }
        Value::LazyFunc(f) => {
            // TLC: FcnLambdaValue.fingerPrint() → toFcnRcd()
            // Enumerate domain, evaluate body for each element, produce concrete Func.
            // Returns error for non-enumerable domains (Nat, Int, Real, String).
            let materialized = materialize_lazy_func_to_func(ctx, f)?;
            // Recursively materialize any lazy values in the function's range
            if has_lazy_state_value(&materialized) {
                materialize_value(ctx, &materialized)
            } else {
                Ok(materialized)
            }
        }
        Value::Closure(_) => Err(EvalError::Internal {
            message: "TLA2 has found a state in which the value of a variable \
                contains an operator (LAMBDA). TLC does not allow operator \
                values in state variables."
                .to_string(),
            span: None,
        }),
        // Compound types with lazy children: recursively materialize
        _ if has_lazy_state_value(value) => materialize_children(ctx, value),
        // No lazy values — return as-is
        _ => Ok(value.clone()),
    }
}

/// Recursively materialize lazy children within compound value types.
///
/// Called by `materialize_value` when a compound value (tuple, seq, record,
/// func, set) contains nested lazy values that need materialization.
fn materialize_children(ctx: &EvalCtx, value: &Value) -> EvalResult<Value> {
    match value {
        Value::Tuple(elems) => {
            let m: Vec<Value> = elems
                .iter()
                .map(|v| materialize_value(ctx, v))
                .collect::<EvalResult<Vec<_>>>()?;
            Ok(Value::Tuple(m.into()))
        }
        Value::Seq(seq) => {
            let m: Vec<Value> = seq
                .iter()
                .map(|v| materialize_value(ctx, v))
                .collect::<EvalResult<Vec<_>>>()?;
            Ok(Value::seq(m))
        }
        Value::Record(rec) => {
            let entries: Vec<_> = rec
                .iter_str()
                .map(|(k, v)| Ok((k, materialize_value(ctx, v)?)))
                .collect::<EvalResult<Vec<_>>>()?;
            Ok(Value::record(entries))
        }
        Value::Func(func) => {
            let mut builder = crate::value::FuncBuilder::with_capacity(func.domain_len());
            for (k, v) in func.mapping_iter() {
                builder.insert(materialize_value(ctx, k)?, materialize_value(ctx, v)?);
            }
            Ok(Value::Func(Arc::new(builder.build())))
        }
        Value::IntFunc(func) => {
            let m: Vec<Value> = func
                .values()
                .iter()
                .map(|v| materialize_value(ctx, v))
                .collect::<EvalResult<Vec<_>>>()?;
            Ok(Value::IntFunc(Arc::new(
                crate::value::IntIntervalFunc::new(
                    IntIntervalFunc::min(func),
                    IntIntervalFunc::max(func),
                    m,
                ),
            )))
        }
        Value::Set(set) => {
            let m: Vec<Value> = set
                .iter()
                .map(|v| materialize_value(ctx, v))
                .collect::<EvalResult<Vec<_>>>()?;
            Ok(Value::set(m))
        }
        _ => Ok(value.clone()),
    }
}

/// Materialize lazy values in all state variables of an ArrayState.
///
/// This is the TLC-compatible normalization pass that should be called before
/// computing fingerprints. It ensures all values are concrete data without
/// process-local IDs, closures, or unevaluated expressions.
///
/// When `spec_may_produce_lazy` is `false`, the spec's AST contains no
/// `FuncDef`, `SetFilter`, or `Lambda` nodes, so lazy values are impossible
/// and the function returns immediately without scanning any values.
///
/// Part of #4053: Skip per-successor `has_lazy_state_value` scan.
///
/// Returns `true` if any values were materialized (state was modified).
pub(crate) fn materialize_array_state(
    ctx: &EvalCtx,
    state: &mut ArrayState,
    spec_may_produce_lazy: bool,
) -> EvalResult<bool> {
    if !spec_may_produce_lazy {
        return Ok(false);
    }
    let mut modified = false;
    let len = state.len();
    for i in 0..len {
        let value = state.get(VarIndex::new(i));
        if has_lazy_state_value(&value) {
            let materialized = materialize_value(ctx, &value)?;
            state.set(VarIndex::new(i), materialized);
            modified = true;
        }
    }
    Ok(modified)
}

/// Materialize lazy values in diff successor changes.
///
/// Call before computing the diff fingerprint to ensure changed values
/// are concrete data. This avoids ID-based fingerprints for lazy values
/// in the diff path.
///
/// When `spec_may_produce_lazy` is `false`, returns immediately.
///
/// Part of #4053: Skip per-successor `has_lazy_state_value` scan.
///
/// Returns `true` if any values were materialized.
pub(crate) fn materialize_diff_changes(
    ctx: &EvalCtx,
    changes: &mut DiffChanges,
    spec_may_produce_lazy: bool,
) -> EvalResult<bool> {
    if !spec_may_produce_lazy {
        return Ok(false);
    }
    let mut modified = false;
    for (_idx, value) in changes.iter_mut() {
        if has_lazy_state_value(value) {
            *value = materialize_value(ctx, value)?;
            modified = true;
        }
    }
    Ok(modified)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_lazy_state_value_concrete() {
        assert!(!has_lazy_state_value(&Value::SmallInt(42)));
        assert!(!has_lazy_state_value(&Value::Bool(true)));
        assert!(!has_lazy_state_value(&Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
        ])));
        assert!(!has_lazy_state_value(&Value::Tuple(
            vec![Value::SmallInt(1), Value::Bool(false)].into()
        )));
    }

    #[test]
    fn test_has_lazy_state_value_nested_setpred() {
        use tla_core::ast::{BoundVar, Expr};
        use tla_core::kani_types::HashMap;
        use tla_core::{FileId, Span, Spanned};

        // Create a minimal SetPred for testing
        let dummy_span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let spv = crate::value::SetPredValue::new(
            Value::set(vec![Value::SmallInt(1)]),
            BoundVar {
                name: Spanned {
                    node: "x".to_string(),
                    span: dummy_span,
                },
                domain: None,
                pattern: None,
            },
            Spanned {
                node: Expr::Bool(true),
                span: dummy_span,
            },
            HashMap::new(),
            None,
            None,
        );
        let setpred = Value::SetPred(Box::new(spv));

        // Direct SetPred
        assert!(has_lazy_state_value(&setpred));

        // SetPred nested in tuple
        let nested = Value::Tuple(vec![Value::SmallInt(1), setpred].into());
        assert!(has_lazy_state_value(&nested));
    }
}
