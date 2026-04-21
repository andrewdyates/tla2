// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scalar setup helpers for model checker preparation.
//!
//! These leaf operations are called through the stable `crate::checker_ops::*`
//! surface by both sequential and parallel model checkers.

#[cfg(debug_assertions)]
use crate::check::debug::tla2_debug;
use crate::check::{format_span_location, CheckError, INLINE_NEXT_NAME};
use crate::config::Config;
use crate::enumerate::{expand_operators, expand_operators_with_primes};
use crate::eval::EvalCtx;
use crate::{ConfigCheckError, EvalCheckError, RuntimeCheckError};
use tla_core::ast::{Expr, OperatorDef};
use tla_core::{Spanned, SyntaxNode, VarRegistry};

/// Validate the VIEW operator: must exist and have zero parameters.
///
/// Returns `Some(name)` if the VIEW operator is configured and valid,
/// `None` if not configured or the operator is missing/invalid.
///
/// Both sequential (`run_prepare.rs:193-224`) and parallel (`prepare.rs:166-194`)
/// checkers previously duplicated this exact logic. Extracting it prevents
/// silent divergence if validation rules change.
pub(crate) fn validate_view_operator(ctx: &EvalCtx, config: &Config) -> Option<String> {
    let view_name = config.view.as_ref()?;

    match ctx.get_op(view_name) {
        Some(def) => {
            if !def.params.is_empty() {
                eprintln!(
                    "Warning: VIEW operator '{}' has {} parameters, expected 0. \
                     Using full state fingerprints",
                    view_name,
                    def.params.len()
                );
                None
            } else {
                debug_eprintln!(
                    tla2_debug(),
                    "VIEW enabled: using '{}' for fingerprinting",
                    view_name
                );
                Some(view_name.clone())
            }
        }
        None => {
            eprintln!(
                "Warning: VIEW operator '{}' not found, using full state fingerprints",
                view_name
            );
            None
        }
    }
}

/// Expand operator references in an operator definition body.
///
/// Returns a new `OperatorDef` with inlined operator definitions in the body.
/// This eliminates expensive operator lookups and expression tree cloning during
/// state enumeration by inlining all operator definitions once at startup.
///
/// Both sequential (`run_prepare.rs:379-391`) and parallel (`prepare.rs:252-264`)
/// checkers previously duplicated this exact OperatorDef reconstruction.
pub(crate) fn expand_operator_body(ctx: &EvalCtx, def: &OperatorDef) -> OperatorDef {
    let expanded_body = expand_operators(ctx, &def.body);
    OperatorDef {
        name: def.name.clone(),
        params: def.params.clone(),
        body: expanded_body,
        local: def.local,
        contains_prime: def.contains_prime,
        guards_depend_on_prime: def.guards_depend_on_prime,
        has_primed_param: def.has_primed_param,
        is_recursive: def.is_recursive,
        self_call_count: def.self_call_count,
    }
}

/// Expand operator body including operators that contain primed variables.
///
/// Used by POR dependency extraction which needs to see the full action body
/// (primed assignments, UNCHANGED) to compute read/write sets. The default
/// `expand_operator_body` skips primed operators to protect guard compilation
/// and constraint evaluation from seeing primed sub-expressions.
///
/// Part of #3354 Slice 4: replaces CompiledAction-tree dependency walk.
pub(crate) fn expand_operator_body_with_primes(ctx: &EvalCtx, def: &OperatorDef) -> OperatorDef {
    let expanded_body = expand_operators_with_primes(ctx, &def.body);
    OperatorDef {
        name: def.name.clone(),
        params: def.params.clone(),
        body: expanded_body,
        local: def.local,
        contains_prime: def.contains_prime,
        guards_depend_on_prime: def.guards_depend_on_prime,
        has_primed_param: def.has_primed_param,
        is_recursive: def.is_recursive,
        self_call_count: def.self_call_count,
    }
}

/// Lower an inline NEXT CST node to an operator definition.
///
/// When the SPECIFICATION formula contains an inline NEXT expression like
/// `Init /\ [][\E n \in Node: Next(n)]_vars`, the resolved spec's `next_node`
/// contains the CST node. This function lowers it to an AST expression, wraps
/// it in a synthetic `OperatorDef` named `INLINE_NEXT_NAME`, and resolves state
/// variables in the body.
///
/// Returns `None` if `next_node` is `None` (no inline NEXT expression).
/// Returns `Some(Ok(op_def))` on success.
/// Returns `Some(Err(CheckError))` if CST lowering fails.
///
/// Both sequential (`run_prepare.rs:33-66`) and parallel (`checker.rs:347-402`)
/// checkers previously duplicated this lowering+construction logic. Each caller
/// then registers the returned `OperatorDef` according to its own storage model:
/// sequential stores in both `module.op_defs` and `ctx`, parallel stores in
/// `self.op_defs` and recomputes `uses_trace`.
pub(crate) fn lower_inline_next(
    next_node: Option<&SyntaxNode>,
    var_registry: &VarRegistry,
) -> Option<Result<OperatorDef, CheckError>> {
    let node = next_node?;

    let expr = match tla_core::lower_single_expr(tla_core::FileId(0), node) {
        Some(e) => e,
        None => {
            return Some(Err(ConfigCheckError::Specification(format!(
                "Failed to lower inline NEXT expression: {}",
                node.text()
            ))
            .into()));
        }
    };

    let mut op_def = OperatorDef {
        name: Spanned::dummy(INLINE_NEXT_NAME.to_string()),
        params: vec![],
        body: Spanned::dummy(expr),
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    tla_eval::state_var::resolve_state_vars_in_op_def(&mut op_def, var_registry);

    Some(Ok(op_def))
}

/// Check ASSUME statements, returning the first failing error.
///
/// Evaluates each ASSUME expression in order. Returns `None` if all pass,
/// `Some(CheckError)` if any fail (false, non-boolean, or eval error).
/// Callers wrap the error in `CheckResult` with their own stats.
///
/// Both sequential (`run_checks.rs:18-46`) and parallel (`prepare.rs:128-153`)
/// checkers previously duplicated this exact match-arm pattern. Extracting it
/// prevents divergence in error classification (e.g., non-boolean handling)
/// and ensures both paths produce identical `CheckError` variants.
pub(crate) fn check_assumes(
    ctx: &EvalCtx,
    assumes: &[(String, Spanned<Expr>)],
) -> Option<CheckError> {
    use crate::eval::eval_entry;
    use crate::value::Value;

    for (module_name, assume_expr) in assumes {
        match eval_entry(ctx, assume_expr) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) | Ok(_) => {
                let location = format_span_location(&assume_expr.span, module_name);
                return Some(RuntimeCheckError::AssumeFalse { location }.into());
            }
            Err(e) => {
                return Some(EvalCheckError::Eval(e).into());
            }
        }
    }
    None
}
