// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE operator inlining with substitutions for unified successor
//! enumeration.
//!
//! Handles `Expr::ModuleRef` by looking up instance metadata, retrieving the
//! operator from the instanced module, applying WITH and parameter
//! substitutions, setting up the instance-local operator scope, and recursing
//! into the inlined body.
//!
//! Extracted from unified.rs as part of #2360.

use std::sync::Arc;

use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{apply_substitutions, EvalCtx};
use crate::OpEnv;

use super::build_diff::build_successor_diffs_from_array_into;
#[cfg(debug_assertions)]
use super::debug_enum;
use super::symbolic_assignments::{
    evaluate_symbolic_assignments, extract_symbolic_assignments_with_registry,
};
use super::unified_dispatch::enumerate_unified_inner;
use super::unified_types::{EnumParams, RecState};

/// Handle `Expr::ModuleRef` — inline an INSTANCE operator with its substitutions.
///
/// Looks up instance metadata, retrieves the operator from the instanced module,
/// applies WITH and parameter substitutions, sets up the instance-local operator
/// scope, and recurses into the inlined body.
pub(super) fn enumerate_module_ref(
    ctx: &mut EvalCtx,
    expr: &Spanned<Expr>,
    instance_name: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    p: &EnumParams<'_>,
    s: &mut RecState<'_>,
) -> Result<(), EvalError> {
    // Look up instance metadata
    let instance_info = match ctx.get_instance(instance_name.name()) {
        Some(info) => info.clone(),
        None => {
            // Instance not found — fall back to symbolic assignment extraction.
            // Part of #1433: warn about the fallback. conjunct_module_ref returns
            // Err(UndefinedOp) for this case; top-level falls back for compatibility
            // with specs where module references resolve through symbolic extraction.
            debug_eprintln!(
                debug_enum(),
                "enumerate_module_ref: instance '{}' not found, falling back to symbolic extraction",
                instance_name
            );
            let mut symbolic = Vec::new();
            extract_symbolic_assignments_with_registry(
                ctx,
                expr,
                p.vars,
                &mut symbolic,
                p.registry,
                p.tir_leaf,
            )?;
            if symbolic.is_empty() {
                // Part of #1433: warn when fallback also produces nothing.
                // This means neither instance lookup nor symbolic extraction
                // could handle the expression — action silently disabled.
                eprintln!(
                    "WARNING: instance '{}' not found and symbolic extraction produced no assignments \
                     (action silently disabled at {:?})",
                    instance_name, expr.span
                );
                return Ok(());
            }
            let assignments = evaluate_symbolic_assignments(ctx, &symbolic, p.tir_leaf)?;
            build_successor_diffs_from_array_into(
                ctx,
                p.base_with_fp,
                p.vars,
                &assignments,
                p.registry,
                s.results,
            );
            return Ok(());
        }
    };

    // Get the operator definition from the instanced module
    let op_def = match ctx.get_instance_op_arc(&instance_info.module_name, op_name) {
        Some(def) => def,
        None => {
            return Err(EvalError::UndefinedOp {
                name: format!("{}!{}", instance_name, op_name),
                span: Some(expr.span),
            });
        }
    };
    let resolved_def_ptr = Arc::as_ptr(op_def) as usize;

    // Apply INSTANCE ... WITH substitutions and parameter substitutions.
    // Part of #3063: cache substituted body per call site.
    let inlined = super::subst_cache::cached_substitute(ctx, expr, resolved_def_ptr, || {
        let mut body = apply_substitutions(&op_def.body, &instance_info.substitutions);
        if !op_def.params.is_empty() && op_def.params.len() == args.len() {
            let param_subs: Vec<Substitution> = op_def
                .params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| Substitution {
                    from: param.name.clone(),
                    to: arg.clone(),
                })
                .collect();
            body = apply_substitutions(&body, &param_subs);
        }
        body
    });

    // Set up instance-local operator scope
    // Part of #1433: empty default is correct — modules without registered
    // instance operators simply have no local ops in scope. Not error-swallowing.
    let instance_local_ops: OpEnv = ctx
        .instance_ops()
        .get(&instance_info.module_name)
        .cloned()
        .unwrap_or_default();

    let merged_ops = if let Some(outer_ops) = ctx.local_ops().as_deref() {
        let mut merged = instance_local_ops.clone();
        for (name, def) in outer_ops.iter() {
            merged.entry(name.clone()).or_insert_with(|| def.clone());
        }
        merged
    } else {
        instance_local_ops
    };

    let saved_local_ops = ctx.local_ops().clone();
    *ctx.local_ops_mut() = Some(Arc::new(merged_ops));

    let result = enumerate_unified_inner(ctx, &inlined, p, s);

    *ctx.local_ops_mut() = saved_local_ops;
    result
}
