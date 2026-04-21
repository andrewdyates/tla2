// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::live_expr::ExprLevel;
use super::super::core::AstToLive;
use crate::eval::{apply_substitutions, compose_substitutions, EvalCtx};
use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::Spanned;

/// Resolve INSTANCE info from a named identifier in the current context.
///
/// NOTE: This is intentionally separate from `temporal_fairness::resolve_instance_info`
/// because that version has an extra `!def.params.is_empty()` guard that would change
/// level classification behavior for parameterized operator definitions.
fn resolve_instance_info(
    ctx: &EvalCtx,
    instance_name: &str,
) -> Option<(String, Vec<Substitution>)> {
    if let Some(info) = ctx.get_instance(instance_name) {
        let effective_subs =
            ctx.compute_effective_instance_substitutions(&info.module_name, &info.substitutions);
        return Some((
            info.module_name.clone(),
            compose_substitutions(&effective_subs, ctx.instance_substitutions()),
        ));
    }
    if let Some(def) = ctx.get_op(instance_name) {
        if let Expr::InstanceExpr(module_name, substitutions) = &def.body.node {
            let effective_subs =
                ctx.compute_effective_instance_substitutions(module_name, substitutions);
            return Some((
                module_name.clone(),
                compose_substitutions(&effective_subs, ctx.instance_substitutions()),
            ));
        }
    }
    None
}

fn resolve_module_target_ctx(ctx: &EvalCtx, target: &ModuleTarget) -> Option<EvalCtx> {
    match target {
        ModuleTarget::Named(name) => {
            let (module_name, instance_subs) = resolve_instance_info(ctx, name)?;
            // Part of #1433: empty default is correct — modules without registered
            // instance operators simply have no local ops in scope. Not error-swallowing.
            let instance_ops = ctx
                .instance_ops()
                .get(&module_name)
                .cloned()
                .unwrap_or_default();
            Some(ctx.with_instance_scope(instance_ops, instance_subs))
        }
        ModuleTarget::Parameterized(name, params) => {
            let def = ctx.get_op(name)?;
            let Expr::InstanceExpr(module_name, instance_subs) = &def.body.node else {
                return None;
            };
            if def.params.len() != params.len() {
                return None;
            }

            // Bind instance operator parameters into the WITH substitutions.
            let param_subs: Vec<Substitution> = def
                .params
                .iter()
                .zip(params.iter())
                .map(|(p, arg)| Substitution {
                    from: p.name.clone(),
                    to: arg.clone(),
                })
                .collect();

            let instantiated_subs: Vec<Substitution> = instance_subs
                .iter()
                .map(|s| Substitution {
                    from: s.from.clone(),
                    to: apply_substitutions(&s.to, &param_subs),
                })
                .collect();

            let effective_subs = compose_substitutions(
                &ctx.compute_effective_instance_substitutions(module_name, &instantiated_subs),
                ctx.instance_substitutions(),
            );
            // Part of #1433: empty default is correct — modules without registered
            // instance operators simply have no local ops in scope. Not error-swallowing.
            let instance_ops = ctx
                .instance_ops()
                .get(module_name)
                .cloned()
                .unwrap_or_default();
            Some(ctx.with_instance_scope(instance_ops, effective_subs))
        }
        ModuleTarget::Chained(base_expr) => resolve_chained_target_ctx(ctx, base_expr),
    }
}

fn resolve_chained_target_ctx(ctx: &EvalCtx, base_expr: &Spanned<Expr>) -> Option<EvalCtx> {
    let Expr::ModuleRef(base_target, inst_name, inst_args) = &base_expr.node else {
        return None;
    };
    if !inst_args.is_empty() {
        return None;
    }

    let base_ctx = resolve_module_target_ctx(ctx, base_target)?;
    let inst_def = base_ctx.get_op(inst_name)?;
    let Expr::InstanceExpr(module_name, inst_subs) = &inst_def.body.node else {
        return None;
    };

    let effective_subs = compose_substitutions(
        &base_ctx.compute_effective_instance_substitutions(module_name, inst_subs),
        base_ctx.instance_substitutions(),
    );
    // Part of #1433: empty default is correct — modules without registered
    // instance operators simply have no local ops in scope. Not error-swallowing.
    let instance_ops = ctx
        .instance_ops()
        .get(module_name)
        .cloned()
        .unwrap_or_default();

    Some(base_ctx.with_instance_scope(instance_ops, effective_subs))
}

impl AstToLive {
    /// Classify an `Expr::ModuleRef` — resolve the target INSTANCE context and
    /// look up the operator definition to determine its level.
    ///
    /// Handles:
    /// - target/argument pre-level aggregation
    /// - recursion guard for `format!("{target}!{op_name}")`
    /// - lookup of the resolved operator body
    /// - #2835: conservative temporal fallback when resolution fails
    pub(super) fn level_module_ref_with_ctx(
        &self,
        ctx: &EvalCtx,
        target: &ModuleTarget,
        op_name: &str,
        args: &[Spanned<Expr>],
        visited: &mut std::collections::HashSet<String>,
        bound_vars: &mut std::collections::HashSet<String>,
    ) -> ExprLevel {
        // Start with target sub-expression levels
        let mut level = match target {
            ModuleTarget::Parameterized(_, params) => {
                let mut l = ExprLevel::Constant;
                for p in params {
                    l = l.max(self.get_level_with_ctx_inner(ctx, &p.node, visited, bound_vars));
                }
                l
            }
            ModuleTarget::Chained(base) => {
                self.get_level_with_ctx_inner(ctx, &base.node, visited, bound_vars)
            }
            ModuleTarget::Named(_) => ExprLevel::Constant,
        };
        // Include args level
        for arg in args {
            level = level.max(self.get_level_with_ctx_inner(ctx, &arg.node, visited, bound_vars));
        }

        // Prevent infinite recursion
        let combined_name = format!("{}!{}", target, op_name);
        if visited.contains(&combined_name) {
            return level;
        }

        if let Some(instance_ctx) = resolve_module_target_ctx(ctx, target) {
            if let Some(op_def) = instance_ctx.get_op(op_name) {
                let substituted_body = match instance_ctx.instance_substitutions() {
                    Some(subs) => apply_substitutions(&op_def.body, subs),
                    None => op_def.body.clone(),
                };

                visited.insert(combined_name.clone());
                let op_level = self.get_level_with_ctx_inner(
                    &instance_ctx,
                    &substituted_body.node,
                    visited,
                    bound_vars,
                );
                visited.remove(&combined_name);
                level = level.max(op_level);
            } else {
                // Part of #2835: operator not found in resolved instance — conservatively
                // treat as temporal to avoid incorrect safety promotion.
                level = level.max(ExprLevel::Temporal);
            }
        } else {
            // Part of #2835: instance cannot be resolved (e.g., nested INSTANCE
            // visible only within the declaring module's scope). Conservatively
            // treat as temporal to prevent incorrect promotion to BFS-inline
            // invariant/init checking, which would fail at runtime because the
            // instance is not in the top-level evaluation context.
            level = level.max(ExprLevel::Temporal);
        }

        level
    }
}
