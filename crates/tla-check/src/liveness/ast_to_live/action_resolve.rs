// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::live_expr::ExprLevel;
use super::core::AstToLive;
#[cfg(debug_assertions)]
use super::core::{debug_instance_resolve, debug_let, debug_resolve, debug_subst};
use super::reify::{value_is_reifiable_for_substitution, value_to_expr};
use crate::error_policy::{eval_speculative, FallbackClass};
use crate::eval::{compose_substitutions, EvalCtx};
use tla_core::ast::{Expr, ModuleTarget};
use tla_core::Spanned;

/// Debug: trace instance resolve context for an operator.
#[cfg(debug_assertions)]
fn debug_log_instance_resolve(name: &str, is_from_local_ops: bool, ctx: &EvalCtx) {
    debug_block!(debug_instance_resolve(), {
        eprintln!(
            "[DEBUG INSTANCE RESOLVE] op='{}' is_from_local_ops={} has_subs={}",
            name,
            is_from_local_ops,
            ctx.instance_substitutions().is_some()
        );
        if let Some(subs) = ctx.instance_substitutions() {
            for s in subs {
                eprintln!("[DEBUG INSTANCE RESOLVE]   sub: {} <- ...", s.from.node);
            }
        }
    });
}

/// Debug: trace zero-arg operator inlining (extracted to reduce nesting depth).
#[cfg(debug_assertions)]
fn debug_log_ident_inline(name: &str, body: &Expr) {
    debug_block!(debug_let(), {
        eprintln!(
            "[DEBUG IDENT] Inlining zero-arg op '{}', body is {:?}",
            name,
            std::mem::discriminant(body)
        );
        if let Expr::Let(defs, _) = body {
            for d in defs {
                eprintln!(
                    "[DEBUG IDENT]   LET def: {} (params={})",
                    d.name.node,
                    d.params.len()
                );
            }
        }
    });
}

impl AstToLive {
    pub(super) fn reify_current_target_leaf_expr(
        &self,
        ctx: &EvalCtx,
        expr: &Spanned<Expr>,
    ) -> Spanned<Expr> {
        let qualified = self.qualify_predicate_expr(ctx, expr);
        let mut visited = std::collections::HashSet::new();
        let result = self.resolve_action_expr_node(ctx, &qualified.node, &mut visited);
        Spanned {
            span: qualified.span,
            node: result,
        }
    }

    /// Resolve an action expression by inlining operator references.
    ///
    /// When an action expression is stored in LiveExpr (e.g., for WF/SF fairness),
    /// operator references must be resolved/inlined so the expression can be
    /// evaluated later without requiring the original context to have those
    /// operators bound. This is especially important for INSTANCE'd modules where
    /// the referenced operators are only available through the instance context.
    pub fn resolve_action_expr(&self, ctx: &EvalCtx, expr: &Spanned<Expr>) -> Spanned<Expr> {
        if self.current_target().is_some() {
            return self.reify_current_target_leaf_expr(ctx, expr);
        }
        let mut visited = std::collections::HashSet::new();
        let resolved_node = self.resolve_action_expr_node(ctx, &expr.node, &mut visited);
        Spanned {
            node: resolved_node,
            span: expr.span,
        }
    }

    /// Recursively resolve operator references in an expression node.
    ///
    /// This is used to inline operator definitions so that the resulting expression
    /// can be evaluated later without the original context's operator bindings.
    pub(super) fn resolve_action_expr_node(
        &self,
        ctx: &EvalCtx,
        expr: &Expr,
        visited: &mut std::collections::HashSet<String>,
    ) -> Expr {
        // Debug: trace entry into resolve_action_expr_node
        debug_block!(debug_resolve(), {
            if let Expr::Let(defs, _) = expr {
                eprintln!(
                    "[DEBUG RESOLVE] resolve_action_expr_node entered with LET ({} defs)",
                    defs.len()
                );
                for d in defs {
                    eprintln!(
                        "[DEBUG RESOLVE]   def: {} (params={})",
                        d.name.node,
                        d.params.len()
                    );
                }
            }
        });
        match expr {
            // Identifier - try to resolve operator definition and inline it
            Expr::Ident(name, _) => {
                // Prevent infinite recursion for cyclic definitions
                if visited.contains(name) {
                    return expr.clone();
                }
                // Part of #575: For config-overridden constants, try to evaluate and inline
                // the value. This is essential for liveness checking where the action
                // expression is evaluated in a context that may not have the constant bound.
                // E.g., `Prisoner = {"Alice", "Bob", "Eve"}` in config - we need to inline
                // the set value so that guards like `p \in NormalPrisoner` can be evaluated.
                if ctx.is_config_constant(name) {
                    // Try to evaluate the constant and inline its value.
                    // Part of #1433: Use eval_speculative with ConstantResolution to
                    // classify expected failures (undefined var/op, primed var) vs unexpected.
                    let ident_expr = Spanned::dummy(expr.clone());
                    match eval_speculative(ctx, &ident_expr, &[FallbackClass::ConstantResolution]) {
                        Ok(Some(value)) => {
                            // NOTE: `value_to_expr` is intentionally partial; do not invent a
                            // fallback literal (e.g. Expr::String(format!("{:?}", value))).
                            if value_is_reifiable_for_substitution(&value) {
                                if let Ok(reified) = value_to_expr(&value) {
                                    return reified;
                                }
                            }
                        }
                        Ok(None) => {
                            // Expected: constant depends on state, keep as Ident
                        }
                        Err(e) => {
                            // Part of #2806: Unexpected eval error — not ConstantResolution class.
                            // Log so unexpected errors (DivisionByZero, TypeError, etc.) are
                            // visible rather than silently swallowed.
                            eprintln!(
                                "Warning: unexpected eval error during config constant '{name}' resolution (kept as Ident): {e}"
                            );
                        }
                    }
                    // Evaluation failed or not reifiable - keep as Ident
                    return expr.clone();
                }
                let is_from_local_ops = ctx
                    .local_ops()
                    .as_ref()
                    .is_some_and(|local| local.contains_key(name));
                let active_instance_sub = if is_from_local_ops {
                    None
                } else {
                    ctx.active_instance_substitution(name)
                };

                if active_instance_sub.is_none() {
                    if let Some(op_def) = ctx.get_op(name) {
                        if op_def.params.is_empty() {
                            // Debug: trace zero-arg operator inlining
                            #[cfg(debug_assertions)]
                            debug_log_ident_inline(name, &op_def.body.node);

                            // IMPORTANT: Whether to apply instance substitutions depends on WHERE
                            // the operator is defined:
                            //
                            // 1. Operators from the OUTER module (found in shared.ops):
                            //    DO NOT apply substitutions. For example:
                            //      pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"
                            //      R == INSTANCE Reachable WITH pc <- pcBar
                            //    The "pc" inside pcBar refers to ParReach's pc variable, NOT
                            //    Reachable's pc (which would be substituted with pcBar).
                            //
                            // 2. Operators from the INSTANCED module (found in local_ops):
                            //    MUST apply substitutions. For example:
                            //      -- stages.tla --
                            //      vars == << tee, primer, dna, template, hybrid, stage, cycle >>
                            //      -- product.tla --
                            //      stagesInstance == INSTANCE stages WITH template <- sumList(templates), ...
                            //    When resolving "vars", the variables "template", "hybrid", etc. inside
                            //    the tuple MUST be substituted with the INSTANCE expressions.
                            //
                            // Fix for #1090: Check if operator is from local_ops (instance module).
                            // Debug trace for #1090
                            #[cfg(debug_assertions)]
                            debug_log_instance_resolve(name, is_from_local_ops, ctx);

                            let resolve_ctx = if is_from_local_ops {
                                // Keep substitutions for instance module operators
                                ctx.clone()
                            } else {
                                // #3220: Strip both instance_substitutions AND local_ops
                                // for outer-module operators. The previous
                                // without_instance_substitutions() only cleared
                                // substitutions, leaving local_ops from the instanced
                                // module in scope. This allowed inner-module names
                                // (e.g. Node == 0..N-1 from AsyncTerminationDetection)
                                // to shadow outer-module constants (e.g. Node =
                                // {n1,...,n5} from config).
                                ctx.with_outer_resolution_scope()
                            };

                            // Mark as visited before recursing
                            visited.insert(name.clone());
                            let result = self.resolve_action_expr_node(
                                &resolve_ctx,
                                &op_def.body.node,
                                visited,
                            );
                            visited.remove(name);
                            debug_eprintln!(
                                debug_let(),
                                "[DEBUG IDENT] After inlining '{}', result is {:?}",
                                name,
                                std::mem::discriminant(&result)
                            );

                            // Part of #575: For constant-level operators (no state dependencies),
                            // try to evaluate the resolved body and inline the result.
                            //
                            // IMPORTANT: This must be guarded by expression level. The liveness
                            // converter may run with a state / next-state context bound (or under
                            // quantified bindings). If we accidentally pre-evaluate a state- or
                            // action-level operator here, we'd freeze it to the conversion-time
                            // bindings and break liveness semantics.
                            //
                            // Example of a safe constant-level case:
                            //   DesignatedCounter == CHOOSE p \in Prisoner: TRUE
                            //   NormalPrisoner == Prisoner \ {DesignatedCounter}
                            // After resolution, the Prisoner set is inlined, and we can evaluate
                            // the CHOOSE expression to get a concrete value.
                            let level = self.get_level_with_ctx(&resolve_ctx, &result);
                            if level != ExprLevel::Constant {
                                return result;
                            }

                            // Part of #1433: Use eval_speculative with ConstantResolution
                            // to classify expected vs unexpected eval failures.
                            let result_expr = Spanned::dummy(result.clone());
                            match eval_speculative(
                                &resolve_ctx,
                                &result_expr,
                                &[FallbackClass::ConstantResolution],
                            ) {
                                Ok(Some(value)) => {
                                    debug_eprintln!(
                                        debug_subst(),
                                        "[ZERO-ARG] {} evaluated to {:?}",
                                        name,
                                        value
                                    );
                                    if value_is_reifiable_for_substitution(&value) {
                                        if let Ok(reified) = value_to_expr(&value) {
                                            return reified;
                                        }
                                    }
                                    return result;
                                }
                                Ok(None) => {
                                    // Expected — expression depends on state
                                    // despite constant level classification.
                                    return result;
                                }
                                Err(e) => {
                                    // Part of #2806: Unexpected eval error — not ConstantResolution class.
                                    // Log so unexpected errors (DivisionByZero, TypeError, etc.) are
                                    // visible rather than silently swallowed.
                                    eprintln!(
                                        "Warning: unexpected eval error during zero-arg op '{name}' constant folding (kept resolved): {e}"
                                    );
                                    return result;
                                }
                            }
                        }
                    }
                }
                // Not an operator - check if there's an instance substitution for this identifier
                // (e.g., for VARIABLE names that get substituted via INSTANCE ... WITH ...)
                if let Some(sub) = active_instance_sub {
                    let outer_ctx = if ctx.local_ops().is_some() {
                        ctx.with_outer_resolution_scope()
                    } else {
                        ctx.without_instance_substitutions()
                    };
                    return self.resolve_action_expr_node(&outer_ctx, &sub.to.node, visited);
                }
                expr.clone()
            }

            // ModuleRef - keep the reference intact.
            //
            // The evaluator can resolve `M!Op` with the correct instance substitutions and
            // module-local operator scope. Inlining module references here is unnecessary and can
            // be incorrect when the referenced operator body includes module-local operators with
            // parameters.
            Expr::ModuleRef(target, op_name, args) => {
                let new_target = match target {
                    ModuleTarget::Parameterized(name, params) => ModuleTarget::Parameterized(
                        name.clone(),
                        params
                            .iter()
                            .map(|p| self.resolve_action_expr_spanned(ctx, p, visited))
                            .collect(),
                    ),
                    ModuleTarget::Chained(base) => ModuleTarget::Chained(Box::new(
                        self.resolve_action_expr_spanned(ctx, base, visited),
                    )),
                    ModuleTarget::Named(n) => ModuleTarget::Named(n.clone()),
                };
                Expr::ModuleRef(
                    new_target,
                    op_name.clone(),
                    args.iter()
                        .map(|a| self.resolve_action_expr_spanned(ctx, a, visited))
                        .collect(),
                )
            }

            // SubstIn - compose the wrapper substitutions into the current INSTANCE
            // scope and keep resolving inside the body. TLC's liveness converter
            // descends through SubstIn rather than treating it as an opaque leaf.
            Expr::SubstIn(subs, body) => {
                let effective_subs = compose_substitutions(subs, ctx.instance_substitutions());
                let sub_ctx = ctx.with_instance_substitutions(effective_subs);
                self.resolve_action_expr_node(&sub_ctx, &body.node, visited)
            }

            // LET and Apply have dedicated helpers to keep this dispatcher focused.
            Expr::Let(defs, body) => self.resolve_action_let_expr(ctx, defs, body, visited),
            Expr::Apply(op, args) => self.resolve_action_apply_expr(ctx, op, args, visited),

            // Remaining expression variants are handled by the generic recursive resolver.
            _ => self.resolve_action_expr_node_compound(ctx, expr, visited),
        }
    }

    fn resolve_action_let_expr(
        &self,
        ctx: &EvalCtx,
        defs: &[tla_core::ast::OperatorDef],
        body: &Spanned<Expr>,
        visited: &mut std::collections::HashSet<String>,
    ) -> Expr {
        // Expand non-recursive zero-arg LET bindings (like local variables) so liveness
        // ENABLED checks don't depend on carrying a LET evaluation context (#233).
        //
        // If any substituted name remains referenced after rewriting (e.g., due to
        // unexpected AST forms or shadowing), keep the LET wrapper as a correctness
        // fallback so evaluation can still resolve it.
        let mut zero_arg_subs: Vec<(String, Spanned<Expr>)> = Vec::new();
        let mut zero_arg_defs: Vec<tla_core::ast::OperatorDef> = Vec::new();
        let mut param_defs: Vec<tla_core::ast::OperatorDef> = Vec::new();

        for d in defs {
            let resolved_body = self.resolve_action_expr_spanned(ctx, &d.body, visited);
            if d.params.is_empty() {
                // InstanceExpr defs (e.g., G == INSTANCE Graphs) must stay in the LET
                // so eval_let can place them in local_ops for ModuleRef resolution.
                // They are not value-producing and cannot be inlined. (#2984)
                let is_instance = matches!(&resolved_body.node, Expr::InstanceExpr(_, _));
                let is_recursive = Self::expr_references_name(&resolved_body.node, &d.name.node);
                if is_recursive || is_instance {
                    param_defs.push(tla_core::ast::OperatorDef {
                        name: d.name.clone(),
                        params: d.params.clone(),
                        body: resolved_body,
                        local: d.local,
                        contains_prime: d.contains_prime,
                        guards_depend_on_prime: d.guards_depend_on_prime,
                        has_primed_param: d.has_primed_param,
                        is_recursive: d.is_recursive,
                        self_call_count: d.self_call_count,
                    });
                } else {
                    zero_arg_subs.push((d.name.node.clone(), resolved_body.clone()));
                    zero_arg_defs.push(tla_core::ast::OperatorDef {
                        name: d.name.clone(),
                        params: d.params.clone(),
                        body: resolved_body,
                        local: d.local,
                        contains_prime: d.contains_prime,
                        guards_depend_on_prime: d.guards_depend_on_prime,
                        has_primed_param: d.has_primed_param,
                        is_recursive: d.is_recursive,
                        self_call_count: d.self_call_count,
                    });
                }
            } else {
                param_defs.push(tla_core::ast::OperatorDef {
                    name: d.name.clone(),
                    params: d.params.clone(),
                    body: resolved_body,
                    local: d.local,
                    contains_prime: d.contains_prime,
                    guards_depend_on_prime: d.guards_depend_on_prime,
                    has_primed_param: d.has_primed_param,
                    is_recursive: d.is_recursive,
                    self_call_count: d.self_call_count,
                });
            }
        }

        // BUG FIX #3114: Add LET-bound names to `visited` before resolving the body.
        // This prevents the Ident handler from inlining module-level operators that
        // share a name with a LET-local binding (e.g., `nxtQ` action shadowed by
        // `LET nxtQ == Len(queens) + 1`). The Ident handler at line ~105 returns
        // expr.clone() for visited names, keeping them as Ident nodes. Then
        // apply_let_substitutions correctly replaces them with the LET definition body.
        let let_bound_names: Vec<String> = zero_arg_subs.iter().map(|(n, _)| n.clone()).collect();
        for name in &let_bound_names {
            visited.insert(name.clone());
        }
        let resolved_body = self.resolve_action_expr_spanned(ctx, body, visited);
        for name in &let_bound_names {
            visited.remove(name);
        }
        let substituted_body = if zero_arg_subs.is_empty() {
            resolved_body
        } else {
            debug_block!(debug_let(), {
                eprintln!(
                    "[DEBUG LET] Applying {} substitutions:",
                    zero_arg_subs.len()
                );
                for (name, _) in &zero_arg_subs {
                    eprintln!("[DEBUG LET]   Substituting: {name}");
                }
            });
            let result = self.apply_let_substitutions(&resolved_body, &zero_arg_subs);
            debug_block!(debug_let(), {
                for (name, _) in &zero_arg_subs {
                    let still_refs = Self::expr_references_name(&result.node, name);
                    eprintln!("[DEBUG LET]   After subst, still refs {name}? {still_refs}");
                }
            });
            result
        };

        // If all zero-arg substitutions were successful (none referenced after subst),
        // we don't need to keep them in the LET. But if any are still referenced,
        // we need to keep the LET wrapper for evaluation to resolve them.
        let still_references_any_sub = zero_arg_subs
            .iter()
            .any(|(name, _)| Self::expr_references_name(&substituted_body.node, name));

        if still_references_any_sub {
            // Some substitution didn't work - keep all defs for runtime resolution
            let mut all_defs = param_defs;
            all_defs.extend(zero_arg_defs);
            debug_eprintln!(
                debug_let(),
                "[DEBUG LET] Keeping all {} defs (still refs subs)",
                all_defs.len()
            );
            Expr::Let(all_defs, Box::new(substituted_body))
        } else if param_defs.is_empty() {
            // All zero-arg were substituted, no param defs - drop the LET
            debug_eprintln!(
                debug_let(),
                "[DEBUG LET] Dropping LET - all {} zero-arg substituted",
                zero_arg_subs.len()
            );
            substituted_body.node
        } else {
            // Zero-arg were substituted, but have param defs - keep LET with only param_defs
            debug_eprintln!(
                debug_let(),
                "[DEBUG LET] Keeping LET with only {} param defs",
                param_defs.len()
            );
            Expr::Let(param_defs, Box::new(substituted_body))
        }
    }

    /// Helper to resolve a spanned expression while threading through the visited set
    pub(super) fn resolve_action_expr_spanned(
        &self,
        ctx: &EvalCtx,
        expr: &Spanned<Expr>,
        visited: &mut std::collections::HashSet<String>,
    ) -> Spanned<Expr> {
        Spanned {
            node: self.resolve_action_expr_node(ctx, &expr.node, visited),
            span: expr.span,
        }
    }
}
