// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::live_expr::LiveExpr;
use super::core::AstToLive;
use super::errors::ConvertError;
use super::temporal_fairness::{parse_subscript_from_fused_name, resolve_module_target_ctx};
use crate::eval::{apply_substitutions, EvalCtx, OpEnv};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

impl AstToLive {
    /// Convert temporal-level expressions
    pub(super) fn convert_temporal(
        &self,
        ctx: &EvalCtx,
        expr: &Expr,
        original: Arc<Spanned<Expr>>,
    ) -> Result<LiveExpr, ConvertError> {
        match expr {
            // Boolean constants
            Expr::Bool(b) => Ok(LiveExpr::Bool(*b)),

            // Conjunction
            Expr::And(left, right) => {
                let left_live = self.convert(ctx, left)?;
                let right_live = self.convert(ctx, right)?;
                Ok(LiveExpr::and(vec![left_live, right_live]))
            }

            // Disjunction
            Expr::Or(left, right) => {
                let left_live = self.convert(ctx, left)?;
                let right_live = self.convert(ctx, right)?;
                Ok(LiveExpr::or(vec![left_live, right_live]))
            }

            // Negation
            Expr::Not(inner) => {
                let inner_live = self.convert(ctx, inner)?;
                Ok(LiveExpr::not(inner_live))
            }

            // Implication: A => B becomes ~A \/ B
            Expr::Implies(left, right) => {
                let left_live = self.convert(ctx, left)?;
                let right_live = self.convert(ctx, right)?;
                Ok(LiveExpr::or(vec![LiveExpr::not(left_live), right_live]))
            }

            // Equivalence: A <=> B becomes (A /\ B) \/ (~A /\ ~B)
            Expr::Equiv(left, right) => {
                let left_live = self.convert(ctx, left)?;
                let right_live = self.convert(ctx, right)?;
                // (A /\ B) \/ (~A /\ ~B)
                let both_true = LiveExpr::and(vec![left_live.clone(), right_live.clone()]);
                let both_false =
                    LiveExpr::and(vec![LiveExpr::not(left_live), LiveExpr::not(right_live)]);
                Ok(LiveExpr::or(vec![both_true, both_false]))
            }

            // Temporal: Always []P
            Expr::Always(inner) => {
                let inner_live = self.convert(ctx, inner)?;
                Ok(LiveExpr::always(inner_live))
            }

            // Temporal: Eventually <>P
            Expr::Eventually(inner) => {
                let inner_live = self.convert(ctx, inner)?;
                Ok(LiveExpr::eventually(inner_live))
            }

            // Leads-to: P ~> Q expands to [](P => <>Q) = [](~P \/ <>Q)
            Expr::LeadsTo(left, right) => {
                let left_live = self.convert(ctx, left)?;
                let right_live = self.convert(ctx, right)?;
                // [](~P \/ <>Q)
                let implies_eventually = LiveExpr::or(vec![
                    LiveExpr::not(left_live),
                    LiveExpr::eventually(right_live),
                ]);
                Ok(LiveExpr::always(implies_eventually))
            }

            Expr::WeakFair(subscript, action) => {
                Ok(self.build_fairness_expansion(ctx, action, subscript, true))
            }

            Expr::StrongFair(subscript, action) => {
                Ok(self.build_fairness_expansion(ctx, action, subscript, false))
            }

            // ENABLED A
            Expr::Enabled(inner) => {
                // Resolve any operator references in the action expression
                let resolved_action = self.resolve_action_expr(ctx, inner);
                Ok(LiveExpr::enabled_with_bindings(
                    Arc::new(resolved_action),
                    false,
                    None,
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }

            // Prime: x' - this is action level, handled by get_level returning Action
            Expr::Prime(_) => {
                let qualified = self.qualify_predicate_expr(ctx, original.as_ref());
                let wrapped = self.wrap_in_let_defs(qualified);
                Ok(LiveExpr::action_pred_with_bindings(
                    Arc::new(wrapped),
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }

            // IF-THEN-ELSE: IF g THEN a ELSE b becomes (g /\ a) \/ (~g /\ b)
            Expr::If(guard, then_expr, else_expr) => {
                let guard_live = self.convert(ctx, guard)?;
                let then_live = self.convert(ctx, then_expr)?;
                let else_live = self.convert(ctx, else_expr)?;

                let then_branch = LiveExpr::and(vec![guard_live.clone(), then_live]);
                let else_branch = LiveExpr::and(vec![LiveExpr::not(guard_live), else_live]);

                Ok(LiveExpr::or(vec![then_branch, else_branch]))
            }

            // Bounded Exists: \E x \in S: Body
            // Expand to disjunction over all values in S
            // Based on TLC's Liveness.java OPCODE_be handling (lines 222-251)
            Expr::Exists(bounds, body) => {
                self.convert_bounded_quantifier(ctx, bounds, body, true, original)
            }

            // Bounded Forall: \A x \in S: Body
            // Expand to conjunction over all values in S
            // Based on TLC's Liveness.java OPCODE_bf handling (lines 253-286)
            Expr::Forall(bounds, body) => {
                self.convert_bounded_quantifier(ctx, bounds, body, false, original)
            }

            // Handle WF_xxx and SF_xxx parsed as function applications
            // This happens because the lexer matches "WF_vars" as a single identifier
            // instead of "WF_" token followed by "vars" identifier.
            Expr::Apply(op, args) if args.len() == 1 => {
                if let Expr::Ident(name, _) = &op.node {
                    if let Some(subscript_name) = name.strip_prefix("WF_") {
                        let subscript_expr =
                            parse_subscript_from_fused_name(subscript_name, op.span);
                        return Ok(self.build_fairness_expansion(
                            ctx,
                            &args[0],
                            &subscript_expr,
                            true,
                        ));
                    }
                    if let Some(subscript_name) = name.strip_prefix("SF_") {
                        let subscript_expr =
                            parse_subscript_from_fused_name(subscript_name, op.span);
                        return Ok(self.build_fairness_expansion(
                            ctx,
                            &args[0],
                            &subscript_expr,
                            false,
                        ));
                    }
                }
                // Fall through to default handling
                let actual_level = self.get_level_with_ctx(ctx, expr);
                self.predicate_by_level(ctx, &original, actual_level)
            }

            // Module reference: look up the actual operator and convert its body
            Expr::ModuleRef(instance_name, op_name, args) => {
                // For now, only inline zero-argument module references.
                if args.is_empty() {
                    if let Some(instance_ctx) = resolve_module_target_ctx(ctx, instance_name) {
                        if let Some(op_def) = instance_ctx.get_op(op_name) {
                            if op_def.params.is_empty() {
                                let substituted_body = match instance_ctx.instance_substitutions() {
                                    Some(subs) => apply_substitutions(&op_def.body, subs),
                                    None => op_def.body.clone(),
                                };
                                let _guard = self.push_target(Arc::new(instance_name.clone()));
                                return self.convert(&instance_ctx, &substituted_body);
                            }
                        }
                    }
                }
                // If we can't resolve it, fall back to predicate
                let actual_level = self.get_level_with_ctx(ctx, expr);
                self.predicate_by_level(ctx, &original, actual_level)
            }

            // Identifier reference: look up the operator definition and convert its body
            Expr::Ident(name, _) => {
                let from_local = ctx
                    .local_ops()
                    .as_ref()
                    .is_some_and(|l| l.contains_key(name));
                if !from_local {
                    if let Some(sub) = ctx.active_instance_substitution(name) {
                        let outer_ctx = if ctx.local_ops().is_some() {
                            ctx.with_outer_resolution_scope()
                        } else {
                            ctx.without_instance_substitutions()
                        };
                        return self.convert(&outer_ctx, &sub.to);
                    }
                }

                // Look up the operator to get its body (respecting module-local operator scopes)
                if let Some(op_def) = ctx.get_op(name) {
                    // Only inline zero-argument operators
                    if op_def.params.is_empty() {
                        // #2434: only substitute instanced-module (local_ops) operators
                        let substituted_body = match (from_local, ctx.instance_substitutions()) {
                            (true, Some(subs)) => apply_substitutions(&op_def.body, subs),
                            _ => op_def.body.clone(),
                        };
                        // #3220: when the operator is from the outer module
                        // (shared.ops, not local_ops) and we're inside an
                        // INSTANCE scope, strip the INSTANCE scope so the body
                        // resolves in the outer module's context. Prevents
                        // inner-module names (e.g. Node == 0..N-1) from
                        // shadowing outer-module constants (e.g. Node =
                        // {n1,...,n5} from config). Parallels
                        // action_resolve.rs which strips instance_substitutions
                        // for outer-module operators; here we also strip
                        // local_ops via with_outer_resolution_scope().
                        let convert_ctx = if !from_local && ctx.local_ops().is_some() {
                            ctx.with_outer_resolution_scope()
                        } else {
                            ctx.clone()
                        };
                        return self.convert(&convert_ctx, &substituted_body);
                    }
                }
                // If we can't resolve it, fall back to predicate
                let actual_level = self.get_level_with_ctx(ctx, expr);
                self.predicate_by_level(ctx, &original, actual_level)
            }

            // LET expressions: add definitions to context and convert body
            Expr::Let(defs, body) => {
                // Clone existing local_ops or create new
                let mut local_ops: OpEnv = match ctx.local_ops().as_ref() {
                    Some(ops) => (**ops).clone(),
                    None => OpEnv::new(),
                };
                // Add LET definitions to local_ops for resolution during conversion
                for def in defs {
                    local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
                }
                // Create new context with merged local_ops
                let new_ctx = ctx.with_local_ops(local_ops);
                // Push LET definitions onto stack so predicates can be wrapped
                let _guard = self.push_let_defs(defs.clone());
                // Convert the body with the new context
                self.convert(&new_ctx, body)
            }

            // CASE: CASE g1 -> b1 [] g2 -> b2 [] OTHER -> d
            // Convert to disjunction: (g1 /\ b1) \/ (g2 /\ b2) \/ ... \/ d
            // Based on TLC's Liveness.java handling of CASE at temporal level.
            Expr::Case(arms, other) => {
                let mut parts: Vec<LiveExpr> = Vec::with_capacity(arms.len() + 1);
                for arm in arms {
                    let guard_live = self.convert(ctx, &arm.guard)?;
                    let body_live = self.convert(ctx, &arm.body)?;
                    parts.push(LiveExpr::and(vec![guard_live, body_live]));
                }
                if let Some(other_expr) = other {
                    parts.push(self.convert(ctx, other_expr)?);
                }
                Ok(LiveExpr::or(parts))
            }

            Expr::Label(label) => self.convert(ctx, &label.body),

            // Expressions that are not inherently temporal but may have been classified
            // as temporal by get_level_with_ctx due to subexpressions. Re-evaluate the
            // actual resolved level and treat as predicate if sub-temporal, or error if
            // truly temporal. These variants should not normally reach convert_temporal
            // but can when operator resolution or subexpression analysis classifies them
            // as temporal level.
            // Apply without the WF_/SF_ guard (multi-arg operators, or non-WF/SF single-arg)
            Expr::Apply(_, _)
            | Expr::FuncApply(_, _)
            | Expr::Choose(_, _)
            | Expr::StateVar(_, _, _)
            | Expr::OpRef(_)
            | Expr::InstanceExpr(_, _)
            | Expr::Lambda(_, _)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::SetEnum(_)
            | Expr::SetBuilder(_, _)
            | Expr::SetFilter(_, _)
            | Expr::In(_, _)
            | Expr::NotIn(_, _)
            | Expr::Subseteq(_, _)
            | Expr::Union(_, _)
            | Expr::Intersect(_, _)
            | Expr::SetMinus(_, _)
            | Expr::Powerset(_)
            | Expr::BigUnion(_)
            | Expr::FuncDef(_, _)
            | Expr::Domain(_)
            | Expr::Except(_, _)
            | Expr::FuncSet(_, _)
            | Expr::Record(_)
            | Expr::RecordAccess(_, _)
            | Expr::RecordSet(_)
            | Expr::Tuple(_)
            | Expr::Times(_)
            | Expr::Unchanged(_)
            | Expr::Eq(_, _)
            | Expr::Neq(_, _)
            | Expr::Lt(_, _)
            | Expr::Leq(_, _)
            | Expr::Gt(_, _)
            | Expr::Geq(_, _)
            | Expr::Add(_, _)
            | Expr::Sub(_, _)
            | Expr::Mul(_, _)
            | Expr::Div(_, _)
            | Expr::IntDiv(_, _)
            | Expr::Mod(_, _)
            | Expr::Pow(_, _)
            | Expr::Neg(_)
            | Expr::Range(_, _) => {
                let actual_level = self.get_level_with_ctx(ctx, expr);
                self.predicate_by_level(ctx, &original, actual_level)
            }

            // SubstIn: apply the deferred substitutions to the body at the AST
            // level, then convert the result. TLC's liveness converter descends
            // through SubstIn rather than treating it as an opaque leaf — otherwise
            // INSTANCE substitutions are silently dropped (see #3166).
            Expr::SubstIn(subs, body) => {
                let substituted = apply_substitutions(body, subs);
                self.convert(ctx, &substituted)
            }
        }
    }
}
