// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound expression handling for action resolution in liveness translation.
//!
//! Contains `resolve_action_apply_expr` (function application inlining) and
//! `resolve_action_expr_node_compound` (recursive descent for compound AST nodes).
//!
//! Extracted from `action_resolve.rs` for file-size compliance. Part of #3389.

use super::core::AstToLive;
#[cfg(debug_assertions)]
use super::core::{debug_let, debug_subst};
use crate::eval::EvalCtx;
use tla_core::ast::{BoundVar, Expr};
use tla_core::inlining_is_capture_safe;
use tla_core::Spanned;

impl AstToLive {
    pub(super) fn resolve_action_apply_expr(
        &self,
        ctx: &EvalCtx,
        op: &Spanned<Expr>,
        args: &[Spanned<Expr>],
        visited: &mut std::collections::HashSet<String>,
    ) -> Expr {
        // First resolve all arguments
        let new_args: Vec<_> = args
            .iter()
            .map(|a| self.resolve_action_expr_spanned(ctx, a, visited))
            .collect();

        // Check if the operator is an Ident that resolves to a parameterized operator
        if let Expr::Ident(name, _) = &op.node {
            // Prevent infinite recursion for cyclic definitions
            if !visited.contains(name) {
                if let Some(op_def) = ctx.get_op(name) {
                    // Debug output for operators that might have LET bindings
                    debug_block!(debug_let(), {
                        eprintln!(
                            "[DEBUG APPLY] Resolving {}({} args), body is {:?}",
                            name,
                            new_args.len(),
                            std::mem::discriminant(&op_def.body.node)
                        );
                        if let Expr::Let(defs, _) = &op_def.body.node {
                            for d in defs {
                                eprintln!(
                                    "[DEBUG APPLY]   LET def: {} (params={})",
                                    d.name.node,
                                    d.params.len()
                                );
                            }
                        }
                    });
                    // Inline the operator body with parameter substitution
                    // Part of #708: Check for variable capture before inlining.
                    // If substituting arguments would cause capture, skip inlining
                    // and fall through to keep it as an Apply expression.
                    if !op_def.params.is_empty()
                        && op_def.params.len() == new_args.len()
                        && inlining_is_capture_safe(op_def, &new_args)
                    {
                        // Debug: trace operator inlining (#590)
                        debug_block!(debug_subst(), {
                            eprintln!(
                                "[INLINE] Inlining {}({})",
                                name,
                                op_def
                                    .params
                                    .iter()
                                    .map(|p| p.name.node.as_str())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            );
                            for (i, arg) in new_args.iter().enumerate() {
                                eprintln!("[INLINE]   arg[{}] = {:?}", i, arg.node);
                            }
                        });

                        // Build a mapping from parameter names to argument expressions
                        let outer_ctx = ctx.without_instance_substitutions();

                        // Mark as visited before recursing
                        visited.insert(name.clone());

                        // Substitute parameters with arguments in the body
                        let substituted_body = self.substitute_params_in_expr(
                            &op_def.body.node,
                            &op_def.params,
                            &new_args,
                        );

                        // Debug: show substituted body
                        debug_eprintln!(
                            debug_subst(),
                            "[INLINE] {} body after subst: {:?}",
                            name,
                            substituted_body
                        );

                        // Debug: show result after substitution
                        debug_block!(debug_let(), {
                            eprintln!(
                                "[DEBUG APPLY] After subst for {}: {:?}",
                                name,
                                std::mem::discriminant(&substituted_body)
                            );
                            if let Expr::Let(defs, _) = &substituted_body {
                                for d in defs {
                                    eprintln!("[DEBUG APPLY]   Subst LET def: {}", d.name.node);
                                }
                            }
                        });

                        // Recursively resolve the substituted body
                        let result =
                            self.resolve_action_expr_node(&outer_ctx, &substituted_body, visited);
                        visited.remove(name);
                        return result;
                    }
                }
            }
        }

        // Fall through: keep as Apply with resolved subexpressions
        Expr::Apply(
            Box::new(self.resolve_action_expr_spanned(ctx, op, visited)),
            new_args,
        )
    }

    pub(super) fn resolve_action_expr_node_compound(
        &self,
        ctx: &EvalCtx,
        expr: &Expr,
        visited: &mut std::collections::HashSet<String>,
    ) -> Expr {
        match expr {
            // Binary operators
            Expr::And(a, b) => Expr::And(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Or(a, b) => Expr::Or(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Implies(a, b) => Expr::Implies(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Equiv(a, b) => Expr::Equiv(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Eq(a, b) => Expr::Eq(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Neq(a, b) => Expr::Neq(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::In(a, b) => Expr::In(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::NotIn(a, b) => Expr::NotIn(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),

            // Comparison operators (#575: missing handlers caused fairness constraint bugs)
            Expr::Lt(a, b) => Expr::Lt(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Leq(a, b) => Expr::Leq(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Gt(a, b) => Expr::Gt(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Geq(a, b) => Expr::Geq(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Subseteq(a, b) => Expr::Subseteq(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),

            // Arithmetic operators (#575: missing handlers caused fairness constraint bugs)
            Expr::Add(a, b) => Expr::Add(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Sub(a, b) => Expr::Sub(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Mul(a, b) => Expr::Mul(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Div(a, b) => Expr::Div(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Mod(a, b) => Expr::Mod(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::IntDiv(a, b) => Expr::IntDiv(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Pow(a, b) => Expr::Pow(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Neg(e) => Expr::Neg(Box::new(self.resolve_action_expr_spanned(ctx, e, visited))),

            // Choose expression (#575: must resolve subexpressions)
            Expr::Choose(bound, body) => {
                let new_bound = BoundVar {
                    name: bound.name.clone(),
                    pattern: bound.pattern.clone(),
                    domain: bound
                        .domain
                        .as_ref()
                        .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                };
                Expr::Choose(
                    new_bound,
                    Box::new(self.resolve_action_expr_spanned(ctx, body, visited)),
                )
            }

            // Unary operators
            Expr::Not(e) => Expr::Not(Box::new(self.resolve_action_expr_spanned(ctx, e, visited))),
            Expr::Prime(e) => {
                Expr::Prime(Box::new(self.resolve_action_expr_spanned(ctx, e, visited)))
            }
            Expr::Enabled(e) => {
                Expr::Enabled(Box::new(self.resolve_action_expr_spanned(ctx, e, visited)))
            }
            Expr::Unchanged(e) => {
                Expr::Unchanged(Box::new(self.resolve_action_expr_spanned(ctx, e, visited)))
            }

            // IF-THEN-ELSE
            Expr::If(cond, then_e, else_e) => Expr::If(
                Box::new(self.resolve_action_expr_spanned(ctx, cond, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, then_e, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, else_e, visited)),
            ),

            // Quantifiers
            Expr::Exists(bounds, body) => {
                let new_bounds: Vec<_> = bounds
                    .iter()
                    .map(|b| BoundVar {
                        name: b.name.clone(),
                        pattern: b.pattern.clone(),
                        domain: b
                            .domain
                            .as_ref()
                            .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                    })
                    .collect();
                Expr::Exists(
                    new_bounds,
                    Box::new(self.resolve_action_expr_spanned(ctx, body, visited)),
                )
            }
            Expr::Forall(bounds, body) => {
                let new_bounds: Vec<_> = bounds
                    .iter()
                    .map(|b| BoundVar {
                        name: b.name.clone(),
                        pattern: b.pattern.clone(),
                        domain: b
                            .domain
                            .as_ref()
                            .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                    })
                    .collect();
                Expr::Forall(
                    new_bounds,
                    Box::new(self.resolve_action_expr_spanned(ctx, body, visited)),
                )
            }

            // EXCEPT
            Expr::Except(base, specs) => {
                let new_specs: Vec<_> = specs
                    .iter()
                    .map(|s| {
                        let new_path: Vec<_> = s
                            .path
                            .iter()
                            .map(|p| match p {
                                tla_core::ast::ExceptPathElement::Index(idx) => {
                                    tla_core::ast::ExceptPathElement::Index(
                                        self.resolve_action_expr_spanned(ctx, idx, visited),
                                    )
                                }
                                tla_core::ast::ExceptPathElement::Field(f) => {
                                    tla_core::ast::ExceptPathElement::Field(f.clone())
                                }
                            })
                            .collect();
                        tla_core::ast::ExceptSpec {
                            path: new_path,
                            value: self.resolve_action_expr_spanned(ctx, &s.value, visited),
                        }
                    })
                    .collect();
                Expr::Except(
                    Box::new(self.resolve_action_expr_spanned(ctx, base, visited)),
                    new_specs,
                )
            }

            // Record
            Expr::Record(fields) => {
                let new_fields: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| (k.clone(), self.resolve_action_expr_spanned(ctx, v, visited)))
                    .collect();
                Expr::Record(new_fields)
            }

            // Record access
            Expr::RecordAccess(record, field) => Expr::RecordAccess(
                Box::new(self.resolve_action_expr_spanned(ctx, record, visited)),
                field.clone(),
            ),

            // FuncApply
            Expr::FuncApply(func, arg) => Expr::FuncApply(
                Box::new(self.resolve_action_expr_spanned(ctx, func, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, arg, visited)),
            ),

            // Set operations
            Expr::SetEnum(elems) => {
                let new_elems: Vec<_> = elems
                    .iter()
                    .map(|e| self.resolve_action_expr_spanned(ctx, e, visited))
                    .collect();
                Expr::SetEnum(new_elems)
            }
            Expr::Union(a, b) => Expr::Union(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::Intersect(a, b) => Expr::Intersect(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),
            Expr::SetMinus(a, b) => Expr::SetMinus(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),

            // Tuple
            Expr::Tuple(elems) => {
                let new_elems: Vec<_> = elems
                    .iter()
                    .map(|e| self.resolve_action_expr_spanned(ctx, e, visited))
                    .collect();
                Expr::Tuple(new_elems)
            }

            // Range: a..b (#589)
            Expr::Range(a, b) => Expr::Range(
                Box::new(self.resolve_action_expr_spanned(ctx, a, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, b, visited)),
            ),

            // SetBuilder: {expr : x \in S, y \in T} (#589)
            Expr::SetBuilder(expr, bounds) => {
                let new_bounds: Vec<_> = bounds
                    .iter()
                    .map(|b| BoundVar {
                        name: b.name.clone(),
                        pattern: b.pattern.clone(),
                        domain: b
                            .domain
                            .as_ref()
                            .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                    })
                    .collect();
                Expr::SetBuilder(
                    Box::new(self.resolve_action_expr_spanned(ctx, expr, visited)),
                    new_bounds,
                )
            }

            // SetFilter: {x \in S : P} (#589)
            Expr::SetFilter(bound, predicate) => {
                let new_bound = BoundVar {
                    name: bound.name.clone(),
                    pattern: bound.pattern.clone(),
                    domain: bound
                        .domain
                        .as_ref()
                        .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                };
                Expr::SetFilter(
                    new_bound,
                    Box::new(self.resolve_action_expr_spanned(ctx, predicate, visited)),
                )
            }

            // FuncDef: [x \in S |-> expr] (#589)
            Expr::FuncDef(bounds, expr) => {
                let new_bounds: Vec<_> = bounds
                    .iter()
                    .map(|b| BoundVar {
                        name: b.name.clone(),
                        pattern: b.pattern.clone(),
                        domain: b
                            .domain
                            .as_ref()
                            .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited))),
                    })
                    .collect();
                Expr::FuncDef(
                    new_bounds,
                    Box::new(self.resolve_action_expr_spanned(ctx, expr, visited)),
                )
            }

            // Domain: DOMAIN f (#589)
            Expr::Domain(expr) => Expr::Domain(Box::new(
                self.resolve_action_expr_spanned(ctx, expr, visited),
            )),

            // FuncSet: [S -> T] (#589)
            Expr::FuncSet(s, t) => Expr::FuncSet(
                Box::new(self.resolve_action_expr_spanned(ctx, s, visited)),
                Box::new(self.resolve_action_expr_spanned(ctx, t, visited)),
            ),

            // RecordSet: [a : S, b : T] (#589)
            Expr::RecordSet(fields) => {
                let new_fields: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| (k.clone(), self.resolve_action_expr_spanned(ctx, v, visited)))
                    .collect();
                Expr::RecordSet(new_fields)
            }

            // Times: S \X T (#589)
            Expr::Times(elems) => {
                let new_elems: Vec<_> = elems
                    .iter()
                    .map(|e| self.resolve_action_expr_spanned(ctx, e, visited))
                    .collect();
                Expr::Times(new_elems)
            }

            // Powerset: SUBSET S (#589)
            Expr::Powerset(expr) => Expr::Powerset(Box::new(
                self.resolve_action_expr_spanned(ctx, expr, visited),
            )),

            // BigUnion: UNION S (#589)
            Expr::BigUnion(expr) => Expr::BigUnion(Box::new(
                self.resolve_action_expr_spanned(ctx, expr, visited),
            )),

            // Case: CASE arms [] OTHER -> default (#589)
            Expr::Case(arms, default) => {
                let new_arms: Vec<_> = arms
                    .iter()
                    .map(|arm| tla_core::ast::CaseArm {
                        guard: self.resolve_action_expr_spanned(ctx, &arm.guard, visited),
                        body: self.resolve_action_expr_spanned(ctx, &arm.body, visited),
                    })
                    .collect();
                let new_default = default
                    .as_ref()
                    .map(|d| Box::new(self.resolve_action_expr_spanned(ctx, d, visited)));
                Expr::Case(new_arms, new_default)
            }

            // All other expressions: return unchanged (literals, etc.)
            _ => expr.clone(),
        }
    }
}
