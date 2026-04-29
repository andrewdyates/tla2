// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded-quantifier conversion helpers split from `temporal_convert.rs`.
//!
//! Part of #2853.

use super::super::live_expr::{ExprLevel, LiveExpr};
use super::core::{is_binding_error, is_non_enumerable_error, AstToLive};
use super::errors::ConvertError;
use super::reify::value_variant_name;
use crate::eval::{eval_entry, eval_iter_set, EvalCtx};
use crate::Value;
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr};
use tla_core::Spanned;

impl AstToLive {
    /// Convert a bounded quantifier (\E or \A) over temporal formulas.
    ///
    /// This expands quantified temporal formulas by enumerating all values in
    /// the domain and building a disjunction (for \E) or conjunction (for \A).
    ///
    /// Based on TLC's Liveness.java handling of OPCODE_be and OPCODE_bf.
    pub(super) fn convert_bounded_quantifier(
        &self,
        ctx: &EvalCtx,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
        is_exists: bool,
        original: Arc<Spanned<Expr>>,
    ) -> Result<LiveExpr, ConvertError> {
        // TLC only expands bounded quantifiers in liveness conversion when the
        // overall quantified expression is temporal-level; otherwise it treats
        // the original expression as a leaf predicate by level.
        let level = self.get_level_with_ctx(ctx, &original.node);
        if level <= ExprLevel::Action {
            return self.predicate_by_level(ctx, &original, level);
        }

        self.convert_bounded_quantifier_with_bindings(
            ctx,
            bounds,
            body,
            is_exists,
            &original,
            self.current_quantifier_bindings(),
        )
    }

    pub(super) fn predicate_by_level(
        &self,
        ctx: &EvalCtx,
        original: &Arc<Spanned<Expr>>,
        level: ExprLevel,
    ) -> Result<LiveExpr, ConvertError> {
        match level {
            ExprLevel::Constant => match eval_entry(ctx, original.as_ref()) {
                Ok(Value::Bool(b)) => Ok(LiveExpr::Bool(b)),
                Ok(_) => Err(ConvertError::NonBooleanConstant(Arc::clone(original))),
                Err(e) if is_binding_error(&e) || is_non_enumerable_error(&e) => {
                    // Unbound variable/operator or non-enumerable domain (e.g.,
                    // Seq({1}) which is infinite): level was misclassified as
                    // constant or the expression can't be evaluated to a concrete
                    // value. Fall back to state predicate — TLC treats these
                    // constant-level quantifiers as unevaluated predicates too.
                    // Part of #4067.
                    let qualified = if self.current_target().is_some() {
                        self.reify_current_target_leaf_expr(ctx, original.as_ref())
                    } else {
                        self.qualify_predicate_expr(ctx, original.as_ref())
                    };
                    let wrapped = self.wrap_in_let_defs(qualified);
                    Ok(LiveExpr::state_pred_with_bindings(
                        Arc::new(wrapped),
                        self.alloc_tag(),
                        self.current_quantifier_bindings(),
                    ))
                }
                Err(e) => Err(ConvertError::EvalFailed {
                    original: Arc::clone(original),
                    source: e,
                }),
            },
            ExprLevel::State => {
                let qualified = if self.current_target().is_some() {
                    self.reify_current_target_leaf_expr(ctx, original.as_ref())
                } else {
                    self.qualify_predicate_expr(ctx, original.as_ref())
                };
                let wrapped = self.wrap_in_let_defs(qualified);
                Ok(LiveExpr::state_pred_with_bindings(
                    Arc::new(wrapped),
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }
            ExprLevel::Action => {
                // Action-level predicate: use resolve_action_expr to inline operators
                // and expand LET bindings, matching core.rs convert() contract (#1707).
                // qualify_predicate_expr is insufficient - it only handles INSTANCE
                // qualification and is a no-op without an INSTANCE target, leaving
                // operator references and LET bindings unresolved. These unresolved
                // references cause "Undefined variable" errors during SCC checking
                // when the original evaluation context is no longer available.
                let resolved = self.resolve_action_expr(ctx, original.as_ref());
                let wrapped = self.wrap_in_let_defs(resolved);
                Ok(LiveExpr::action_pred_with_bindings(
                    Arc::new(wrapped),
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }
            ExprLevel::Temporal => Err(ConvertError::UnsupportedTemporal(Arc::clone(original))),
        }
    }

    fn convert_bounded_quantifier_with_bindings(
        &self,
        ctx: &EvalCtx,
        bounds: &[BoundVar],
        body: &Spanned<Expr>,
        is_exists: bool,
        original: &Arc<Spanned<Expr>>,
        bindings: Option<crate::eval::BindingChain>,
    ) -> Result<LiveExpr, ConvertError> {
        if bounds.is_empty() {
            // Part of #2895: Apply liveness bindings via BindingChain.
            let ctx = match bindings {
                Some(ref chain) => ctx.with_liveness_bindings(chain),
                None => ctx.clone(),
            };
            let _guard = self.push_quantifier_bindings(bindings);
            return self.convert(&ctx, body);
        }

        let first = &bounds[0];
        let rest = &bounds[1..];

        // Part of #2895: Apply liveness bindings via BindingChain.
        let ctx = match bindings {
            Some(ref chain) => ctx.with_liveness_bindings(chain),
            None => ctx.clone(),
        };

        // Get the domain - it must be evaluable at conversion time (constant level).
        let domain = match &first.domain {
            Some(d) => d,
            None => {
                // Unbounded quantifier - cannot handle in liveness.
                return self.bounded_quantifier_enumeration_failed(
                    &ctx,
                    original,
                    Some("unbounded quantifier cannot be expanded in liveness".to_string()),
                );
            }
        };

        // Evaluate domain to get the set of values.
        let domain_value = match eval_entry(&ctx, domain) {
            Ok(v) => v,
            Err(e) => {
                return self.bounded_quantifier_enumeration_failed(
                    &ctx,
                    original,
                    Some(format!(
                        "bounded-quantifier domain {:?} evaluation failed: {}",
                        domain.node, e
                    )),
                );
            }
        };

        // Iterate over domain values.
        // Part of #1828: use eval_iter_set for SetPred-aware iteration.
        // Part of #3015: use eval_iter_set (not TLC-normalized) for liveness conversion.
        // Liveness bounded quantifiers expand to OR/AND which are commutative - element
        // order doesn't affect correctness. TLC-normalized iteration fails for sets
        // containing non-comparable elements (e.g., SetPred) because TLC sorting requires
        // element comparison via iter_set(), which fails for infinite set elements.
        let domain_elems: Vec<Value> = match eval_iter_set(&ctx, &domain_value, Some(domain.span)) {
            Ok(iter) => iter.collect(),
            Err(e) => {
                // Part of #1433: preserve the concrete iteration error details
                // instead of collapsing everything into a generic
                // "domain is not enumerable" label.
                return self.bounded_quantifier_enumeration_failed(
                    &ctx,
                    original,
                    Some(format!(
                        "bounded-quantifier domain {:?} iteration failed (got {}): {}",
                        domain.node,
                        value_variant_name(&domain_value),
                        e,
                    )),
                );
            }
        };

        let mut parts: Vec<LiveExpr> = Vec::new();

        for elem in domain_elems {
            let new_bindings =
                self.extend_bindings_for_bound(bindings.as_ref(), first, &elem, original)?;
            let converted = self.convert_bounded_quantifier_with_bindings(
                &ctx,
                rest,
                body,
                is_exists,
                original,
                new_bindings,
            )?;
            parts.push(converted);
        }

        if parts.is_empty() {
            // Empty domain: \E over empty set is FALSE, \A over empty set is TRUE.
            // This matches TLC's behavior in Liveness.java.
            Ok(LiveExpr::Bool(!is_exists))
        } else if is_exists {
            Ok(LiveExpr::or(parts))
        } else {
            Ok(LiveExpr::and(parts))
        }
    }

    fn bounded_quantifier_enumeration_failed(
        &self,
        ctx: &EvalCtx,
        original: &Arc<Spanned<Expr>>,
        reason: Option<String>,
    ) -> Result<LiveExpr, ConvertError> {
        // TLC's bounded-quantifier conversion catches enumeration failures (including
        // non-enumerable domains) and either:
        // - falls back to treating the original expression as a predicate leaf
        //   (when <= Action), or
        // - errors that it cannot handle the formula (when > Action).
        let level = self.get_level_with_ctx(ctx, &original.node);
        if level <= ExprLevel::Action {
            return self.predicate_by_level(ctx, original, level);
        }
        Err(ConvertError::CannotHandleFormula {
            original: Arc::clone(original),
            location_module_name: self.location_module_name_for_error(),
            reason,
        })
    }

    /// Add substitution mappings for a bound variable to a BindingChain.
    ///
    /// Handles simple variable binding and tuple destructuring patterns.
    /// TLC-parity: accepts tuple-like values (Seq, Tuple, sequence-like functions).
    ///
    /// Part of #2895: Uses BindingChain instead of FastBinding.
    fn extend_bindings_for_bound(
        &self,
        parent: Option<&crate::eval::BindingChain>,
        bound: &BoundVar,
        elem: &Value,
        original: &Arc<Spanned<Expr>>,
    ) -> Result<Option<crate::eval::BindingChain>, ConvertError> {
        use tla_core::ast::BoundPattern;
        use tla_core::name_intern::intern_name;

        let base = parent
            .cloned()
            .unwrap_or_else(crate::eval::BindingChain::empty);

        match &bound.pattern {
            Some(BoundPattern::Tuple(vars)) => {
                // Destructure tuple-like value and add substitution for each variable.
                // TLC-parity: accept Seq, Tuple, and sequence-like functions (domain 1..n).
                if let Some(tuple) = elem.to_tuple_like_elements() {
                    if tuple.len() != vars.len() {
                        return Err(ConvertError::BoundTuplePatternMismatch {
                            original: Arc::clone(original),
                            expected_arity: vars.len(),
                            actual_value_variant: value_variant_name(elem),
                            actual_arity: Some(tuple.len()),
                        });
                    }
                    let mut chain = base;
                    for (var, val) in vars.iter().zip(tuple.iter()) {
                        let name_id = intern_name(var.node.as_str());
                        chain = chain.cons(name_id, crate::eval::BindingValue::eager(val.clone()));
                    }
                    Ok(Some(chain))
                } else {
                    Err(ConvertError::BoundTuplePatternMismatch {
                        original: Arc::clone(original),
                        expected_arity: vars.len(),
                        actual_value_variant: value_variant_name(elem),
                        actual_arity: None,
                    })
                }
            }
            Some(BoundPattern::Var(var)) => {
                let name_id = intern_name(var.node.as_str());
                Ok(Some(base.cons(
                    name_id,
                    crate::eval::BindingValue::eager(elem.clone()),
                )))
            }
            None => {
                let name_id = intern_name(bound.name.node.as_str());
                Ok(Some(base.cons(
                    name_id,
                    crate::eval::BindingValue::eager(elem.clone()),
                )))
            }
        }
    }
}
