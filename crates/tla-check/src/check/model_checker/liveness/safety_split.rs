// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Safety/liveness classification and splitting logic.
//!
//! Separates temporal properties into safety-checkable parts (init predicates,
//! always-action formulas) and liveness parts (fairness, leads-to, etc.).

mod instance;

use super::super::{Expr, ModelChecker, ModuleTarget, PropertySafetyParts, Spanned};

/// Classification of a term for safety/liveness splitting.
pub(super) enum TermBucket {
    Init(Spanned<Expr>),
    Always(Spanned<Expr>),
    Liveness(Spanned<Expr>),
}

impl ModelChecker<'_> {
    fn is_real_action_subscript(&self, expr: &Spanned<Expr>) -> bool {
        self.ctx.is_action_subscript_span(expr.span)
    }

    /// Separate a property into safety parts (checkable on transitions) and liveness parts.
    ///
    /// Safety parts include:
    /// - Init predicates (state-level, no temporal operators)
    /// - Always-action formulas: `[]Action` where Action is action-level (may contain primes)
    ///   but has no nested temporal operators
    ///
    /// Liveness parts include:
    /// - `[]<>P` (infinitely often)
    /// - `<>[]P` (eventually always)
    /// - `WF_v(A)`, `SF_v(A)` (fairness)
    /// - `P ~> Q` (leads-to)
    /// - Any formula with nested temporal operators
    ///
    /// Returns (safety_parts, liveness_expr) where:
    /// - safety_parts contains init_terms and always_terms for safety checking
    /// - liveness_expr is Some(conjunction of liveness terms) or None if no liveness
    pub(super) fn separate_safety_liveness_parts(
        &self,
        _prop_name: &str,
        body: &Spanned<Expr>,
    ) -> Option<(PropertySafetyParts, Option<Spanned<Expr>>)> {
        let mut terms = Vec::new();
        Self::flatten_and_terms(body, &mut terms);

        let mut init_terms: Vec<Spanned<Expr>> = Vec::new();
        let mut always_terms: Vec<Spanned<Expr>> = Vec::new();
        let mut liveness_terms: Vec<Spanned<Expr>> = Vec::new();

        for term in terms {
            for bucket in self.classify_term(&term) {
                match bucket {
                    TermBucket::Init(e) => init_terms.push(e),
                    TermBucket::Always(e) => always_terms.push(e),
                    TermBucket::Liveness(e) => liveness_terms.push(e),
                }
            }
        }

        // Build liveness expression as conjunction of liveness terms
        let liveness_expr = if liveness_terms.is_empty() {
            None
        } else {
            let mut iter = liveness_terms.into_iter();
            let Some(mut result) = iter.next() else {
                return Some((
                    PropertySafetyParts {
                        init_terms,
                        always_terms,
                    },
                    None,
                ));
            };
            for term in iter {
                result = Spanned {
                    node: Expr::And(Box::new(result), Box::new(term)),
                    span: body.span,
                };
            }
            Some(result)
        };

        Some((
            PropertySafetyParts {
                init_terms,
                always_terms,
            },
            liveness_expr,
        ))
    }

    /// Classify a single conjunct term into init, always, or liveness buckets.
    fn classify_term(&self, term: &Spanned<Expr>) -> Vec<TermBucket> {
        match &term.node {
            Expr::Always(inner) => {
                let converter = crate::liveness::AstToLive::new();
                let level = converter.get_level_with_ctx(&self.ctx, &inner.node);
                let real_action_subscript = self.is_real_action_subscript(inner);

                if real_action_subscript {
                    if Self::has_nested_temporal_for_safety_split(&term.node)
                        || matches!(level, crate::liveness::ExprLevel::Temporal)
                    {
                        vec![TermBucket::Liveness(term.clone())]
                    } else {
                        vec![TermBucket::Always((**inner).clone())]
                    }
                } else if Self::has_nested_temporal_for_safety_split(&term.node)
                    || Self::contains_enabled(&inner.node)
                {
                    vec![TermBucket::Liveness(term.clone())]
                } else {
                    // Check expression level: state/constant-level []P is always
                    // safety; action-level []A requires real action subscript
                    // provenance to be safety (bare []A without subscript goes
                    // to liveness, matching TLC). Part of #3150.
                    match level {
                        crate::liveness::ExprLevel::Constant
                        | crate::liveness::ExprLevel::State => {
                            vec![TermBucket::Always((**inner).clone())]
                        }
                        crate::liveness::ExprLevel::Action
                        | crate::liveness::ExprLevel::Temporal => {
                            vec![TermBucket::Liveness(term.clone())]
                        }
                    }
                }
            }
            Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => vec![TermBucket::Liveness(term.clone())],
            Expr::Apply(op, _) => {
                if let Expr::Ident(name, _) = &op.node {
                    if name.starts_with("WF_") || name.starts_with("SF_") {
                        return vec![TermBucket::Liveness(term.clone())];
                    }
                }
                if Self::contains_temporal_helper(&term.node) {
                    vec![TermBucket::Liveness(term.clone())]
                } else {
                    vec![TermBucket::Init(term.clone())]
                }
            }
            Expr::Ident(name, _) => self.classify_ident_term(term, name),
            Expr::ModuleRef(target, op_name, args) => {
                self.classify_module_ref_term(term, target, op_name, args)
            }
            _ => {
                if Self::contains_temporal_helper(&term.node) || Self::contains_enabled(&term.node)
                {
                    vec![TermBucket::Liveness(term.clone())]
                } else {
                    vec![TermBucket::Init(term.clone())]
                }
            }
        }
    }

    /// Classify an `Expr::Ident` term by looking up its operator definition.
    fn classify_ident_term(&self, term: &Spanned<Expr>, name: &str) -> Vec<TermBucket> {
        let Some(op_def) = self.module.op_defs.get(name) else {
            return vec![TermBucket::Init(term.clone())];
        };
        if matches!(&op_def.body.node, Expr::And(_, _)) {
            let mut expanded = Vec::new();
            Self::flatten_and_terms(&op_def.body, &mut expanded);
            return expanded
                .iter()
                .map(|subterm| self.classify_flat_subterm(subterm))
                .collect();
        }
        if Self::contains_temporal_helper(&op_def.body.node)
            || Self::contains_enabled(&op_def.body.node)
        {
            if Self::has_nested_temporal_for_safety_split(&op_def.body.node)
                || Self::contains_enabled(&op_def.body.node)
            {
                vec![TermBucket::Liveness(term.clone())]
            } else if let Expr::Always(inner) = &op_def.body.node {
                if self.is_real_action_subscript(inner) {
                    vec![TermBucket::Always((**inner).clone())]
                } else {
                    vec![TermBucket::Liveness(term.clone())]
                }
            } else {
                vec![TermBucket::Liveness(term.clone())]
            }
        } else {
            vec![TermBucket::Init(term.clone())]
        }
    }

    /// Classify a sub-term from an expanded conjunction (no Ident lookup).
    #[allow(clippy::if_same_then_else)]
    fn classify_flat_subterm(&self, subterm: &Spanned<Expr>) -> TermBucket {
        match &subterm.node {
            Expr::Always(inner) => {
                if Self::has_nested_temporal_for_safety_split(&subterm.node)
                    || Self::contains_enabled(&inner.node)
                    || !self.is_real_action_subscript(inner)
                {
                    TermBucket::Liveness(subterm.clone())
                } else {
                    TermBucket::Always((**inner).clone())
                }
            }
            Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => TermBucket::Liveness(subterm.clone()),
            _ => {
                if Self::contains_temporal_helper(&subterm.node)
                    || Self::contains_enabled(&subterm.node)
                {
                    TermBucket::Liveness(subterm.clone())
                } else {
                    TermBucket::Init(subterm.clone())
                }
            }
        }
    }

    /// Classify a `ModuleRef` term by splitting its body into safety/liveness parts.
    fn classify_module_ref_term(
        &self,
        term: &Spanned<Expr>,
        target: &ModuleTarget,
        op_name: &str,
        args: &[Spanned<Expr>],
    ) -> Vec<TermBucket> {
        if let Some(buckets) = self.try_split_module_ref(term, target, op_name, args) {
            buckets
        } else {
            vec![TermBucket::Liveness(term.clone())]
        }
    }

    pub(super) fn flatten_and_terms(expr: &Spanned<Expr>, out: &mut Vec<Spanned<Expr>>) {
        match &expr.node {
            Expr::And(left, right) => {
                Self::flatten_and_terms(left, out);
                Self::flatten_and_terms(right, out);
            }
            _ => out.push(expr.clone()),
        }
    }

    pub(crate) fn has_nested_temporal_for_safety_split(expr: &Expr) -> bool {
        match expr {
            Expr::Always(inner) | Expr::Eventually(inner) => {
                Self::contains_temporal_helper(&inner.node)
            }
            Expr::LeadsTo(_, _) | Expr::WeakFair(_, _) | Expr::StrongFair(_, _) => true,
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::Ident(_, _)
            | Expr::OpRef(_)
            | Expr::Prime(_)
            | Expr::Unchanged(_)
            | Expr::Enabled(_) => false,
            Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b) => {
                Self::has_nested_temporal_for_safety_split(&a.node)
                    || Self::has_nested_temporal_for_safety_split(&b.node)
            }
            Expr::Not(e) => Self::has_nested_temporal_for_safety_split(&e.node),
            _ => Self::contains_temporal_helper(expr),
        }
    }
}

#[cfg(test)]
mod tests;
