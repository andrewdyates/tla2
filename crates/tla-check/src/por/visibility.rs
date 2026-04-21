// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Visibility analysis for the C3 ample set condition.
//!
//! An action is "visible" if it can change the truth value of checked
//! invariants. Visible actions must be included in the ample set.

use rustc_hash::FxHashSet;

use crate::var_index::VarIndex;
use tla_core::ast::Expr;
use tla_core::span::Spanned;

use super::dependencies::ActionDependencies;
use super::dependencies_ast::extract_dependencies_ast_expr;

use crate::enumerate::expand_operators;
use tla_eval::EvalCtx;

/// Variables that appear in invariants (for C3 visibility condition)
///
/// An action is "visible" if it can change the truth value of checked invariants.
/// If an action is visible, it must be included in the ample set (C3 condition).
#[derive(Debug, Clone, Default)]
pub(crate) struct VisibilitySet {
    /// Variables that appear in invariants
    pub(super) vars: FxHashSet<VarIndex>,
    /// Conservative fallback: treat all actions as visible.
    /// Set when config invariant lookup fails unexpectedly.
    all_visible: bool,
}

impl VisibilitySet {
    /// Create an empty visibility set
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create visibility set from eval-based invariant expressions.
    ///
    /// Part of #3354 Slice 4: replaces the old `from_invariants(&[CompiledGuard])`
    /// with direct AST-based extraction. Uses the same `extract_dependencies_ast_expr`
    /// that the action dependency path uses.
    ///
    /// Part of #3461: only used in tests; production code uses
    /// `extend_from_expanded_expr` which handles operator expansion.
    #[cfg(test)]
    pub(crate) fn from_eval_invariants(invariants: &[(String, Spanned<Expr>)]) -> Self {
        let mut vars = FxHashSet::default();
        for (_name, expr) in invariants {
            let mut deps = ActionDependencies::new();
            extract_dependencies_ast_expr(&expr.node, &mut deps);
            vars.extend(deps.reads);
        }
        VisibilitySet {
            vars,
            all_visible: false,
        }
    }

    /// Extend visibility from an invariant expression, expanding operator
    /// references first so that `extract_dependencies_ast_expr` can see
    /// through wrapper operators to the underlying state variable reads.
    ///
    /// Part of #3449: config-level INVARIANT entries are name-only strings.
    /// Their bodies must be resolved and expanded before dependency extraction.
    pub(crate) fn extend_from_expanded_expr(&mut self, ctx: &EvalCtx, expr: &Spanned<Expr>) {
        let expanded = expand_operators(ctx, expr);
        let mut deps = ActionDependencies::new();
        extract_dependencies_ast_expr(&expanded.node, &mut deps);
        self.vars.extend(deps.reads);
    }

    /// Mark all actions as visible (conservative fallback).
    ///
    /// Used when config invariant lookup fails unexpectedly at POR setup.
    /// Disables all reduction opportunities rather than continuing with
    /// incomplete visibility.
    pub(crate) fn mark_all_visible(&mut self) {
        self.all_visible = true;
    }

    /// Check if a specific variable is in the visibility set.
    #[cfg(test)]
    pub(crate) fn contains_var(&self, var: &VarIndex) -> bool {
        self.vars.contains(var)
    }

    /// Check if an action is visible (writes to variables in invariants)
    ///
    /// An action is visible if it writes to any variable that appears in
    /// the checked invariants. Visible actions cannot be reduced away
    /// because they might change the truth value of the property being checked.
    pub(crate) fn is_action_visible(&self, deps: &ActionDependencies) -> bool {
        self.all_visible || !deps.writes.is_disjoint(&self.vars)
    }
}
