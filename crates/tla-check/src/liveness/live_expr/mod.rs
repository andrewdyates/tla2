// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Live expression AST for temporal formulas
//!
//! This module defines the internal representation for temporal formulas used
//! during liveness checking. It's distinct from the main AST because:
//! 1. It's already in positive normal form (negation pushed to atoms)
//! 2. It separates state predicates from action predicates
//! 3. It supports efficient evaluation during tableau construction
//!
//! Based on TLC's LiveExprNode hierarchy.

mod analysis;
mod display;
mod dnf;
#[cfg(test)]
mod tests;

use crate::eval::BindingChain;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

/// Expression level for liveness formulas
///
/// Corresponds to TLA+ level constants:
/// - Constant: Can be evaluated without any state
/// - State: Depends on current state variables (state predicate)
/// - Action: Depends on current and next state (action predicate)
/// - Temporal: Contains temporal operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ExprLevel {
    /// Constant expression (no state dependency)
    Constant = 0,
    /// State-level expression (depends on current state)
    State = 1,
    /// Action-level expression (depends on current and next state)
    Action = 2,
    /// Temporal expression (contains temporal operators)
    Temporal = 3,
}

/// A liveness expression (temporal formula in positive normal form)
///
/// This represents temporal formulas after conversion from the AST.
/// Negation is pushed down to atoms, so only positive temporal operators appear.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LiveExpr {
    /// Boolean constant (TRUE or FALSE)
    Bool(bool),

    /// State predicate - evaluated on a single state
    /// Contains the original AST expression for evaluation
    StatePred {
        /// The AST expression to evaluate
        expr: Arc<Spanned<Expr>>,
        /// Optional bound-variable bindings (TLC Context-like).
        ///
        /// Used for liveness bounded quantifiers where we enumerate bindings at
        /// conversion time and later evaluate the leaf predicate under those
        /// bindings (no Value→Expr substitution).
        bindings: Option<BindingChain>,
        /// Unique tag for identifying this predicate during tableau construction
        tag: u32,
    },

    /// Action predicate - evaluated on a state transition (s, s')
    /// Used for fairness constraints and primed expressions
    ActionPred {
        /// The AST expression to evaluate
        expr: Arc<Spanned<Expr>>,
        /// Optional bound-variable bindings (TLC Context-like).
        bindings: Option<BindingChain>,
        /// Unique tag for identifying this predicate
        tag: u32,
    },

    /// ENABLED predicate - true if action is enabled in state
    Enabled {
        /// The action expression
        action: Arc<Spanned<Expr>>,
        /// Optional bound-variable bindings (TLC Context-like).
        bindings: Option<BindingChain>,
        /// If true, only count successors that change state (subscripted-action semantics).
        ///
        /// This is used for fairness constraints like `WF_vars(A)` which are defined in TLC
        /// in terms of `ENABLED(<<A>>_vars)`, where `<<A>>_vars == A /\ (vars' ≠ vars)`.
        require_state_change: bool,
        /// The subscript expression for subscripted action semantics.
        /// For `ENABLED<<A>>_e`, this is `e`. If None, uses global state change check.
        subscript: Option<Arc<Spanned<Expr>>>,
        /// Unique tag
        tag: u32,
    },

    /// Conjunction: P /\ Q /\ ...
    And(Vec<LiveExpr>),

    /// Disjunction: P \/ Q \/ ...
    Or(Vec<LiveExpr>),

    /// Negation: ~P
    /// In positive normal form, this only wraps atoms (Bool, StatePred, ActionPred)
    Not(Box<LiveExpr>),

    /// Always: []P
    Always(Box<LiveExpr>),

    /// Eventually: <>P
    Eventually(Box<LiveExpr>),

    /// Next: ()P (LTL next operator - used internally for tableau)
    /// Not part of TLA+ surface syntax but needed for tableau construction
    Next(Box<LiveExpr>),

    /// State changed predicate - true iff subscript' ≠ subscript (non-stuttering transition)
    /// Used to implement subscripted action semantics `<<A>>_e = A /\ (e' ≠ e)`
    StateChanged {
        /// The subscript expression to check for changes.
        /// For `<<A>>_e`, this is `e`. If None, uses global fingerprint comparison.
        subscript: Option<Arc<Spanned<Expr>>>,
        /// Optional bound-variable bindings (TLC Context-like).
        bindings: Option<BindingChain>,
        /// Unique tag for identifying this predicate
        tag: u32,
    },
}

impl LiveExpr {
    /// Extract the unique tag from this expression, if it has one.
    /// Part of #3065: Used for cross-property check result caching.
    pub fn tag(&self) -> Option<u32> {
        match self {
            LiveExpr::StatePred { tag, .. }
            | LiveExpr::ActionPred { tag, .. }
            | LiveExpr::Enabled { tag, .. }
            | LiveExpr::StateChanged { tag, .. } => Some(*tag),
            _ => None,
        }
    }

    /// Create a true constant
    pub fn true_const() -> Self {
        LiveExpr::Bool(true)
    }

    /// Create a false constant
    pub fn false_const() -> Self {
        LiveExpr::Bool(false)
    }

    /// Create a state predicate
    pub fn state_pred(expr: Arc<Spanned<Expr>>, tag: u32) -> Self {
        LiveExpr::StatePred {
            expr,
            bindings: None,
            tag,
        }
    }

    /// Create a state predicate, optionally carrying quantified-variable bindings.
    pub fn state_pred_with_bindings(
        expr: Arc<Spanned<Expr>>,
        tag: u32,
        bindings: Option<BindingChain>,
    ) -> Self {
        LiveExpr::StatePred {
            expr,
            bindings,
            tag,
        }
    }

    /// Create an action predicate
    pub fn action_pred(expr: Arc<Spanned<Expr>>, tag: u32) -> Self {
        LiveExpr::ActionPred {
            expr,
            bindings: None,
            tag,
        }
    }

    /// Create an action predicate, optionally carrying quantified-variable bindings.
    pub fn action_pred_with_bindings(
        expr: Arc<Spanned<Expr>>,
        tag: u32,
        bindings: Option<BindingChain>,
    ) -> Self {
        LiveExpr::ActionPred {
            expr,
            bindings,
            tag,
        }
    }

    /// Create an ENABLED predicate
    pub fn enabled(action: Arc<Spanned<Expr>>, tag: u32) -> Self {
        LiveExpr::Enabled {
            action,
            bindings: None,
            require_state_change: false,
            subscript: None,
            tag,
        }
    }

    /// Create an ENABLED predicate that requires a non-stuttering successor.
    /// The subscript expression is used to check for state change (e' ≠ e).
    pub fn enabled_subscripted(
        action: Arc<Spanned<Expr>>,
        subscript: Option<Arc<Spanned<Expr>>>,
        tag: u32,
    ) -> Self {
        LiveExpr::Enabled {
            action,
            bindings: None,
            require_state_change: true,
            subscript,
            tag,
        }
    }

    pub fn enabled_with_bindings(
        action: Arc<Spanned<Expr>>,
        require_state_change: bool,
        subscript: Option<Arc<Spanned<Expr>>>,
        tag: u32,
        bindings: Option<BindingChain>,
    ) -> Self {
        LiveExpr::Enabled {
            action,
            bindings,
            require_state_change,
            subscript,
            tag,
        }
    }

    /// Create a state changed predicate (e' ≠ e for subscript e)
    /// If subscript is None, uses global fingerprint comparison.
    pub fn state_changed(subscript: Option<Arc<Spanned<Expr>>>, tag: u32) -> Self {
        LiveExpr::StateChanged {
            subscript,
            bindings: None,
            tag,
        }
    }

    pub fn state_changed_with_bindings(
        subscript: Option<Arc<Spanned<Expr>>>,
        tag: u32,
        bindings: Option<BindingChain>,
    ) -> Self {
        LiveExpr::StateChanged {
            subscript,
            bindings,
            tag,
        }
    }

    /// Create a conjunction
    pub fn and(exprs: Vec<LiveExpr>) -> Self {
        // Short-circuit: if any conjunct is FALSE, the whole conjunction is FALSE.
        // Filter out TRUE conjuncts (identity element for AND).
        // This is critical for DNF performance: quantified fairness constraints
        // like `\A oi, oj \in D : (oi # oj) => WF(...)` produce Bool(true)
        // for trivial pairs (oi = oj). Without filtering, these inflate the
        // DNF cross-product exponentially (3^N vs 1^N per trivial pair).
        if exprs
            .iter()
            .any(|expr| matches!(expr, LiveExpr::Bool(false)))
        {
            return LiveExpr::Bool(false);
        }
        let filtered: Vec<LiveExpr> = exprs
            .into_iter()
            .filter(|expr| !matches!(expr, LiveExpr::Bool(true)))
            .collect();
        if filtered.is_empty() {
            LiveExpr::Bool(true)
        } else if filtered.len() == 1 {
            filtered.into_iter().next().unwrap_or(LiveExpr::Bool(true))
        } else {
            LiveExpr::And(filtered)
        }
    }

    /// Create a disjunction
    pub fn or(exprs: Vec<LiveExpr>) -> Self {
        // Short-circuit: if any disjunct is TRUE, the whole disjunction is TRUE.
        // Filter out FALSE disjuncts (identity element for OR).
        if exprs
            .iter()
            .any(|expr| matches!(expr, LiveExpr::Bool(true)))
        {
            return LiveExpr::Bool(true);
        }
        let filtered: Vec<LiveExpr> = exprs
            .into_iter()
            .filter(|expr| !matches!(expr, LiveExpr::Bool(false)))
            .collect();
        if filtered.is_empty() {
            LiveExpr::Bool(false)
        } else if filtered.len() == 1 {
            filtered.into_iter().next().unwrap_or(LiveExpr::Bool(false))
        } else {
            LiveExpr::Or(filtered)
        }
    }

    /// Create a negation
    #[allow(clippy::should_implement_trait)]
    pub fn not(expr: LiveExpr) -> Self {
        match expr {
            LiveExpr::Bool(value) => LiveExpr::Bool(!value),
            LiveExpr::Not(inner) => *inner,
            _ => LiveExpr::Not(Box::new(expr)),
        }
    }

    /// Create an always expression
    pub fn always(expr: LiveExpr) -> Self {
        LiveExpr::Always(Box::new(expr))
    }

    /// Create an eventually expression
    pub fn eventually(expr: LiveExpr) -> Self {
        LiveExpr::Eventually(Box::new(expr))
    }

    /// Create a next expression
    pub fn next(expr: LiveExpr) -> Self {
        LiveExpr::Next(Box::new(expr))
    }
}
