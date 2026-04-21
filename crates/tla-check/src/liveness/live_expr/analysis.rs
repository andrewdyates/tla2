// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ExprLevel, LiveExpr};

fn simplify_extracted_conjunction(exprs: Vec<LiveExpr>) -> LiveExpr {
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

fn push_unique_expr(out: &mut Vec<LiveExpr>, expr: &LiveExpr) {
    if !out.iter().any(|existing| existing.structurally_equal(expr)) {
        out.push(expr.clone());
    }
}

impl LiveExpr {
    /// Get the level of this expression
    pub fn level(&self) -> ExprLevel {
        match self {
            LiveExpr::Bool(_) => ExprLevel::Constant,
            LiveExpr::StatePred { .. } => ExprLevel::State,
            LiveExpr::ActionPred { .. } => ExprLevel::Action,
            LiveExpr::Enabled { .. } => ExprLevel::State,
            LiveExpr::StateChanged { .. } => ExprLevel::Action,
            LiveExpr::Not(expr) => expr.level(),
            LiveExpr::And(exprs) | LiveExpr::Or(exprs) => exprs
                .iter()
                .map(LiveExpr::level)
                .max()
                .unwrap_or(ExprLevel::Constant),
            LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => {
                ExprLevel::Temporal
            }
        }
    }

    /// Check if this expression contains any action-level subexpressions
    pub fn contains_action(&self) -> bool {
        match self {
            LiveExpr::Bool(_) | LiveExpr::StatePred { .. } | LiveExpr::Enabled { .. } => false,
            LiveExpr::ActionPred { .. } | LiveExpr::StateChanged { .. } => true,
            LiveExpr::Not(expr) => expr.contains_action(),
            LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
                exprs.iter().any(LiveExpr::contains_action)
            }
            LiveExpr::Always(expr) | LiveExpr::Eventually(expr) | LiveExpr::Next(expr) => {
                expr.contains_action()
            }
        }
    }

    /// Check if this expression is in positive normal form
    /// (negation only applied to atoms)
    pub fn is_positive_form(&self) -> bool {
        match self {
            LiveExpr::Bool(_)
            | LiveExpr::StatePred { .. }
            | LiveExpr::ActionPred { .. }
            | LiveExpr::Enabled { .. }
            | LiveExpr::StateChanged { .. } => true,
            LiveExpr::Not(inner) => matches!(
                inner.as_ref(),
                LiveExpr::Bool(_)
                    | LiveExpr::StatePred { .. }
                    | LiveExpr::ActionPred { .. }
                    | LiveExpr::Enabled { .. }
                    | LiveExpr::StateChanged { .. }
            ),
            LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
                exprs.iter().all(LiveExpr::is_positive_form)
            }
            LiveExpr::Always(expr) | LiveExpr::Eventually(expr) | LiveExpr::Next(expr) => {
                expr.is_positive_form()
            }
        }
    }

    /// Push negation down to atoms (convert to positive normal form)
    ///
    /// Uses the following rewriting rules (Manna & Pnueli, p. 452):
    /// - ~TRUE = FALSE
    /// - ~FALSE = TRUE
    /// - ~~P = P
    /// - ~(P /\ Q) = ~P \/ ~Q
    /// - ~(P \/ Q) = ~P /\ ~Q
    /// - ~[]P = <>~P
    /// - ~<>P = []~P
    /// - ~()P = ()~P  (next distributes over negation)
    pub fn push_negation(self) -> Self {
        self.push_neg_inner(false)
    }

    fn push_neg_inner(self, negate: bool) -> Self {
        if negate {
            match self {
                LiveExpr::Bool(value) => LiveExpr::Bool(!value),
                LiveExpr::StatePred { .. }
                | LiveExpr::ActionPred { .. }
                | LiveExpr::Enabled { .. }
                | LiveExpr::StateChanged { .. } => LiveExpr::Not(Box::new(self)),
                LiveExpr::Not(inner) => inner.push_neg_inner(false),
                LiveExpr::And(exprs) => LiveExpr::or(
                    exprs
                        .into_iter()
                        .map(|expr| expr.push_neg_inner(true))
                        .collect(),
                ),
                LiveExpr::Or(exprs) => LiveExpr::and(
                    exprs
                        .into_iter()
                        .map(|expr| expr.push_neg_inner(true))
                        .collect(),
                ),
                LiveExpr::Always(expr) => LiveExpr::Eventually(Box::new(expr.push_neg_inner(true))),
                LiveExpr::Eventually(expr) => LiveExpr::Always(Box::new(expr.push_neg_inner(true))),
                LiveExpr::Next(expr) => LiveExpr::Next(Box::new(expr.push_neg_inner(true))),
            }
        } else {
            match self {
                LiveExpr::Bool(_)
                | LiveExpr::StatePred { .. }
                | LiveExpr::ActionPred { .. }
                | LiveExpr::Enabled { .. }
                | LiveExpr::StateChanged { .. } => self,
                LiveExpr::Not(inner) => inner.push_neg_inner(true),
                LiveExpr::And(exprs) => LiveExpr::and(
                    exprs
                        .into_iter()
                        .map(|expr| expr.push_neg_inner(false))
                        .collect(),
                ),
                LiveExpr::Or(exprs) => LiveExpr::or(
                    exprs
                        .into_iter()
                        .map(|expr| expr.push_neg_inner(false))
                        .collect(),
                ),
                LiveExpr::Always(expr) => LiveExpr::Always(Box::new(expr.push_neg_inner(false))),
                LiveExpr::Eventually(expr) => {
                    LiveExpr::Eventually(Box::new(expr.push_neg_inner(false)))
                }
                LiveExpr::Next(expr) => LiveExpr::Next(Box::new(expr.push_neg_inner(false))),
            }
        }
    }

    /// Get the body if this is of the form []<>A (AE pattern - "always eventually")
    /// Returns None if not in this form
    pub fn get_ae_body(&self) -> Option<&LiveExpr> {
        if let LiveExpr::Always(inner) = self {
            if let LiveExpr::Eventually(body) = inner.as_ref() {
                return Some(body);
            }
        }
        None
    }

    /// Get the body if this is of the form <>[]A (EA pattern - "eventually always")
    /// Returns None if not in this form
    pub fn get_ea_body(&self) -> Option<&LiveExpr> {
        if let LiveExpr::Eventually(inner) = self {
            if let LiveExpr::Always(body) = inner.as_ref() {
                return Some(body);
            }
        }
        None
    }

    /// Check if this is a general temporal formula (not []<> or <>[] at top level)
    pub fn is_general_tf(&self) -> bool {
        self.get_ae_body().is_none() && self.get_ea_body().is_none()
    }

    /// Recursively extract nested []<> (AE) patterns from within this formula.
    ///
    /// For formulas like `<>(P /\ []<>Q)`, this extracts the `[]<>Q` pattern
    /// and returns the formula with that pattern replaced by `true`.
    ///
    /// Returns: `(extracted_ae_bodies, simplified_formula)`
    /// - `extracted_ae_bodies`: Bodies of all []<> patterns found (e.g., `Q`)
    /// - `simplified_formula`: The formula with []<> patterns replaced by true
    ///
    /// This enables proper handling of nested temporal patterns like TLC does:
    /// the []<> obligations are checked via AE constraints (infinitely often),
    /// while the remaining formula goes to the tableau.
    pub fn extract_nested_ae(&self) -> (Vec<LiveExpr>, LiveExpr) {
        let mut ae_bodies = Vec::new();
        let simplified = self.extract_nested_ae_inner(&mut ae_bodies);
        (ae_bodies, simplified)
    }

    fn extract_nested_ae_inner(&self, ae_bodies: &mut Vec<LiveExpr>) -> LiveExpr {
        match self {
            LiveExpr::Always(inner) => {
                if let LiveExpr::Eventually(body) = inner.as_ref() {
                    if body.level() != ExprLevel::Temporal {
                        push_unique_expr(ae_bodies, body.as_ref());
                        return LiveExpr::Bool(true);
                    }
                }
                LiveExpr::Always(Box::new(inner.extract_nested_ae_inner(ae_bodies)))
            }
            LiveExpr::Eventually(inner) => {
                LiveExpr::Eventually(Box::new(inner.extract_nested_ae_inner(ae_bodies)))
            }
            LiveExpr::Next(inner) => {
                LiveExpr::Next(Box::new(inner.extract_nested_ae_inner(ae_bodies)))
            }
            LiveExpr::Not(_) => self.clone(),
            LiveExpr::And(conjuncts) => simplify_extracted_conjunction(
                conjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ae_inner(ae_bodies))
                    .collect(),
            ),
            LiveExpr::Or(disjuncts) => LiveExpr::Or(
                disjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ae_inner(ae_bodies))
                    .collect(),
            ),
            LiveExpr::Bool(_)
            | LiveExpr::StatePred { .. }
            | LiveExpr::ActionPred { .. }
            | LiveExpr::Enabled { .. }
            | LiveExpr::StateChanged { .. } => self.clone(),
        }
    }

    /// Recursively extract []body patterns from within <> contexts.
    ///
    /// For formulas like `<>(P /\ []~Q)` (leads-to violations), this extracts
    /// the `[]~Q` pattern and returns the formula with that pattern replaced by `true`.
    ///
    /// Returns: `(extracted_ea_bodies, simplified_formula)`
    /// - `extracted_ea_bodies`: Bodies of all [] patterns found inside <> (e.g., `~Q`)
    /// - `simplified_formula`: The formula with [] patterns replaced by true
    ///
    /// NOTE: This method is #[cfg(test)] only. Nested EA extraction is intentionally
    /// NOT used in production. TLC only classifies direct <>[]body at the top level
    /// (Liveness.java:844-855). Nested <>(P /\ []Q) cannot be safely extracted as
    /// a global EA constraint because []Q is conditional on P, not global. See #1741.
    #[cfg(test)]
    pub fn extract_nested_ea(&self) -> (Vec<LiveExpr>, LiveExpr) {
        let mut ea_bodies = Vec::new();
        let simplified = self.extract_nested_ea_outer(&mut ea_bodies);
        (ea_bodies, simplified)
    }

    #[cfg(test)]
    fn extract_nested_ea_outer(&self, ea_bodies: &mut Vec<LiveExpr>) -> LiveExpr {
        match self {
            LiveExpr::Eventually(inner) => {
                if let LiveExpr::Always(body) = inner.as_ref() {
                    if body.level() != ExprLevel::Temporal {
                        push_unique_expr(ea_bodies, body.as_ref());
                        return LiveExpr::Bool(true);
                    }
                }
                LiveExpr::Eventually(Box::new(inner.extract_nested_ea_inner(ea_bodies)))
            }
            LiveExpr::Always(inner) => {
                LiveExpr::Always(Box::new(inner.extract_nested_ea_outer(ea_bodies)))
            }
            LiveExpr::Next(inner) => {
                LiveExpr::Next(Box::new(inner.extract_nested_ea_outer(ea_bodies)))
            }
            LiveExpr::Not(_) => self.clone(),
            LiveExpr::And(conjuncts) => simplify_extracted_conjunction(
                conjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ea_outer(ea_bodies))
                    .collect(),
            ),
            LiveExpr::Or(disjuncts) => LiveExpr::Or(
                disjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ea_outer(ea_bodies))
                    .collect(),
            ),
            LiveExpr::Bool(_)
            | LiveExpr::StatePred { .. }
            | LiveExpr::ActionPred { .. }
            | LiveExpr::Enabled { .. }
            | LiveExpr::StateChanged { .. } => self.clone(),
        }
    }

    #[cfg(test)]
    fn extract_nested_ea_inner(&self, ea_bodies: &mut Vec<LiveExpr>) -> LiveExpr {
        match self {
            LiveExpr::Always(body) => {
                if body.level() != ExprLevel::Temporal {
                    push_unique_expr(ea_bodies, body.as_ref());
                    return LiveExpr::Bool(true);
                }
                LiveExpr::Always(Box::new(body.extract_nested_ea_inner(ea_bodies)))
            }
            LiveExpr::Eventually(inner) => {
                LiveExpr::Eventually(Box::new(inner.extract_nested_ea_inner(ea_bodies)))
            }
            LiveExpr::Next(inner) => {
                LiveExpr::Next(Box::new(inner.extract_nested_ea_inner(ea_bodies)))
            }
            LiveExpr::Not(_) => self.clone(),
            LiveExpr::And(conjuncts) => simplify_extracted_conjunction(
                conjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ea_inner(ea_bodies))
                    .collect(),
            ),
            LiveExpr::Or(disjuncts) => LiveExpr::Or(
                disjuncts
                    .iter()
                    .map(|expr| expr.extract_nested_ea_inner(ea_bodies))
                    .collect(),
            ),
            LiveExpr::Bool(_)
            | LiveExpr::StatePred { .. }
            | LiveExpr::ActionPred { .. }
            | LiveExpr::Enabled { .. }
            | LiveExpr::StateChanged { .. } => self.clone(),
        }
    }

    /// Structural equality check (for tableau construction)
    pub fn structurally_equal(&self, other: &LiveExpr) -> bool {
        match (self, other) {
            (LiveExpr::Bool(lhs), LiveExpr::Bool(rhs)) => lhs == rhs,
            (LiveExpr::StatePred { tag: lhs, .. }, LiveExpr::StatePred { tag: rhs, .. }) => {
                lhs == rhs
            }
            (LiveExpr::ActionPred { tag: lhs, .. }, LiveExpr::ActionPred { tag: rhs, .. }) => {
                lhs == rhs
            }
            (LiveExpr::Enabled { tag: lhs, .. }, LiveExpr::Enabled { tag: rhs, .. }) => lhs == rhs,
            (LiveExpr::StateChanged { tag: lhs, .. }, LiveExpr::StateChanged { tag: rhs, .. }) => {
                lhs == rhs
            }
            (LiveExpr::Not(lhs), LiveExpr::Not(rhs)) => lhs.structurally_equal(rhs),
            (LiveExpr::And(lhs), LiveExpr::And(rhs)) if lhs.len() == rhs.len() => lhs
                .iter()
                .zip(rhs.iter())
                .all(|(left, right)| left.structurally_equal(right)),
            (LiveExpr::Or(lhs), LiveExpr::Or(rhs)) if lhs.len() == rhs.len() => lhs
                .iter()
                .zip(rhs.iter())
                .all(|(left, right)| left.structurally_equal(right)),
            (LiveExpr::Always(lhs), LiveExpr::Always(rhs))
            | (LiveExpr::Eventually(lhs), LiveExpr::Eventually(rhs))
            | (LiveExpr::Next(lhs), LiveExpr::Next(rhs)) => lhs.structurally_equal(rhs),
            _ => false,
        }
    }

    /// Extract all "promise" subformulas from this formula.
    ///
    /// In TLC terms, promises are all subformulas of the form `<>r`.
    /// The tableau acceptance check requires that each promise is fulfilled
    /// somewhere in a cycle.
    pub fn extract_promises(&self) -> Vec<LiveExpr> {
        fn collect_promises(expr: &LiveExpr, out: &mut Vec<LiveExpr>) {
            match expr {
                LiveExpr::Eventually(inner) => {
                    let promise = LiveExpr::Eventually(Box::new((**inner).clone()));
                    push_unique_expr(out, &promise);
                    collect_promises(inner, out);
                }
                LiveExpr::Not(inner) | LiveExpr::Always(inner) | LiveExpr::Next(inner) => {
                    collect_promises(inner, out);
                }
                LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
                    for expr in exprs {
                        collect_promises(expr, out);
                    }
                }
                LiveExpr::Bool(_)
                | LiveExpr::StatePred { .. }
                | LiveExpr::ActionPred { .. }
                | LiveExpr::Enabled { .. }
                | LiveExpr::StateChanged { .. } => {}
            }
        }

        let mut promises = Vec::new();
        collect_promises(self, &mut promises);
        promises
    }
}
