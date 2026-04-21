// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formula decomposition and PEM planning for liveness checking.
//!
//! Implements DNF decomposition and AE/EA classification of temporal formulas,
//! following TLC's `Liveness.processLiveness` and `OrderOfSolution` approach.

use super::{GroupedLivenessPlan, LiveExpr, LivenessChecker, PemPlan};
#[cfg(test)]
use super::{LivenessConstraints, Tableau};
#[cfg(test)]
use crate::eval::EvalCtx;

/// Errors from decomposing liveness formulas into checker plans.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum LivenessDecompError {
    /// DNF expansion exceeded the clause count limit.
    #[error("DNF clause count exceeded limit (estimated clauses: {estimated}, limit: {limit})")]
    DnfOverflow { estimated: usize, limit: usize },

    /// A `<>[]` (EA) body has temporal level, which is unsupported.
    #[error("unsupported <>[] body: {formula}")]
    UnsupportedEaBody { formula: String },

    /// A `[]<>` (AE) body has temporal level, which is unsupported.
    #[error("unsupported []<> body: {formula}")]
    UnsupportedAeBody { formula: String },

    /// A temporal formula contains actions in an unsupported form (not `<>[]A` or `[]<>A`).
    #[error(
        "temporal formulas containing actions must be of the form <>[]A or []<>A, \
         found unsupported form: {formula}"
    )]
    UnsupportedActionFormula { formula: String },

    /// `extract_nested_ae` produced a body at temporal level (internal invariant violation).
    #[error("extract_nested_ae produced temporal-level body: {formula}")]
    NestedAeTemporalBody { formula: String },
}

impl LivenessChecker {
    /// Decompose a (negated) liveness formula into one checker per DNF clause.
    ///
    /// This implements the same high-level approach as TLC's
    /// `Liveness.processLiveness`: convert to DNF and classify each conjunct into:
    /// - `<>[]A` (EA action checks)
    /// - `[]<>S` (AE state checks)
    /// - `[]<>A` (AE action checks)
    /// - remaining general temporal formulas (tableau `tf`)
    #[cfg(test)]
    pub fn from_formula(
        formula: &LiveExpr,
        ctx: EvalCtx,
    ) -> Result<Vec<Self>, LivenessDecompError> {
        fn push_unique(list: &mut Vec<LiveExpr>, expr: &LiveExpr) {
            if !list.iter().any(|e| e.structurally_equal(expr)) {
                list.push(expr.clone());
            }
        }

        let clauses =
            formula
                .to_dnf_clauses()
                .map_err(|count| LivenessDecompError::DnfOverflow {
                    estimated: count,
                    limit: LiveExpr::MAX_DNF_CLAUSES,
                })?;
        let mut out = Vec::new();

        for clause in clauses {
            let mut constraints = LivenessConstraints::default();
            let mut tf_terms = Vec::new();

            for term in &clause {
                if let Some(body) = term.get_ea_body() {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut constraints.ea_state, body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut constraints.ea_action, body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::UnsupportedEaBody {
                                formula: term.to_string(),
                            });
                        }
                    }
                    continue;
                }

                if let Some(body) = term.get_ae_body() {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut constraints.ae_state, body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut constraints.ae_action, body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::UnsupportedAeBody {
                                formula: term.to_string(),
                            });
                        }
                    }
                    continue;
                }

                // TLC rejects temporal formulas containing actions unless they are
                // in <>[]A (EA) or []<>A (AE) form. Bare <>Action is invalid because
                // the tableau construction (Manna & Pnueli) is for pure LTL without
                // actions. Previously we misclassified <>Action as ea_action (<>[]Action),
                // which over-filtered SCC edges and caused false negatives (#1515).
                if term.contains_action() {
                    return Err(LivenessDecompError::UnsupportedActionFormula {
                        formula: term.to_string(),
                    });
                }

                // Extract nested []<> (AE) patterns from within the term.
                // NOTE: Nested EA extraction (<>[] patterns inside larger temporal formulas)
                // is intentionally NOT performed. See #1741: TLC only classifies direct
                // <>[]body at the top level (Liveness.java:844-855). Nested <>(P /\ []Q)
                // must remain in the tableau because []Q is conditional on P becoming true,
                // not a global EA constraint that can filter all edges.
                let (ae_bodies, simplified_term) = term.extract_nested_ae();

                // Add extracted AE bodies to constraints
                for body in ae_bodies {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut constraints.ae_state, &body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut constraints.ae_action, &body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::NestedAeTemporalBody {
                                formula: body.to_string(),
                            });
                        }
                    }
                }

                // Add the simplified term (with nested patterns replaced by true)
                // Skip if the term simplified to just true
                if !matches!(simplified_term, LiveExpr::Bool(true)) {
                    tf_terms.push(simplified_term);
                }
            }

            let tf = LiveExpr::and(tf_terms);
            let tableau = Tableau::new(tf);
            out.push(LivenessChecker::new_with_constraints(
                tableau,
                ctx.clone(),
                constraints,
            ));
        }

        Ok(out)
    }

    /// Decompose a (negated) liveness formula into grouped plans (TLC-style).
    ///
    /// Groups clauses by syntactically equivalent temporal formula (`tf`).
    /// Reduces checker count from O(DNF clauses) to O(unique tf groups).
    pub(crate) fn from_formula_grouped(
        formula: &LiveExpr,
    ) -> Result<Vec<GroupedLivenessPlan>, LivenessDecompError> {
        fn push_unique(list: &mut Vec<LiveExpr>, expr: &LiveExpr) {
            if !list.iter().any(|e| e.structurally_equal(expr)) {
                list.push(expr.clone());
            }
        }

        fn add_to_bin(bin: &mut Vec<LiveExpr>, expr: &LiveExpr) -> usize {
            for (idx, existing) in bin.iter().enumerate() {
                if existing.structurally_equal(expr) {
                    return idx;
                }
            }
            let idx = bin.len();
            bin.push(expr.clone());
            idx
        }

        struct ClausePemTmp {
            ea_state: Vec<LiveExpr>,
            ea_action: Vec<LiveExpr>,
            ae_state: Vec<LiveExpr>,
            ae_action: Vec<LiveExpr>,
            tf: LiveExpr,
        }

        let clauses =
            formula
                .to_dnf_clauses()
                .map_err(|count| LivenessDecompError::DnfOverflow {
                    estimated: count,
                    limit: LiveExpr::MAX_DNF_CLAUSES,
                })?;
        let mut clause_pems: Vec<ClausePemTmp> = Vec::with_capacity(clauses.len());

        for clause in clauses {
            let mut ea_state = Vec::new();
            let mut ea_action = Vec::new();
            let mut ae_state = Vec::new();
            let mut ae_action = Vec::new();
            let mut tf_terms = Vec::new();

            for term in &clause {
                if let Some(body) = term.get_ea_body() {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut ea_state, body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut ea_action, body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::UnsupportedEaBody {
                                formula: term.to_string(),
                            });
                        }
                    }
                    continue;
                }

                if let Some(body) = term.get_ae_body() {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut ae_state, body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut ae_action, body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::UnsupportedAeBody {
                                formula: term.to_string(),
                            });
                        }
                    }
                    continue;
                }

                // TLC rejects temporal formulas containing actions unless they are
                // in <>[]A (EA) or []<>A (AE) form (#1515).
                if term.contains_action() {
                    return Err(LivenessDecompError::UnsupportedActionFormula {
                        formula: term.to_string(),
                    });
                }

                let (ae_bodies, simplified_term) = term.extract_nested_ae();
                for body in ae_bodies {
                    match body.level() {
                        super::live_expr::ExprLevel::Constant
                        | super::live_expr::ExprLevel::State => {
                            push_unique(&mut ae_state, &body);
                        }
                        super::live_expr::ExprLevel::Action => {
                            push_unique(&mut ae_action, &body);
                        }
                        super::live_expr::ExprLevel::Temporal => {
                            return Err(LivenessDecompError::NestedAeTemporalBody {
                                formula: body.to_string(),
                            });
                        }
                    }
                }

                if !matches!(simplified_term, LiveExpr::Bool(true)) {
                    tf_terms.push(simplified_term);
                }
            }

            let tf = LiveExpr::and(tf_terms);
            clause_pems.push(ClausePemTmp {
                ea_state,
                ea_action,
                ae_state,
                ae_action,
                tf,
            });
        }

        // Group clauses by syntactic tf equality (TLC's tfbin/pembin)
        let mut tf_bin: Vec<LiveExpr> = Vec::new();
        let mut pem_bin: Vec<Vec<usize>> = Vec::new();

        for (i, cpem) in clause_pems.iter().enumerate() {
            let mut found = None;
            for (j, existing_tf) in tf_bin.iter().enumerate() {
                if existing_tf.structurally_equal(&cpem.tf) {
                    found = Some(j);
                    break;
                }
            }
            match found {
                Some(j) => pem_bin[j].push(i),
                None => {
                    tf_bin.push(cpem.tf.clone());
                    pem_bin.push(vec![i]);
                }
            }
        }

        // Build GroupedLivenessPlan for each tf group
        let mut plans: Vec<GroupedLivenessPlan> = Vec::with_capacity(tf_bin.len());

        for (group_idx, tf) in tf_bin.into_iter().enumerate() {
            let mut check_state: Vec<LiveExpr> = Vec::new();
            let mut check_action: Vec<LiveExpr> = Vec::new();
            let mut pems: Vec<PemPlan> = Vec::new();

            for &clause_idx in &pem_bin[group_idx] {
                let cpem = &clause_pems[clause_idx];
                let ea_action_idx: Vec<usize> = cpem
                    .ea_action
                    .iter()
                    .map(|e| add_to_bin(&mut check_action, e))
                    .collect();
                let ea_state_idx: Vec<usize> = cpem
                    .ea_state
                    .iter()
                    .map(|e| add_to_bin(&mut check_state, e))
                    .collect();
                let ae_state_idx: Vec<usize> = cpem
                    .ae_state
                    .iter()
                    .map(|e| add_to_bin(&mut check_state, e))
                    .collect();
                let ae_action_idx: Vec<usize> = cpem
                    .ae_action
                    .iter()
                    .map(|e| add_to_bin(&mut check_action, e))
                    .collect();

                pems.push(PemPlan {
                    ea_action_idx,
                    ea_state_idx,
                    ae_state_idx,
                    ae_action_idx,
                });
            }

            debug_assert!(!pems.is_empty(), "grouped plan must have at least one PEM");
            plans.push(GroupedLivenessPlan {
                tf,
                check_state,
                check_action,
                pems,
            });
        }

        Ok(plans)
    }
}
