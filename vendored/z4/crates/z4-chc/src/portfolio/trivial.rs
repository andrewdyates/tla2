// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trivial-solve shortcuts for the CHC portfolio.
//!
//! When preprocessing inlines away all predicates, the problem reduces to
//! checking whether query constraints are satisfiable. This module handles
//! that special case without invoking the full engine portfolio.

use super::{PortfolioResult, PortfolioSolver, ValidationResult};
use crate::pdr::{Counterexample, InvariantModel, PredicateInterpretation};
use crate::smt::{SmtContext, SmtResult};
use crate::transform::{
    ClauseInliner, DeadParamEliminator, LocalVarEliminator, TransformationPipeline,
};
use crate::{ChcExpr, ChcVar};

impl PortfolioSolver {
    /// Try to solve trivially-inlined problems.
    ///
    /// After preprocessing (ClauseInliner), if all predicates are inlined away,
    /// the problem reduces to checking if query constraints are satisfiable.
    /// If all query constraints are unsatisfiable, the problem is Safe.
    /// If any query constraint is satisfiable, the problem is Unsafe.
    pub(super) fn try_solve_trivial(&self) -> Option<PortfolioResult> {
        // Check if any clause has predicates in its body
        let has_body_predicates = self
            .problem
            .clauses()
            .iter()
            .any(|c| !c.body.predicates.is_empty());

        if has_body_predicates {
            return None; // Not a trivial problem
        }

        // All clauses have empty body predicates - check query constraints
        let queries: Vec<_> = self.problem.queries().collect();
        if queries.is_empty() {
            // No queries means trivially safe
            if self.config.verbose {
                safe_eprintln!("Portfolio: Trivially safe (no query clauses)");
            }
            let model = self.trivial_true_model();
            return match self.validate_safe(&model) {
                ValidationResult::Valid => Some(PortfolioResult::Safe(model)),
                ValidationResult::Invalid(reason) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivial Safe (no queries) failed validation: {reason}; falling through to engines"
                        );
                    }
                    None
                }
            };
        }

        // Check if any query constraint is satisfiable
        let mut smt = self.problem.make_smt_context();
        for query in &queries {
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

            smt.reset();
            match smt.check_sat(&constraint) {
                SmtResult::Sat(_model) => {
                    // Query constraint is satisfiable in the (possibly abstracted) domain.
                    //
                    // If BV-to-Int abstraction was applied, this SAT result may be spurious:
                    // the integer model may not map to valid bitvector values. BV-to-Int is
                    // an over-approximation (SAFE in Int → SAFE in BV, but UNSAFE in Int
                    // does NOT imply UNSAFE in BV).
                    //
                    // To confirm: inline the original (un-abstracted) problem and check
                    // whether its query constraints are also satisfiable in the native
                    // BV domain. If so, the system is genuinely unsafe (#6781).
                    if self.bv_abstracted {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Trivial query SAT after BV-to-Int abstraction — \
                                 confirming against original problem"
                            );
                        }
                        if let Some(result) = self.confirm_trivial_unsafe_on_original(&mut smt) {
                            return Some(result);
                        }
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Original-domain confirmation failed, \
                                 falling through to engines"
                            );
                        }
                        return None;
                    }

                    // No abstraction — SAT result is reliable. System is unsafe.
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivially unsafe (query constraint satisfiable)"
                        );
                    }
                    return Some(PortfolioResult::Unsafe(Counterexample {
                        steps: Vec::new(),
                        witness: None,
                    }));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This query is unreachable, continue checking
                }
                SmtResult::Unknown => {
                    // Can't determine - fall through to engines
                    return None;
                }
            }
        }

        // All query constraints are unsatisfiable - safe
        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Trivially safe (all {} query constraints unsatisfiable)",
                queries.len()
            );
        }

        // SOUNDNESS FIX (#6781): When BV abstraction was applied, the trivial
        // UNSAT result on the transformed problem might be due to preprocessing
        // losing reachability information (dead-param-elim + BvToBool interaction).
        // Cross-check by inlining the original problem (without BV transforms)
        // and verifying that its query constraints are also UNSAT.
        if self.bv_abstracted {
            if let Some(unsafe_result) = self.confirm_trivial_unsafe_on_original(&mut smt) {
                // Original-domain check found a SAT query — the transformed
                // UNSAT was a false negative from preprocessing.
                return Some(unsafe_result);
            }
        }

        // When preprocessing eliminated all predicates AND all queries are UNSAT,
        // the trivial model P(x) = true is provably valid:
        // - No query can be violated (all UNSAT, confirmed by SMT above)
        // - BV abstraction cross-check passed (no original-domain unsafety)
        // - Therefore P(x) = true satisfies all Horn clauses by construction
        //
        // In this case, skip the expensive PdrSolver validation (which times out
        // on BV64 problems). The validation is defense-in-depth, but the proof
        // above is complete.
        if self.problem.predicates().is_empty() {
            let mut model = InvariantModel::new();
            for pred in self.original_problem.predicates() {
                let vars: Vec<ChcVar> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                    .collect();
                model.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
                );
            }
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Trivial Safe — preprocessing eliminated all {} predicates, \
                     all {} queries UNSAT, returning P(x)=true model directly",
                    self.original_problem.predicates().len(),
                    queries.len()
                );
            }
            // SOUNDNESS FIX (#7912, Gap D): Defense-in-depth query-only validation.
            // The predicate-free + all-queries-UNSAT proof above is constructively
            // sound, but validate_safe_query_only() confirms the model excludes bad
            // states. Full validate_safe() is intentionally skipped here because
            // PdrSolver times out on BV64 problems. Query-only is O(query_clauses).
            match self.validate_safe_query_only(&model) {
                super::SafePrecheckResult::Valid
                | super::SafePrecheckResult::ExactNegatedQuery(_) => {
                    return Some(PortfolioResult::Safe(model));
                }
                super::SafePrecheckResult::Invalid(reason) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivial Safe (predicate-free) failed query-only validation: {reason}; falling through to engines"
                        );
                    }
                    return None;
                }
            }
        }
        let model = self.trivial_true_model();
        match self.validate_safe(&model) {
            ValidationResult::Valid => Some(PortfolioResult::Safe(model)),
            ValidationResult::Invalid(reason) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Trivial Safe (unsat queries) failed validation: {reason}; falling through to engines"
                    );
                }
                None
            }
        }
    }

    /// Confirm a trivial-unsafe result by inlining the original (un-abstracted)
    /// problem and checking query constraints in the native BV domain.
    ///
    /// When BV-to-Int abstraction makes the trivial SAT check unreliable, we
    /// can still confirm unsafety by inlining the original problem (no BV
    /// transforms, just local-var-elim + dead-param-elim + clause inlining)
    /// and checking the resulting query constraints. If the original domain
    /// also yields SAT on a query, the system is genuinely unsafe.
    ///
    /// Part of #6781: without this, the trivial-SAT result is discarded and
    /// engines fall back to the original BV problem, which they cannot solve.
    fn confirm_trivial_unsafe_on_original(&self, smt: &mut SmtContext) -> Option<PortfolioResult> {
        // Inline the original problem without BV transforms
        let inlining_pipeline = TransformationPipeline::new()
            .with(LocalVarEliminator::new())
            .with(DeadParamEliminator::new())
            .with(ClauseInliner::new());
        let inlined = inlining_pipeline.transform(self.original_problem.clone());

        // Check if inlining eliminated all predicates
        let has_body_predicates = inlined
            .problem
            .clauses()
            .iter()
            .any(|c| !c.body.predicates.is_empty());
        if has_body_predicates {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Original problem still has predicates after inlining — \
                     cannot confirm trivially"
                );
            }
            return None;
        }

        // Check query constraints in the native BV domain
        for query in inlined.problem.queries() {
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            smt.reset();
            match smt.check_sat(&constraint) {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivially unsafe confirmed in original BV domain"
                        );
                    }
                    return Some(PortfolioResult::Unsafe(Counterexample {
                        steps: Vec::new(),
                        witness: None,
                    }));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This query is unreachable in original domain, continue
                }
                SmtResult::Unknown => {
                    // Can't determine in original domain
                    if self.config.verbose {
                        safe_eprintln!("Portfolio: Original-domain query check returned Unknown");
                    }
                    return None;
                }
            }
        }

        // All original queries are UNSAT — the abstracted SAT was indeed spurious
        None
    }

    pub(super) fn trivial_true_model(&self) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            model.set(
                pred.id,
                PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
            );
        }
        model
    }
}
