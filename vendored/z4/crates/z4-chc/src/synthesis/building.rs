// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate building and verification for structural invariant synthesis.
//!
//! Builds candidate invariant expressions from detected loop patterns and
//! verifies them against all CHC clauses via SMT solving.

use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcVar, ClauseHead, PredicateId};
use rustc_hash::FxHashMap;

use super::types::{LoopPattern, SynthesisPattern};
use super::StructuralSynthesizer;

impl<'a> StructuralSynthesizer<'a> {
    /// Build candidate invariant from detected patterns.
    pub(super) fn build_candidate(
        &self,
        patterns: &[LoopPattern],
    ) -> FxHashMap<PredicateId, ChcExpr> {
        let mut candidate = FxHashMap::default();

        if patterns.is_empty() {
            return candidate;
        }

        // For multi-predicate SCCs, using per-predicate init bounds can produce
        // non-inductive candidates (e.g., one predicate has an init fact but others do not).
        // Compute SCC-wide init bounds and apply them consistently.
        let scc_info = crate::pdr::scc::tarjan_scc(self.problem);
        let mut scc_min_init: FxHashMap<(usize, usize), i64> = FxHashMap::default();
        let mut scc_max_init: FxHashMap<(usize, usize), i64> = FxHashMap::default();

        for pattern in patterns {
            let Some(init) = pattern.init_value else {
                continue;
            };
            let Some(scc_id) = scc_info.predicate_to_scc.get(&pattern.pred_id) else {
                continue;
            };
            let key = (*scc_id, pattern.var_index);
            scc_min_init
                .entry(key)
                .and_modify(|v| *v = (*v).min(init))
                .or_insert(init);
            scc_max_init
                .entry(key)
                .and_modify(|v| *v = (*v).max(init))
                .or_insert(init);
        }

        // Group conjuncts by predicate ID (currently all patterns have the same pred_id,
        // but this design supports future extension to multi-predicate problems)
        let mut conjuncts_by_pred: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        for pattern in patterns {
            let conjuncts = conjuncts_by_pred.entry(pattern.pred_id).or_default();
            let scc_id = scc_info.predicate_to_scc.get(&pattern.pred_id).copied();
            let scc_min_init_value = scc_id
                .and_then(|id| scc_min_init.get(&(id, pattern.var_index)))
                .copied();
            let scc_max_init_value = scc_id
                .and_then(|id| scc_max_init.get(&(id, pattern.var_index)))
                .copied();
            match pattern.pattern {
                SynthesisPattern::BoundedIncrement => {
                    // Invariant: x <= upper_bound + stride
                    // The guard (x < N) allows transitions when x = N-1, producing x = N-1+stride.
                    // The upper_bound extracted from guard already has -1 applied for strict <,
                    // so we add stride to get the actual maximum post-transition value.
                    if let Some(upper) = pattern.upper_bound {
                        let adjusted_upper = upper.saturating_add(pattern.stride);
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(adjusted_upper),
                        ));
                    }
                    // Also add lower bound from SCC-wide init if available
                    if let Some(init) = scc_min_init_value {
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(init),
                        ));
                    }
                }
                SynthesisPattern::BoundedDecrement => {
                    // Invariant: x >= lower_bound + stride (stride is negative for decrement)
                    // The guard (x > L) allows transitions when x = L+1, producing x = L+1+stride.
                    // Since stride is negative, this gives the actual minimum post-transition value.
                    if let Some(lower) = pattern.lower_bound {
                        let adjusted_lower = lower.saturating_add(pattern.stride);
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(adjusted_lower),
                        ));
                    }
                    // Also add upper bound from SCC-wide init if available
                    if let Some(init) = scc_max_init_value {
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(init),
                        ));
                    }
                }
                SynthesisPattern::IntervalBounds => {
                    // Just use init and guard bounds
                    if let Some(init) = if pattern.stride > 0 {
                        scc_min_init_value
                    } else {
                        scc_max_init_value
                    } {
                        if pattern.stride > 0 {
                            conjuncts.push(ChcExpr::ge(
                                ChcExpr::var(pattern.var.clone()),
                                ChcExpr::int(init),
                            ));
                        } else {
                            conjuncts.push(ChcExpr::le(
                                ChcExpr::var(pattern.var.clone()),
                                ChcExpr::int(init),
                            ));
                        }
                    }
                    if let Some(lower) = pattern.lower_bound {
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(lower),
                        ));
                    }
                    if let Some(upper) = pattern.upper_bound {
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(upper),
                        ));
                    }
                }
            }
        }

        // Build candidate invariants for each predicate
        for (pred_id, conjuncts) in conjuncts_by_pred {
            if !conjuncts.is_empty() {
                candidate.insert(pred_id, ChcExpr::and_vec(conjuncts));
            }
        }

        candidate
    }

    /// Verify that the candidate invariant is inductive.
    ///
    /// Checks each clause: body_with_inv => head_with_inv
    pub(super) fn verify_inductive(&self, candidate: &FxHashMap<PredicateId, ChcExpr>) -> bool {
        let mut smt = SmtContext::new();

        // Check each clause
        for clause in self.problem.clauses() {
            // Substitute predicates with candidate invariants
            let body_with_inv = self.substitute_predicates_in_body(clause, candidate);
            let head_with_inv = self.substitute_predicate_in_head(clause, candidate);

            // Check: body_with_inv => head_with_inv is valid
            // Equivalent to: body_with_inv AND NOT(head_with_inv) is UNSAT
            let negated_implication = ChcExpr::and(body_with_inv, ChcExpr::not(head_with_inv));

            // Reset SMT context between checks to avoid accumulated state
            smt.reset();
            let result = smt.check_sat(&negated_implication);

            match result {
                SmtResult::Sat(_) => {
                    // Counterexample found - invariant not inductive for this clause
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Good - this clause is satisfied
                    continue;
                }
                SmtResult::Unknown => {
                    // Can't verify - assume not inductive
                    return false;
                }
            }
        }

        true
    }

    /// Substitute predicates in clause body with invariant expressions.
    fn substitute_predicates_in_body(
        &self,
        clause: &crate::HornClause,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> ChcExpr {
        let mut conjuncts = Vec::new();

        // Add constraint
        if let Some(constraint) = &clause.body.constraint {
            conjuncts.push(constraint.clone());
        }

        // Substitute each predicate with its interpretation
        for (pred_id, args) in &clause.body.predicates {
            if let Some(inv) = candidate.get(pred_id) {
                // Build substitution from canonical vars to actual args using actual sorts
                let Some(pred) = self.problem.get_predicate(*pred_id) else {
                    continue;
                };
                let substitution: Vec<(ChcVar, ChcExpr)> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .zip(args.iter())
                    .map(|((i, sort), arg)| {
                        let canonical_var = ChcVar::new(format!("x{i}"), sort.clone());
                        (canonical_var, arg.clone())
                    })
                    .collect();
                conjuncts.push(inv.substitute(&substitution));
            }
        }

        ChcExpr::and_vec(conjuncts)
    }

    /// Substitute predicate in clause head with invariant expression.
    fn substitute_predicate_in_head(
        &self,
        clause: &crate::HornClause,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> ChcExpr {
        match &clause.head {
            ClauseHead::False => ChcExpr::Bool(false),
            ClauseHead::Predicate(pred_id, args) => {
                if let Some(inv) = candidate.get(pred_id) {
                    let Some(pred) = self.problem.get_predicate(*pred_id) else {
                        return ChcExpr::Bool(true);
                    };
                    let substitution: Vec<(ChcVar, ChcExpr)> = pred
                        .arg_sorts
                        .iter()
                        .enumerate()
                        .zip(args.iter())
                        .map(|((i, sort), arg)| {
                            let canonical_var = ChcVar::new(format!("x{i}"), sort.clone());
                            (canonical_var, arg.clone())
                        })
                        .collect();
                    inv.substitute(&substitution)
                } else {
                    ChcExpr::Bool(true)
                }
            }
        }
    }
}
