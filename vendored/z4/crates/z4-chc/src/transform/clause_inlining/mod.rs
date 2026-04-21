// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause inlining transformation for CHC problems.
//!
//! This module implements clause inlining based on Eldarica's ClauseInliner.
//! It identifies non-recursive predicates with unique definitions and inlines
//! their bodies into clauses that use them, reducing the number of predicates.
//!
//! # Example
//!
//! Given:
//! ```text
//! Init(x) ⇐ true                    ; fact clause
//! Loop(x) ⇐ Init(x)                 ; single-use intermediate
//! Loop(x+1) ⇐ Loop(x), x < 10       ; self-loop
//! false ⇐ Loop(x), x ≥ 10           ; query
//! ```
//!
//! After inlining Init:
//! ```text
//! Loop(0) ⇐ true                    ; inlined: Init(0) → body of Init clause
//! Loop(x+1) ⇐ Loop(x), x < 10       ; unchanged
//! false ⇐ Loop(x), x ≥ 10           ; unchanged
//! ```
//!
//! # Reference
//!
//! Based on Eldarica: `reference/eldarica/src/main/scala/lazabs/horn/preprocessor/ClauseInliner.scala`

use crate::{ChcExpr, ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

mod back_translator;
mod clause_ops;
mod multi_def;

use back_translator::InliningBackTranslator;

use super::{TransformationResult, Transformer};

/// Global counter for fresh variable generation to avoid name collisions.
static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Generate a fresh variable name with the given prefix.
fn fresh_var_name(prefix: &str) -> String {
    let count = FRESH_COUNTER.fetch_add(1, Ordering::SeqCst);
    format!("{prefix}__inline_{count}")
}

/// Clause inlining preprocessor.
///
/// Inlines non-recursive predicates to reduce the number of predicates
/// in the CHC problem. Has two phases:
///
/// **Phase 1 (unique-definition):** Inlines predicates with exactly one
/// defining clause. This always reduces or preserves clause count.
///
/// **Phase 2 (multi-definition, Z3-style):** Inlines predicates with up to
/// `max_multi_defs` defining clauses, provided they appear in at most
/// `max_multi_tail_uses` tail positions across all clauses. This trades
/// clause count for predicate count: each use site expands to N clauses
/// (one per definition), but the predicate is eliminated.
///
/// Reference: Z3's `mk_rule_inliner` (`reference/z3/src/muz/transforms/dl_mk_rule_inliner.cpp`)
pub(crate) struct ClauseInliner {
    /// Maximum constraint size after inlining to prevent blowup.
    constraint_size_limit: usize,
    /// Maximum number of definitions for multi-def inlining (Z3 uses 4).
    max_multi_defs: usize,
    /// Maximum number of tail occurrences for multi-def inlining (Z3 uses 1).
    max_multi_tail_uses: usize,
    /// Enable verbose output.
    verbose: bool,
}

impl Default for ClauseInliner {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseInliner {
    /// Create a new clause inliner with default settings.
    pub(crate) fn new() -> Self {
        Self {
            constraint_size_limit: 10000,
            max_multi_defs: 8,
            max_multi_tail_uses: 2,
            verbose: false,
        }
    }

    /// Enable or disable verbose output.
    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Inline non-recursive clauses in the problem.
    ///
    /// Returns only the transformed problem (without back-translation info).
    /// Used by tests; production code uses `Transformer::transform` which
    /// also produces a back-translator.
    #[cfg(test)]
    pub(crate) fn inline(&self, problem: &ChcProblem) -> ChcProblem {
        self.inline_tracked(problem).0
    }

    /// Inline non-recursive clauses and return both the simplified problem
    /// and the defining clauses for each inlined predicate (for back-translation).
    /// Result of inlining: transformed problem, definitions for back-translation,
    /// and a mapping from new (compacted) predicate IDs to original IDs.
    fn inline_tracked(
        &self,
        problem: &ChcProblem,
    ) -> (
        ChcProblem,
        Vec<(PredicateId, HornClause)>,
        FxHashMap<PredicateId, PredicateId>,
    ) {
        let mut clauses: Vec<HornClause> = problem.clauses().to_vec();
        let mut inlined_defs: Vec<(PredicateId, HornClause)> = Vec::new();

        // Phase 1: Unique-definition inlining (Eldarica-style).
        self.inline_unique_defs(&mut clauses, &mut inlined_defs);

        // Phase 2: Multi-definition inlining (Z3-style).
        // Part of #6047: reduces 4-predicate z4_watched to 1 predicate (matching Z3).
        clauses = self.inline_multi_def(&clauses, &mut inlined_defs);

        // Phase 3: Compact predicates — remove eliminated predicates from declarations
        // and remap IDs so PDR doesn't waste time on ghost predicates.
        let (new_problem, new_to_old) = self.compact_predicates(problem, &mut clauses);
        (new_problem, inlined_defs, new_to_old)
    }

    /// Build a compacted `ChcProblem` containing only predicates still referenced
    /// in the remaining clauses. Returns the new problem and a new→old ID mapping.
    fn compact_predicates(
        &self,
        original: &ChcProblem,
        clauses: &mut Vec<HornClause>,
    ) -> (ChcProblem, FxHashMap<PredicateId, PredicateId>) {
        // Collect predicate IDs still referenced in clauses.
        let mut used: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in clauses.iter() {
            for (pid, _) in &clause.body.predicates {
                used.insert(*pid);
            }
            if let Some(pid) = clause.head.predicate_id() {
                used.insert(pid);
            }
        }

        let old_preds = original.predicates();
        let all_used = used.len() == old_preds.len();
        if all_used {
            // No predicates were eliminated — skip remapping.
            let mut new_problem = ChcProblem::new();
            for pred in old_preds {
                new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
            }
            for clause in clauses.drain(..) {
                new_problem.add_clause(clause);
            }
            return (new_problem, FxHashMap::default());
        }

        // Build old→new mapping for used predicates (preserving order).
        let mut old_to_new: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
        let mut new_to_old: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
        let mut new_problem = ChcProblem::new();
        for pred in old_preds {
            if used.contains(&pred.id) {
                let new_id = new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
                old_to_new.insert(pred.id, new_id);
                new_to_old.insert(new_id, pred.id);
            }
        }

        if self.verbose {
            let eliminated = old_preds.len() - used.len();
            eprintln!(
                "CHC inlining: compacted {0} -> {1} predicates ({eliminated} eliminated)",
                old_preds.len(),
                used.len(),
            );
        }

        // Remap predicate IDs in all clauses and add them.
        for clause in clauses.drain(..) {
            new_problem.add_clause(Self::remap_clause_preds(&clause, &old_to_new));
        }
        (new_problem, new_to_old)
    }

    /// Remap predicate IDs in a clause using the given mapping.
    fn remap_clause_preds(
        clause: &HornClause,
        mapping: &FxHashMap<PredicateId, PredicateId>,
    ) -> HornClause {
        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let new_pid = mapping.get(pid).copied().unwrap_or(*pid);
                (new_pid, args.clone())
            })
            .collect();
        let new_body = ClauseBody::new(new_body_preds, clause.body.constraint.clone());
        let new_head = match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                let new_pid = mapping.get(pid).copied().unwrap_or(*pid);
                ClauseHead::Predicate(new_pid, args.clone())
            }
            ClauseHead::False => ClauseHead::False,
        };
        HornClause::new(new_body, new_head)
    }

    /// Phase 1: iteratively inline predicates with unique (single) definitions.
    fn inline_unique_defs(
        &self,
        clauses: &mut Vec<HornClause>,
        inlined_defs: &mut Vec<(PredicateId, HornClause)>,
    ) {
        let mut iteration = 0;
        loop {
            iteration += 1;
            let unique_def_indices = self.find_unique_def_indices(clauses);
            if unique_def_indices.is_empty() {
                break;
            }
            let final_def_indices = self.extract_acyclic_def_indices(clauses, unique_def_indices);
            if final_def_indices.is_empty() {
                break;
            }

            let final_defs: FxHashMap<PredicateId, HornClause> = final_def_indices
                .iter()
                .map(|(&pred_id, &clause_idx)| (pred_id, clauses[clause_idx].clone()))
                .collect();

            if self.verbose {
                let inlined_preds: Vec<_> =
                    final_defs.keys().map(|id| format!("P{}", id.0)).collect();
                safe_eprintln!(
                    "CHC inlining iteration {}: inlining {} predicates: {:?}",
                    iteration,
                    final_defs.len(),
                    inlined_preds
                );
            }

            // Record inlined definitions for back-translation. Normalize complex
            // head args to plain variables (#5295).
            for (&pred_id, clause) in &final_defs {
                let normalized = Self::normalize_head_for_back_translation(clause);
                inlined_defs.push((pred_id, normalized));
            }

            // Remove defining clauses and apply inlining to remaining clauses.
            let inlined_heads: FxHashSet<PredicateId> = final_defs.keys().copied().collect();
            clauses.retain(|c| {
                c.head
                    .predicate_id()
                    .map_or(true, |h| !inlined_heads.contains(&h))
            });
            *clauses = clauses
                .iter()
                .map(|c| self.apply_defs(c, &final_defs))
                .collect();
        }
    }

    /// Find predicates with unique definitions (returns clause indices).
    ///
    /// A predicate P is uniquely defined if:
    /// 1. P appears in the head of exactly one clause
    /// 2. That clause has at most one body predicate (not self-recursive)
    /// 3. P is not FALSE (never inline the query head)
    fn find_unique_def_indices(&self, clauses: &[HornClause]) -> FxHashMap<PredicateId, usize> {
        let mut defs: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut blocked: FxHashSet<PredicateId> = FxHashSet::default();

        for (idx, clause) in clauses.iter().enumerate() {
            let Some(head_pred) = clause.head.predicate_id() else {
                // Query clause (head is false) - skip
                continue;
            };

            if blocked.contains(&head_pred) {
                continue;
            }

            // Check if this clause is suitable for inlining
            let is_self_recursive = clause
                .body
                .predicates
                .iter()
                .any(|(id, _)| *id == head_pred);

            let has_multiple_body_preds = clause.body.predicates.len() > 1;

            if defs.contains_key(&head_pred) || has_multiple_body_preds || is_self_recursive {
                // Multiple definitions, or unsuitable clause - block this predicate
                if self.verbose {
                    let reason = if is_self_recursive {
                        "self_recursive"
                    } else if defs.contains_key(&head_pred) {
                        "multiple_definitions"
                    } else {
                        "multiple_body_preds"
                    };
                    safe_eprintln!("CHC inlining: blocking P{} ({})", head_pred.0, reason);
                }
                blocked.insert(head_pred);
                defs.remove(&head_pred);
            } else {
                // First (and potentially only) suitable definition
                defs.insert(head_pred, idx);
            }
        }

        // Filter out predicates whose definitions exceed size limits
        defs.retain(|_, &mut idx| {
            let clause = &clauses[idx];
            let constraint_size = clause.body.constraint.as_ref().map_or(0, Self::expr_size);
            constraint_size <= self.constraint_size_limit
        });

        if self.verbose {
            safe_eprintln!(
                "CHC inlining: {} clauses, {} predicates, {} candidates after filtering",
                clauses.len(),
                blocked.len() + defs.len(),
                defs.len()
            );
        }

        defs
    }

    /// Extract acyclic subset of definitions (using clause indices).
    ///
    /// Removes predicates that form cycles in their definitions to prevent
    /// infinite expansion during inlining.
    ///
    /// The algorithm proceeds bottom-up: first inline predicates whose body
    /// predicates are all non-candidates (leaf definitions), then inline
    /// predicates whose body predicates have already been inlined, and repeat.
    fn extract_acyclic_def_indices(
        &self,
        clauses: &[HornClause],
        unique_defs: FxHashMap<PredicateId, usize>,
    ) -> FxHashMap<PredicateId, usize> {
        let candidate_preds: FxHashSet<PredicateId> = unique_defs.keys().copied().collect();
        let mut remaining = unique_defs;
        let mut final_defs: FxHashMap<PredicateId, usize> = FxHashMap::default();

        let mut iterations = 0;
        let max_iterations = remaining.len() + 1; // Prevent infinite loop

        while !remaining.is_empty() && iterations < max_iterations {
            iterations += 1;

            // Find predicates whose body predicates are all either:
            // - Not candidates at all (external predicates)
            // - Already in final_defs (already scheduled for inlining)
            let can_inline: FxHashMap<PredicateId, usize> = remaining
                .iter()
                .filter(|(_, &idx)| {
                    let clause = &clauses[idx];
                    clause.body.predicates.iter().all(|(body_pred, _)| {
                        // Body pred is safe if it's not a candidate or already inlined
                        !candidate_preds.contains(body_pred) || final_defs.contains_key(body_pred)
                    })
                })
                .map(|(&p, &idx)| (p, idx))
                .collect();

            if can_inline.is_empty() {
                // All remaining predicates depend on other remaining predicates - cycle detected
                // Break the cycle by removing one predicate
                if let Some(cycle_breaker) = self.find_cycle_breaker_indices(clauses, &remaining) {
                    remaining.remove(&cycle_breaker);
                } else {
                    // No cycle breaker found, stop
                    break;
                }
            } else {
                // Remove can_inline from remaining and add to final_defs
                for pred in can_inline.keys() {
                    remaining.remove(pred);
                }
                final_defs.extend(can_inline);
            }
        }

        final_defs
    }

    /// Find a predicate to remove to break a cycle (using indices).
    ///
    /// Chooses a predicate that appears both as head and body in the remaining set.
    fn find_cycle_breaker_indices(
        &self,
        clauses: &[HornClause],
        remaining: &FxHashMap<PredicateId, usize>,
    ) -> Option<PredicateId> {
        let heads: FxHashSet<PredicateId> = remaining.keys().copied().collect();

        // Sort for deterministic cycle-breaker selection (#3060)
        let mut sorted_remaining: Vec<_> = remaining.iter().collect();
        sorted_remaining.sort_unstable_by_key(|(pid, _)| pid.index());
        for (_, &idx) in &sorted_remaining {
            let clause = &clauses[idx];
            for (body_pred, _) in &clause.body.predicates {
                if heads.contains(body_pred) {
                    return Some(*body_pred);
                }
            }
        }

        // Fallback: pick the smallest-index predicate for determinism
        sorted_remaining.first().map(|(pid, _)| **pid)
    }
}

impl Transformer for ClauseInliner {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let (new_problem, inlined_defs, new_to_old) = self.inline_tracked(&problem);
        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(InliningBackTranslator {
                inlined_defs,
                new_to_old,
            }),
        }
    }
}

#[cfg(test)]
mod tests;
