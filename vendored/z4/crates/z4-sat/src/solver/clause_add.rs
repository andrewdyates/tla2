// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause addition and management methods for the SAT solver.
//!
//! Includes: empty clause handling (mark_empty_clause*), clause addition
//! (add_clause*, add_theory_lemma, add_theory_propagation), watch literal
//! reordering, clause DB internals, factor candidate marking, and
//! solution-witness checking on clause changes.

use super::*;

impl Solver {
    /// Mark that an empty clause was derived (UNSAT), with optional LRAT
    /// resolution hints.
    ///
    /// Callers that have resolution chain data (e.g. `record_level0_conflict_chain`)
    /// pass the chain as `hints` so the LRAT proof entry includes the derivation.
    /// Most callers pass `&[]` (no hints available).
    ///
    /// This also records the empty clause to the trace if enabled.
    #[inline]
    pub(super) fn mark_empty_clause_with_hints(&mut self, hints: &[u64]) {
        self.mark_empty_clause_with_hints_and_trace(hints, Vec::new());
    }

    /// Mark empty clause with both LRAT proof hints and clause-trace resolution
    /// hints attached atomically (#4435).
    pub(super) fn mark_empty_clause_with_hints_and_trace(
        &mut self,
        hints: &[u64],
        trace_hints: Vec<u64>,
    ) {
        // Solution-guided debugging (#4615): if a known satisfying assignment
        // exists, deriving the empty clause is a soundness bug. CaDiCaL parity:
        // check_no_solution_after_learning_empty_clause.
        assert!(
            self.cold.solution_witness.is_none(),
            "BUG: derived empty clause (UNSAT) but a satisfying assignment was \
             configured via set_solution — solver incorrectly claims unsatisfiable"
        );

        let first_empty_clause = !self.has_empty_clause;
        // Only record the scope depth on the first occurrence; a base-level
        // empty clause (depth 0) must never be overwritten by a scoped one.
        if first_empty_clause {
            self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
        }
        self.has_empty_clause = true;

        // Write empty clause to proof writer and allocate LRAT ID atomically.
        // Guard: only on the first derivation — repeated calls must NOT
        // advance next_clause_id (Fix 1 of #4475: ID drift on repeated calls).
        if !self.cold.empty_clause_in_proof {
            let proof_steps_before = self
                .proof_manager
                .as_ref()
                .map_or(0, ProofManager::added_count);
            // proof_emit_add handles both forward checking (#4483) and proof
            // emission, satisfying the single-authority contract (#4564).
            // For LRAT mode, proof_emit_add also prepends level-0 unit proof
            // IDs (#7108). This is safe even when the caller already includes
            // level-0 IDs because the hint chain deduplicates.
            let proof_clause_id = match self.proof_emit_add(&[], hints, ProofAddKind::Derived) {
                Ok(id) if id != 0 => Some(id),
                _ => None,
            };
            let proof_steps_after = self
                .proof_manager
                .as_ref()
                .map_or(proof_steps_before, ProofManager::added_count);
            if proof_steps_after > proof_steps_before {
                self.cold.empty_clause_in_proof = true;
                self.cold.empty_clause_lrat_id = proof_clause_id;
            }

            // Assign clause ID and record to clause trace.
            // When LRAT is enabled, resync with proof writer's ID if deletion
            // steps consumed IDs (#4398). In fail-close mode, non-empty LRAT
            // writes are intentionally suppressed, so writer IDs may lag solver
            // IDs. Keep solver IDs monotonic to avoid duplicate IDs in ClauseTrace.
            //
            // When LRAT is disabled but clause_trace is enabled (SMT proof path),
            // still allocate a clause ID and record the empty clause with its
            // resolution hints so that process_trace can reconstruct the proof
            // chain (#6368).
            if self.cold.lrat_enabled {
                let clause_id = if let Some(pid) = proof_clause_id.filter(|&id| id != 0) {
                    // Guard: LRAT returns Ok(0) as io_failed sentinel (#4434, #4572).
                    // Only sync when the writer returned a real ID.
                    // NOTE: uses pid+1 (not pid) because no add_clause_db follows.
                    // Contrast with enqueue_derived_unit which sets pid and lets
                    // add_clause_db increment (#4886).
                    self.cold.next_clause_id = pid + 1;
                    pid
                } else {
                    let id = self.cold.next_clause_id;
                    self.cold.next_clause_id += 1;
                    id
                };
                self.cold.empty_clause_lrat_id = Some(clause_id);
                // Record to clause trace if enabled — hints attached atomically
                if let Some(ref mut trace) = self.cold.clause_trace {
                    trace.add_clause_with_hints(clause_id, vec![], false, trace_hints);
                }
            } else if self.cold.clause_trace.is_some() {
                // SMT proof path: clause trace enabled without LRAT. Allocate a
                // local clause ID and record the empty clause with resolution
                // hints so process_trace can build a proper derivation (#6368).
                let clause_id = self.cold.empty_clause_lrat_id.unwrap_or_else(|| {
                    let id = self.cold.next_clause_id;
                    self.cold.next_clause_id += 1;
                    id
                });
                self.cold.empty_clause_lrat_id = Some(clause_id);
                if let Some(ref mut trace) = self.cold.clause_trace {
                    trace.add_clause_with_hints(clause_id, vec![], false, trace_hints);
                }
            }
        }
    }

    /// Mark that an empty clause was derived (UNSAT) with no resolution hints.
    #[inline]
    pub(super) fn mark_empty_clause(&mut self) {
        self.mark_empty_clause_with_hints(&[]);
    }

    /// Mark the empty clause with LRAT hints reconstructed from the level-0 trail.
    ///
    /// Used by inprocessing fallback paths that detect UNSAT without a concrete
    /// conflict clause to pass to `record_level0_conflict_chain`.
    #[inline]
    pub(super) fn mark_empty_clause_with_level0_hints(&mut self) {
        if self.cold.lrat_enabled {
            self.ensure_level0_unit_proof_ids();
            let hints = self.build_finalize_empty_clause_hints();
            self.mark_empty_clause_with_hints(&hints);
        } else {
            self.mark_empty_clause();
        }
    }

    /// Add a clause
    pub fn add_clause(&mut self, literals: Vec<Literal>) -> bool {
        if literals.is_empty() {
            self.mark_empty_clause();
            return false; // Empty clause = UNSAT
        }

        let mut literals = literals;
        if let Some(selector) = self.cold.scope_selectors.last().copied() {
            literals.push(Literal::positive(selector));
        }

        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped(literals, false);
        self.clear_diagnostic_pass();
        result
    }

    /// Add a pre-sorted clause, skipping the sort step but still deduping.
    ///
    /// The caller guarantees that literals are sorted by `.0` value.
    /// This function performs an O(n) dedup pass and tautology check on
    /// the sorted input, which is cheaper than add_clause's O(n log n)
    /// sort + O(n) dedup. For BV instances with 100K+ clauses, this
    /// saves ~10% of clause-addition time.
    ///
    /// If duplicate literals or tautologies (x and !x) are found, they
    /// are handled correctly (duplicates removed, tautologies skipped).
    pub fn add_clause_prenormalized(&mut self, literals: &[Literal]) -> bool {
        if literals.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // O(n) dedup + tautology check on pre-sorted input.
        // This is critical for correctness: Tseitin/BV clauses can contain
        // duplicate literals after CNF transformation, and passing duplicates
        // to the original ledger causes FINALIZE_SAT_FAIL during model
        // reconstruction (#8782).
        let mut deduped: Vec<Literal> = Vec::with_capacity(literals.len());
        for &lit in literals {
            if let Some(&last) = deduped.last() {
                if lit == last {
                    // Duplicate literal — skip
                    continue;
                }
                if lit.variable() == last.variable() {
                    // Tautology (x and !x) — skip entire clause
                    return true;
                }
            }
            deduped.push(lit);
        }

        if deduped.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // Record in original ledger (same as add_clause_unscoped).
        self.cold.original_ledger.push_clause(&deduped);
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;

        let _ = self.add_clause_db(&deduped, false);
        true
    }

    /// Add a clause without any scope selector (global clause).
    ///
    /// Use this for clauses that should persist across all push/pop scopes.
    /// Unlike `add_clause`, this does NOT add a scope selector even if
    /// we're currently inside a push() scope.
    #[allow(clippy::needless_pass_by_value)]
    pub fn add_clause_global(&mut self, literals: Vec<Literal>) -> bool {
        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped(literals, false);
        self.clear_diagnostic_pass();
        result
    }

    /// Add a clause scoped to an ancestor push depth.
    ///
    /// Depth `0` is global. Depth `self.scope_depth()` matches [`Self::add_clause`].
    /// This is used by incremental SMT layers when an assertion is first encoded
    /// in a deeper scope than the scope where it semantically belongs.
    pub fn add_clause_at_scope_depth(
        &mut self,
        literals: Vec<Literal>,
        scope_depth: usize,
    ) -> bool {
        debug_assert!(
            scope_depth <= self.cold.scope_selectors.len(),
            "requested scope depth {} exceeds active depth {}",
            scope_depth,
            self.cold.scope_selectors.len()
        );

        if scope_depth == 0 {
            return self.add_clause_global(literals);
        }
        if scope_depth == self.cold.scope_selectors.len() {
            return self.add_clause(literals);
        }

        let mut literals = literals;
        let selector = self.cold.scope_selectors[scope_depth - 1];
        literals.push(Literal::positive(selector));

        self.set_diagnostic_pass(DiagnosticPass::Input);
        let result = self.add_clause_unscoped(literals, false);
        self.clear_diagnostic_pass();
        result
    }

    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_clause_unscoped(
        &mut self,
        mut literals: Vec<Literal>,
        learned: bool,
    ) -> bool {
        // All literal variables must be in range
        debug_assert!(
            literals
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: add_clause_unscoped: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        if literals.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // Normalize: remove duplicate literals and discard tautologies.
        // Duplicate literals confuse the 2-watched literal scheme (both watches
        // on the same variable). Tautologies (x ∨ ¬x) are always satisfied.
        // CaDiCaL does this in External::add(); add_theory_lemma() already did.
        literals.sort_by_key(|l| l.0);
        literals.dedup();
        for i in 1..literals.len() {
            if literals[i].variable() == literals[i - 1].variable() {
                return true; // Tautology — always satisfied, nothing to add
            }
        }
        if literals.is_empty() {
            self.mark_empty_clause();
            return false;
        }

        // Record original (non-learned) clauses in the immutable ledger.
        // Only clauses from the public add_clause/add_clause_global API reach
        // here; derived clauses (BVE resolvents, theory lemmas) go through
        // add_clause_watched → add_clause_db and are NOT recorded, because
        // the ledger must reflect the true user input formula only.
        // #5031: original_clauses needed in release for incremental-solve
        // clause_db rebuild in reset_search_state.
        if !learned {
            self.cold.original_ledger.push_clause(&literals);
            // Keep boundary in sync: this clause goes into both the ledger AND
            // the arena (via add_clause_db below), so it's already "known" to
            // the arena. Without this, reset_search_state would re-add it.
            self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
            // New irredundant clause invalidates the uniform formula cache.
            self.cold.uniform_formula_cache = None;
        }

        let _ = self.add_clause_db(&literals, learned);

        true
    }

    /// Reorder clause literals for optimal watch selection using explicit state slices.
    fn reorder_clause_for_watches_with_state(
        vals: &[i8],
        var_data: &[VarData],
        literals: &mut [Literal],
    ) {
        if literals.len() < 2 {
            return;
        }

        // Score each literal: higher is better for watching
        // Unassigned = highest priority (we want to detect unit propagation)
        // True at high level = good (clause is satisfied, watches stable)
        // False at high level = better than false at low level
        let score = |lit: Literal| -> i64 {
            let v = vals[lit.index()];
            if v == 0 {
                i64::MAX // Unassigned - best
            } else {
                let level = i64::from(var_data[lit.variable().index()].level);
                if v > 0 {
                    // Literal is true
                    1_000_000 + level
                } else {
                    // Literal is false
                    level
                }
            }
        };

        // Find best two literals
        let mut best_idx = 0;
        let mut best_score = score(literals[0]);
        for (i, &lit) in literals.iter().enumerate().skip(1) {
            let s = score(lit);
            if s > best_score {
                best_score = s;
                best_idx = i;
            }
        }
        literals.swap(0, best_idx);

        let mut second_idx = 1;
        let mut second_score = score(literals[1]);
        for (i, &lit) in literals.iter().enumerate().skip(2) {
            let s = score(lit);
            if s > second_score {
                second_score = s;
                second_idx = i;
            }
        }
        literals.swap(1, second_idx);

        // Postcondition: no non-watched literal has a better score than the worst
        // watched literal. Violations indicate a bug in the scoring/selection logic.
        // (#3812: unified watch-attachment contract)
        debug_assert!(
            {
                let s0 = score(literals[0]);
                let s1 = score(literals[1]);
                let min_watch = s0.min(s1);
                literals[2..].iter().all(|lit| score(*lit) <= min_watch)
            },
            "BUG: reorder_clause_for_watches postcondition: non-watched literal has better score than watched"
        );
    }

    /// Learned-clause ordering: keep 1UIP at position 0 and place the max
    /// non-UIP decision level at position 1.
    fn reorder_learned_clause_for_watches(var_data: &[VarData], literals: &mut [Literal]) {
        if literals.len() <= 2 {
            return;
        }
        let max_idx = literals[1..]
            .iter()
            .enumerate()
            .max_by_key(|(_, lit)| var_data[lit.variable().index()].level)
            .map(|(i, _)| i + 1)
            .unwrap_or(1);
        if max_idx != 1 {
            literals.swap(1, max_idx);
        }
    }

    /// Prepare watched literals according to the selected ordering policy.
    pub(super) fn prepare_watched_literals_with_state(
        vals: &[i8],
        var_data: &[VarData],
        literals: &mut [Literal],
        policy: WatchOrderPolicy,
    ) -> Option<(Literal, Literal)> {
        if literals.len() < 2 {
            return None;
        }
        match policy {
            WatchOrderPolicy::Preserve => {}
            WatchOrderPolicy::AssignmentScore => {
                Self::reorder_clause_for_watches_with_state(vals, var_data, literals);
            }
            WatchOrderPolicy::LearnedBacktrack => {
                Self::reorder_learned_clause_for_watches(var_data, literals);
                let second_level = var_data[literals[1].variable().index()].level;
                let max_non_uip_level = literals[1..]
                    .iter()
                    .map(|lit| var_data[lit.variable().index()].level)
                    .max()
                    .unwrap_or(0);
                debug_assert_eq!(
                    second_level, max_non_uip_level,
                    "BUG: learned clause watch invariant violated: lits[1] must be the highest non-UIP level"
                );
            }
        }
        let lit0 = literals[0];
        let lit1 = literals[1];
        debug_assert_ne!(
            lit0, lit1,
            "BUG: watch literals must be distinct (policy={policy:?}, lit={lit0:?})"
        );
        Some((lit0, lit1))
    }

    /// Prepare watched literals according to the selected ordering policy.
    pub(super) fn prepare_watched_literals(
        &self,
        literals: &mut [Literal],
        policy: WatchOrderPolicy,
    ) -> Option<(Literal, Literal)> {
        Self::prepare_watched_literals_with_state(&self.vals, &self.var_data, literals, policy)
    }

    /// Attach the selected watched-literal pair to watch lists.
    pub(super) fn attach_clause_watches(
        &mut self,
        clause_ref: ClauseRef,
        watched: (Literal, Literal),
        is_binary: bool,
    ) {
        self.watches
            .watch_clause(clause_ref, watched.0, watched.1, is_binary);
    }
}
