// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory lemma and theory propagation clause addition.
//!
//! Split from `clause_add.rs` for file-size compliance (#5142).
//! Contains `add_theory_lemma` and `add_theory_propagation`.

use super::*;

impl Solver {
    /// Determine the proof emission kind for theory lemmas.
    ///
    /// Preprocessing extension lemmas (e.g., XOR Gauss-Jordan) use
    /// `TrustedTransform` because they are derivable from consumed
    /// original clauses. SMT theory lemmas use `Axiom` (#7913).
    #[inline]
    fn theory_lemma_proof_kind(&self) -> ProofAddKind {
        if self.cold.extension_trusted_lemmas {
            ProofAddKind::TrustedTransform
        } else {
            ProofAddKind::Axiom
        }
    }

    /// Add a theory lemma clause during solving.
    ///
    /// Unlike `add_clause`, this properly sets up watches so the clause can
    /// participate in propagation. This is essential for eager DPLL(T) where
    /// theory solvers add lemmas during the SAT search.
    ///
    /// The clause is reordered so that:
    /// - `literals[0]` is unassigned or the most recently assigned satisfying literal
    /// - `literals[1]` is unassigned or the next best choice for watching
    ///
    /// Returns the clause reference, or None if the clause is trivially SAT/UNSAT.
    pub fn add_theory_lemma(&mut self, mut literals: Vec<Literal>) -> Option<ClauseRef> {
        if literals.is_empty() {
            self.mark_empty_clause();
            return None;
        }

        // Remove duplicate literals and check for tautology
        literals.sort_by_key(|l| l.0);
        literals.dedup();

        // Bump VSIDS activity for variables in theory lemmas (#4919).
        // Without this, theory-relevant variables don't get prioritized in
        // the VSIDS decision heuristic. Boolean conflict analysis bumps
        // variables in learned clauses (conflict_analysis.rs:255), but
        // theory lemmas went through add_theory_lemma without bumping.
        // This causes the DPLL solver to spend decisions on low-activity
        // Boolean encoding variables instead of theory atoms, starving
        // the theory of conflicts and propagations.
        for lit in &literals {
            let var = lit.variable();
            if var.index() < self.num_vars {
                self.vsids.bump(
                    var,
                    &self.vals,
                    self.active_branch_heuristic != BranchHeuristic::Vmtf,
                );
            }
        }

        // Check for tautology (both x and ¬x)
        for i in 1..literals.len() {
            if literals[i].variable() == literals[i - 1].variable() {
                // Tautology - clause is always true
                return None;
            }
        }

        // All literal variables must be in range for safe assignment indexing.
        // Grow solver if extension produces out-of-range literals.
        {
            let max_var = literals
                .iter()
                .map(|l| l.variable().index())
                .max()
                .unwrap_or(0);
            if max_var >= self.num_vars {
                self.ensure_num_vars(max_var + 1);
            }
        }

        // Option C fail-close for #4492: LRAT cannot justify SMT theory lemmas
        // with SAT-resolution hints. Once theory lemmas appear, disable external
        // LRAT emission and rely on clause-trace/SMT proof paths instead.
        //
        // Exception (#7913): preprocessing extensions (e.g., XOR Gauss-Jordan)
        // consume original clauses and produce equivalent theory lemmas. These
        // are trusted transforms, not external theory axioms, so they do not
        // need to block LRAT.
        if !self.cold.extension_trusted_lemmas {
            if let Some(ref mut manager) = self.proof_manager {
                if manager.is_lrat() {
                    manager.block_lrat_for_theory_lemmas();
                }
            }
        }

        // Handle unit clause
        if literals.len() == 1 {
            let lit = literals[0];
            let var = lit.variable();
            match self.var_value_from_vals(var.index()) {
                Some(v) if v == lit.is_positive() => {
                    // Already satisfied
                    return None;
                }
                Some(_) => {
                    // Conflict with current assignment.
                    // At level 0, the conflicting assignment is permanent —
                    // the unit axiom contradicts a root-level fact, so UNSAT.
                    // Still route it through record_level0_conflict_chain()
                    // so the empty clause trace keeps the theory-clause and
                    // level-0 reason IDs needed for SMT proof reconstruction.
                    // At level > 0, don't declare UNSAT — the assignment may
                    // be retractable. Add the clause to the DB and return it
                    // as a conflict so the caller can backtrack (#6242).
                    let idx = self.add_clause_db_checked(&literals, true, false, &[]);
                    // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
                    self.mark_subsume_dirty_if_kept(idx);
                    let _ = self.proof_emit_add_prechecked(
                        &literals,
                        &[],
                        self.theory_lemma_proof_kind(),
                    );
                    #[cfg(debug_assertions)]
                    {
                        self.cold.pending_forward_check = None;
                    }
                    let clause_ref = ClauseRef(idx as u32);
                    if self.decision_level == 0 {
                        self.record_level0_conflict_chain(clause_ref);
                        return None;
                    }
                    return Some(clause_ref);
                }
                None => {
                    // Enqueue as unit propagation
                    debug_assert!(
                        literals.len() == 1,
                        "BUG: theory lemma unit path reached with {} literals",
                        literals.len(),
                    );
                    // Theory lemmas are axioms from the SMT layer, NOT derived
                    // by SAT resolution. Use forward_check_derived=false so the
                    // forward checker adds them as originals (not RUP-checked).
                    let idx = self.add_clause_db_checked(&literals, true, false, &[]);
                    // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
                    self.mark_subsume_dirty_if_kept(idx);
                    // Write to proof to keep LRAT clause ID counters in sync (#4123).
                    let pid = self
                        .proof_emit_add_prechecked(&literals, &[], self.theory_lemma_proof_kind())
                        .unwrap_or(0);
                    #[cfg(debug_assertions)]
                    {
                        self.cold.pending_forward_check = None;
                    }
                    let clause_ref = ClauseRef(idx as u32);
                    // Unit theory axiom: enqueue with reason=None (#6242).
                    // Store proof ID in unit_proof_id so LRAT chain collection
                    // can reference it (#6257).
                    if pid != 0 {
                        self.unit_proof_id[var.index()] = pid;
                    }
                    self.enqueue(lit, None);
                    return Some(clause_ref);
                }
            }
        }

        // Reorder literals to find best watched literals.
        let watched = self
            .prepare_watched_literals(&mut literals, WatchOrderPolicy::AssignmentScore)
            .expect("theory lemma multi-literal path requires at least 2 literals");

        debug_assert!(
            literals.len() >= 2,
            "BUG: theory lemma multi-literal path reached with {} literals",
            literals.len(),
        );
        // Theory lemmas are axioms from the SMT layer, NOT derived
        // by SAT resolution. Use forward_check_derived=false so the
        // forward checker adds them as originals (not RUP-checked).
        let idx = self.add_clause_db_checked(&literals, true, false, &[]);
        // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
        self.mark_subsume_dirty_if_kept(idx);
        // Write to proof to keep LRAT clause ID counters in sync (#4123).
        let _ = self.proof_emit_add_prechecked(&literals, &[], self.theory_lemma_proof_kind());
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }
        let clause_ref = ClauseRef(idx as u32);

        // Set up watches on first two literals.
        self.attach_clause_watches(clause_ref, watched, literals.len() == 2);
        let (lit0, lit1) = watched;

        // Check if the clause is already falsified or unit
        let lit0_val = self.lit_value(lit0);
        let lit1_val = self.lit_value(lit1);

        if lit0_val == Some(false) && lit1_val == Some(false) {
            // All literals are false - conflict detected
            // Only set has_empty_clause at level 0 (original fix for #132).
            // At higher levels, this is a normal conflict - the XOR extension
            // (or other theories) may add conflict clauses at any level,
            // and we should backtrack normally rather than claim UNSAT.
            if self.decision_level == 0 {
                self.record_level0_conflict_chain(clause_ref);
            } else {
                // At level > 0, BCP won't discover this conflict because
                // both watched literals are already assigned — no trail event
                // will trigger watch propagation for this clause. Store as
                // pending so the main solve loop can initiate conflict
                // analysis (#6262).
                self.pending_theory_conflict = Some(clause_ref);
            }
            return Some(clause_ref);
        } else if lit0_val.is_none() && lit1_val == Some(false) {
            // Unit clause - propagate lit0
            self.enqueue(lit0, Some(clause_ref));
        }

        Some(clause_ref)
    }

    /// Add a theory propagation directly to the trail without watch-list overhead (#4919).
    ///
    /// This is the lightweight counterpart to `add_theory_lemma`. It handles the
    /// common case where the theory knows a literal is implied (all reason literals
    /// are falsified, one literal is unassigned). Instead of adding the clause to
    /// the watch lists and waiting for BCP, this method:
    ///
    /// 1. Stores the clause in the arena (needed as reason during conflict analysis)
    /// 2. Directly enqueues the propagated literal on the trail
    /// 3. Skips watch-list attachment, VSIDS bumping, sort/dedup/tautology checks
    ///
    /// This matches Z3's `ctx().assign()` pattern for theory propagation where
    /// the literal goes directly to the trail with a lazy justification.
    ///
    /// # Arguments
    /// - `clause`: The full reason clause with the propagated literal as the FIRST
    ///   element. Format: `[propagated_lit, ¬reason₁, ¬reason₂, ...]`
    /// - `propagated`: The literal to enqueue (must equal `clause[0]`)
    ///
    /// # Safety invariant
    /// The caller must ensure:
    /// - `propagated` is unassigned
    /// - All other literals in `clause` are falsified under the current assignment
    /// - `propagated == clause[0]`
    pub fn add_theory_propagation(
        &mut self,
        mut clause: Vec<Literal>,
        propagated: Literal,
    ) -> Option<ClauseRef> {
        if clause.is_empty() {
            return None;
        }

        // Ensure propagated literal is at position 0 for correct reason extraction.
        // During conflict analysis, the solver reads reason[var] and uses literals[1..]
        // as the reason for the assignment. Position 0 is the asserted literal.
        if clause[0] != propagated {
            if let Some(pos) = clause.iter().position(|&l| l == propagated) {
                clause.swap(0, pos);
            } else {
                // propagated literal not in clause — fallback to full add_theory_lemma
                return self.add_theory_lemma(clause);
            }
        }

        debug_assert!(
            clause[0] == propagated,
            "BUG: add_theory_propagation: clause[0] != propagated"
        );

        // Normalize reason literals: remove duplicates and tautologies (#6506).
        // Theory solvers (e.g. LRA eager_row_bound_derivation) can produce
        // clauses with duplicate reason literals. Duplicates break the 2WL
        // invariant — initialize_watches() panics when both watch positions
        // hold the same literal.
        //
        // #7851 D3: Fast-path for already-deduplicated reasons.
        // LRA's collect_interval_reasons uses a `seen` HashSet (implied_interval.rs:156)
        // which guarantees no duplicates. Check with a linear scan first; only
        // fall through to the O(n log n) sort+dedup if duplicates are detected.
        // Z3 trusts theory reasons in its assign() path (arith_solver.cpp:1229-1241).
        if clause.len() >= 2 {
            // Fast duplicate/tautology check: O(n) scan before O(n log n) sort.
            let prop_var = propagated.variable();
            let mut needs_normalization = false;
            {
                // Check for prop_var in reason tail.
                for lit in &clause[1..] {
                    if lit.variable() == prop_var {
                        needs_normalization = true;
                        break;
                    }
                }
                // Check for duplicate literals in tail (pairwise scan).
                // For small tails (common case), this is cheaper than sort.
                if !needs_normalization && clause.len() <= 64 {
                    'outer: for i in 1..clause.len() {
                        for j in (i + 1)..clause.len() {
                            if clause[i].variable() == clause[j].variable() {
                                needs_normalization = true;
                                break 'outer;
                            }
                        }
                    }
                } else if !needs_normalization {
                    // For large clauses, fall back to sort-based detection.
                    needs_normalization = true;
                }
            }

            if needs_normalization {
                // Sort reason literals for dedup.
                clause[1..].sort_by_key(|l| l.0);
                // Remove consecutive duplicates in the tail only.
                let mut write = 1;
                for read in 2..clause.len() {
                    if clause[read] != clause[write] {
                        write += 1;
                        if write != read {
                            clause[write] = clause[read];
                        }
                    }
                }
                clause.truncate(write + 1);

                // Remove reason literals sharing a variable with propagated.
                // Same polarity = exact duplicate of propagated (redundant).
                // Opposite polarity = tautology → fall back to add_theory_lemma.
                if clause[1..]
                    .iter()
                    .any(|l| l.variable() == prop_var && *l != propagated)
                {
                    return self.add_theory_lemma(clause);
                }
                clause.retain(|l| *l == propagated || l.variable() != prop_var);

                // Check for tautologies among reason literals (same variable,
                // opposite polarity). After sort, same-variable literals are adjacent.
                for i in 2..clause.len() {
                    if clause[i].variable() == clause[i - 1].variable() {
                        return self.add_theory_lemma(clause);
                    }
                }
            }
        }

        // Fast check: if propagated literal is already assigned, skip or detect conflict.
        let var = propagated.variable();
        if var.index() >= self.num_vars {
            return None;
        }
        let val = self.vals[propagated.index()];
        if val > 0 {
            // Already true — propagation is redundant
            return None;
        }
        if val < 0 {
            // Already false — this is a conflict. Use full path for proper handling.
            return self.add_theory_lemma(clause);
        }

        // All literal variables must be in range
        debug_assert!(
            clause.iter().all(|l| l.variable().index() < self.num_vars),
            "BUG: add_theory_propagation: literal variable out of range"
        );

        // Reason literals (positions 1..n) must all be falsified under the
        // current assignment. If any reason literal is unassigned or satisfied,
        // the propagation reason is invalid for conflict analysis (#6262).
        // Fall back to add_theory_lemma which handles watches correctly.
        for lit in &clause[1..] {
            if self.lit_val(*lit) >= 0 {
                return self.add_theory_lemma(clause);
            }
        }

        // LRAT: block external LRAT for SMT theory lemmas.
        // Preprocessing extensions (XOR GJ) use trusted transforms (#7913).
        if !self.cold.extension_trusted_lemmas {
            if let Some(ref mut manager) = self.proof_manager {
                if manager.is_lrat() {
                    manager.block_lrat_for_theory_lemmas();
                }
            }
        }

        // Store clause in arena and set up watches (#6262).
        //
        // Originally this path skipped watch setup for speed. But without
        // watches, BCP cannot rediscover the clause after backtracking
        // undoes the propagation. This caused finalize_sat_model failures:
        // the clause sits in the DB, all literals false, no BCP trigger.
        //
        // With watches on clause[0] (propagated) and clause[1] (highest
        // false reason), BCP will re-discover unit propagation after
        // backtracking past the propagated literal's level.
        let idx = self.add_clause_db_checked(&clause, true, false, &[]);
        // Theory lemmas are always kept (LBD 0) — mark dirty (#7393).
        self.mark_subsume_dirty_if_kept(idx);
        let pid = self
            .proof_emit_add_prechecked(&clause, &[], self.theory_lemma_proof_kind())
            .unwrap_or(0);
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }
        let clause_ref = ClauseRef(idx as u32);

        if clause.len() <= 1 {
            // Unit clause: enqueue with reason=None (#6242).
            if pid != 0 {
                self.unit_proof_id[var.index()] = pid;
            }
            self.enqueue(propagated, None);
        } else {
            // Multi-literal: set up watches before enqueue.
            // clause[0] = propagated (about to be true), clause[1] = first reason (false).
            // This is the standard unit-propagation watch state.
            self.attach_clause_watches(clause_ref, (clause[0], clause[1]), clause.len() == 2);
            self.enqueue(propagated, Some(clause_ref));
        }

        Some(clause_ref)
    }
}
