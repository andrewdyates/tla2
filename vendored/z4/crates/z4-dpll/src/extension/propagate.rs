// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager propagation: the main BCP callback for the theory extension.
//!
//! Extracted from mod.rs for code health (#5970). Contains the body of
//! `Extension::propagate()` as a `propagate_impl()` helper, following
//! the same delegation pattern used by `check()` → `check_impl()`.

use z4_core::{FarkasAnnotation, TermId, TheoryLemmaKind, TheoryResult, TheorySolver};
use z4_sat::{ExtPropagateResult, Literal, SolverContext};

use super::types::format_term_recursive;
use super::{infer_bound_axiom_arith_kind, TheoryExtension};
use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_farkas,
};
use crate::verification::{
    log_conflict_debug, log_propagation_debug, verify_conflict_semantic, verify_euf_conflict,
    verify_theory_conflict, verify_theory_conflict_with_farkas, verify_theory_propagation,
};
#[cfg(debug_assertions)]
use crate::verification::{
    verify_lra_full_state_satisfiable, verify_propagation_semantic,
    verify_theory_conflict_with_farkas_full,
};

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Core logic for `Extension::propagate()`.
    ///
    /// Processes pending axiom clauses, feeds new SAT trail assignments to the
    /// theory solver, runs `check_during_propagate`, handles all `TheoryResult`
    /// variants (Sat, Unknown, NeedLemmas, NeedSplit, Unsat, UnsatWithFarkas),
    /// and collects theory propagations into SAT clauses.
    pub(super) fn propagate_impl(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.eager_stats.propagate_calls += 1;
        if !self.pending_axiom_clauses.is_empty() {
            let axioms = std::mem::take(&mut self.pending_axiom_clauses);
            let axiom_terms = std::mem::take(&mut self.pending_axiom_terms);
            let axiom_farkas = std::mem::take(&mut self.pending_axiom_farkas);
            // Record bound axioms as theory lemma proof steps (#6178, #6686).
            // Without this, SAT-level BCP can derive UNSAT using these axiom
            // clauses before the theory solver produces a Farkas conflict,
            // leaving the proof tracker without a corresponding TheoryLemma step.
            //
            // #6686: Use Farkas certificates from axiom validation so the
            // exported Alethe proof has `la_generic :args (c1 c2)` instead of
            // bare `la_generic` (which carcara rejects).
            if let Some(ref mut proof_ctx) = self.proof {
                for ((t1, p1, t2, p2), farkas) in
                    axiom_terms.into_iter().zip(axiom_farkas.into_iter())
                {
                    let term1 = if p1 {
                        t1
                    } else {
                        let Some(&neg) = proof_ctx.negations.get(&t1) else {
                            continue;
                        };
                        neg
                    };
                    let term2 = if p2 {
                        t2
                    } else {
                        let Some(&neg) = proof_ctx.negations.get(&t2) else {
                            continue;
                        };
                        neg
                    };
                    let clause = vec![term1, term2];
                    // #6365, #6686: Record bound axioms with Farkas certificates
                    // from axiom validation. Use the extracted certificate when
                    // available; fall back to unit [1, 1] when the validation
                    // returned plain Unsat without Farkas data.
                    let upgraded = self
                        .terms
                        .and_then(|terms| infer_bound_axiom_arith_kind(terms, t1, t2, p1, p2));
                    if let Some(kind) = upgraded {
                        let farkas_cert =
                            farkas.unwrap_or_else(|| FarkasAnnotation::from_ints(&[1i64, 1]));
                        proof_ctx.tracker.add_theory_lemma_with_farkas_and_kind(
                            clause,
                            farkas_cert,
                            kind,
                        );
                    } else {
                        // TODO(#8106): Bound axioms that fail arith kind inference
                        // still export as Generic/trust. These may be EUF or
                        // combined-theory axioms that need a dedicated classifier.
                        proof_ctx
                            .tracker
                            .add_theory_lemma_with_kind(clause, TheoryLemmaKind::Generic);
                    }
                }
            }
            return ExtPropagateResult::clauses(axioms);
        }

        let trail = ctx.trail();
        let sat_level = ctx.decision_level();
        // Only capture timestamps when diagnostic tracing is active.
        // Instant::now() syscalls accounted for ~5% of DPLL hot-loop time.
        let propagate_start = self.diagnostic_trace.is_some().then(std::time::Instant::now);
        let mut asserted_theory_atoms = 0usize;
        let mut check_result_label = "sat";
        // Push theory scope to match SAT decision level
        // This enables incremental backtracking via pop() instead of reset()
        let mut pushed = false;
        while self.theory_level < sat_level {
            // Save trail position before push so backtrack can restore it (#5548).
            self.level_trail_positions.push(self.last_trail_pos);
            self.theory.push();
            self.theory_level += 1;
            pushed = true;
            if let Some(diag) = self.diagnostic_trace {
                diag.emit_push(self.theory_level);
            }
            if self.debug {
                safe_eprintln!("[EAGER] Push to theory level {}", self.theory_level);
            }
        }

        // Process new assignments since last call
        let new_assignments = if self.last_trail_pos < trail.len() {
            &trail[self.last_trail_pos..]
        } else {
            &[]
        };

        // Feed new theory-relevant assignments to the theory solver
        for &lit in new_assignments {
            let var = lit.variable();
            if self.is_theory_atom(var) {
                if let Some(&term) = self.var_to_term.get(&var.id()) {
                    let value = lit.is_positive();
                    if self.debug {
                        safe_eprintln!(
                            "[EAGER] Asserting term {:?} = {} (var {:?}) at level {}",
                            term,
                            value,
                            var,
                            sat_level,
                        );
                    }
                    if sat_level == 0 && tracing::enabled!(tracing::Level::WARN) {
                        if let Some(terms) = self.terms {
                            let term_str = format_term_recursive(terms, term, 6);
                            tracing::warn!(
                                term = ?term,
                                value = value,
                                term_str = %term_str,
                                "  asserting theory atom at level 0"
                            );
                        }
                    }
                    self.theory.assert_literal(term, value);
                    asserted_theory_atoms += 1;
                }
            }
        }
        self.last_trail_pos = trail.len();

        // Skip theory check when no state change occurred (#4919):
        // - No new theory atoms were asserted (assert_literal not called)
        // - No push happened (scope unchanged)
        // - At least one check has already been done (not the first call)
        // This avoids redundant simplex re-verification on BCP rounds that
        // only propagate Boolean-only literals. The theory's check result is
        // unchanged when its state is unchanged.
        if asserted_theory_atoms == 0 && !pushed && self.has_checked {
            self.eager_stats.state_unchanged_skips += 1;
            self.emit_eager_event(sat_level, 0, "skip", 0, propagate_start);
            return ExtPropagateResult::none();
        }

        // #4919 / #8065: Adaptive atom batching for BCP theory check deferral.
        //
        // Z3 only runs theory checks at final_check_eh (complete assignment),
        // not during BCP. Z4 runs theory checks during BCP, which enables
        // eager conflict detection but also creates massive overhead on
        // ITE-heavy formulas (sc-*, simple_startup-*, uart-*) where BCP
        // assigns atoms from inactive ITE branches.
        //
        // Adaptive batching: when the theory solver is in "steady state"
        // (many consecutive checks with no propagations/conflicts), increase
        // the batch target so we accumulate more atoms before checking. This
        // reduces the number of BCP-time simplex calls while preserving
        // eagerness during the early conflict-finding phase.
        //
        // Phase 1 (streak < 5): No batching. Every theory atom triggers a check.
        // Phase 2 (5 <= streak < 50): Batch up to 20 atoms before checking.
        //   Original behavior — handles bound starvation.
        // Phase 3 (streak >= 50): Batch up to 200 atoms. The theory is in
        //   deep steady-state; most BCP checks are wasted. This is the key
        //   optimization for ITE-heavy benchmarks: instead of O(N) simplex
        //   calls per decision level, we get O(N/200).
        //
        // Conditions for deferral:
        // - Must have had >= streak threshold consecutive zero-propagation checks
        // - Must have accumulated < batch_target deferred atoms
        // - Must not be at decision level 0 (need to check for initial conflicts)
        // - Must not be the first check (need initial state)
        // - Must not have a push (scope change requires fresh check)
        // - Must not already have a pending split to hand back upstream
        const STARVATION_STREAK_THRESHOLD: u32 = 5;
        const BATCH_ATOM_TARGET_SMALL: u32 = 20;
        const DEEP_STREAK_THRESHOLD: u32 = 50;
        const BATCH_ATOM_TARGET_LARGE: u32 = 200;
        self.deferred_atom_count += asserted_theory_atoms as u32;
        let batch_target = if self.zero_propagation_streak >= DEEP_STREAK_THRESHOLD {
            BATCH_ATOM_TARGET_LARGE
        } else {
            BATCH_ATOM_TARGET_SMALL
        };
        let batching_ready = self.has_checked
            && !pushed
            && self.pending_split.is_none()
            && self.zero_propagation_streak >= STARVATION_STREAK_THRESHOLD
            && self.deferred_atom_count < batch_target;
        if batching_ready && sat_level == 0 {
            self.eager_stats.level0_batch_guard_hits += 1;
        }
        if batching_ready && sat_level > 0 {
            self.eager_stats.batch_defers += 1;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                "batch_defer",
                0,
                propagate_start,
            );
            return ExtPropagateResult::none();
        }
        // Reset deferred count — we're about to check.
        self.deferred_atom_count = 0;
        self.has_checked = true;
        if sat_level == 0 {
            self.eager_stats.level0_checks += 1;
        }

        // First check for theory conflicts (e.g., disequality violated by transitivity)
        // This is critical for eq_diamond where (= x0 x14) = false but transitivity
        // proves x0 = x14.
        // Use BCP-time hook: combined solvers override this to skip expensive
        // Nelson-Oppen fixpoints while standalone theories delegate to check().
        let check_res = if self.disable_theory_check {
            TheoryResult::Sat
        } else {
            self.theory.check_during_propagate()
        };
        let mut stop_for_inline_refinement_handoff = false;
        // #6546 Packet 5: buffer for inline lemma clauses added during
        // the check_during_propagate match. Merged into the propagation
        // `clauses` vec later before returning ExtPropagateResult.
        let mut inline_lemma_clauses: Vec<Vec<Literal>> = Vec::new();
        match check_res {
            TheoryResult::Sat => {
                // Clear stale pending single-var disequality splits from a prior
                // propagate() call (#6020). A NeedDisequalitySplit or NeedSplit
                // on a partial assignment may become unnecessary after further BCP.
                // But do NOT clear NeedExpressionSplit: multi-var disequalities
                // (E != F) need split atoms to be properly enforced. Clearing
                // them causes oscillation where the split is repeatedly discovered
                // and lost without ever reaching the pipeline (#4919).
                //
                // #6662: also clear NeedExpressionSplit if the split has
                // already been encoded in the persistent SAT solver.
                let is_stale_expr_split = matches!(
                    &self.pending_split,
                    Some(TheoryResult::NeedExpressionSplit(s))
                    if self.processed_expr_splits.is_some_and(|ps| ps.contains(&s.disequality_term))
                );
                if is_stale_expr_split
                    || !matches!(
                        &self.pending_split,
                        Some(TheoryResult::NeedExpressionSplit(_))
                    )
                {
                    self.pending_split = None;
                }
                let refinements = self.theory.take_bound_refinements();
                stop_for_inline_refinement_handoff =
                    self.should_stop_for_inline_bound_refinement_handoff(&refinements);
                self.record_pending_bound_refinements(refinements);
            }
            TheoryResult::Unknown => {
                // Theory cannot determine status yet — continue search.
                self.pending_bound_refinements.clear();
                check_result_label = "unknown";
            }
            // #6546 Packet 5: inline NeedLemmas handling during BCP.
            // Instead of storing NeedLemmas as pending_split (which requires a
            // full SAT re-solve), convert lemma clauses to SAT literals and add
            // them as inline clauses. This eliminates O(N) SAT-solve round-trips
            // for array ROW2 lemmas. Storeinv size 5: 1252 iterations → ~1.
            TheoryResult::NeedLemmas(lemmas) => {
                let mut sat_clauses = Vec::with_capacity(lemmas.len());
                let mut all_mapped = true;
                for lemma in &lemmas {
                    let sat_lits: Vec<Literal> = lemma
                        .clause
                        .iter()
                        .filter_map(|t| self.term_to_literal(t.term, t.value))
                        .collect();
                    if sat_lits.len() == lemma.clause.len() {
                        sat_clauses.push(sat_lits);
                    } else {
                        all_mapped = false;
                        break;
                    }
                }
                if all_mapped && !sat_clauses.is_empty() {
                    // All lemma terms have SAT variables — inject inline.
                    self.eager_stats.inline_lemma_clauses += sat_clauses.len() as u64;
                    check_result_label = "inline_lemmas";
                    inline_lemma_clauses.extend(sat_clauses);
                    // Record proof entries for inline lemmas (#6725).
                    // #8106: Infer specific kind instead of Generic/trust.
                    if let Some(ref mut proof_ctx) = self.proof {
                        for lemma in &lemmas {
                            let terms: Vec<TermId> = lemma
                                .clause
                                .iter()
                                .map(|lit| {
                                    if lit.value {
                                        lit.term
                                    } else {
                                        proof_ctx
                                            .negations
                                            .get(&lit.term)
                                            .copied()
                                            .unwrap_or(lit.term)
                                    }
                                })
                                .collect();
                            if let Some(term_store) = self.terms {
                                let kind = crate::theory_inference::infer_theory_lemma_kind_from_clause_terms(
                                    term_store,
                                    &terms,
                                );
                                match kind {
                                    TheoryLemmaKind::Generic => {
                                        proof_ctx.tracker.add_theory_lemma(terms);
                                    }
                                    _ => {
                                        proof_ctx.tracker.add_theory_lemma_with_kind(terms, kind);
                                    }
                                }
                            } else {
                                proof_ctx.tracker.add_theory_lemma(terms);
                            }
                        }
                    }
                } else {
                    // Fallback: some terms missing from SAT — use pending_split.
                    self.pending_split = Some(TheoryResult::NeedLemmas(lemmas));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedExpressionSplit(split) => {
                if self
                    .processed_expr_splits
                    .is_some_and(|s| s.contains(&split.disequality_term))
                {
                    check_result_label = "sat(stale-split)";
                } else {
                    self.expr_split_seen_count += 1;
                    self.pending_split = Some(TheoryResult::NeedExpressionSplit(split));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedModelEquality(eq) => {
                if self.model_equality_already_encoded(&eq) {
                    check_result_label = "sat(stale-model-eq)";
                } else {
                    self.pending_split = Some(TheoryResult::NeedModelEquality(eq));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                if let Some(check_result) = self.filter_stale_model_equalities(eqs) {
                    self.pending_split = Some(check_result);
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                } else {
                    check_result_label = "sat(stale-model-eqs)";
                }
            }
            check_result @ TheoryResult::NeedSplit(_)
            | check_result @ TheoryResult::NeedDisequalitySplit(_)
            | check_result @ TheoryResult::NeedStringLemma(_) => {
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                check_result_label = "split";
            }
            TheoryResult::Unsat(conflict_terms) => {
                // Log conflict for debugging false-UNSAT (#6242)
                if sat_level == 0 {
                    tracing::warn!(
                        conflict_len = conflict_terms.len(),
                        asserted_theory_atoms,
                        sat_level,
                        "Theory conflict at decision level 0 — potential false-UNSAT"
                    );
                    for (i, lit) in conflict_terms.iter().enumerate() {
                        tracing::warn!(
                            idx = i,
                            term = ?lit.term,
                            value = lit.value,
                            "  conflict atom"
                        );
                    }
                }
                // Verify the conflict is structurally valid (#3175)
                log_conflict_debug(&conflict_terms, "Unsat");
                if let Err(e) = verify_theory_conflict(&conflict_terms) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#4666): theory conflict verification failed in propagate(); skipping"
                    );
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                // EUF semantic re-check (#4704): re-derive conflict via fresh
                // congruence closure. Catches semantic bugs that pass structural
                // checks (e.g., claiming congruence when terms are not congruent).
                if self.theory.supports_euf_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_euf_conflict(&conflict_terms, terms) {
                            tracing::error!(
                                theory = std::any::type_name::<T>(),
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                "BUG(#4704): EUF semantic verification failed in propagate(); skipping"
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }
                // LRA semantic re-check (#6242, #7935): verify conflict atoms
                // are jointly UNSAT via fresh LRA solver.  Promoted to all
                // builds — the per-conflict check is cheap (2-3 atoms) and
                // catches spurious conflicts that cause false-UNSAT in release.
                if self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_conflict_semantic(&conflict_terms, terms) {
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                "BUG(#6242): LRA conflict semantic check failed; skipping conflict"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }
                // #7935: Full-state soundness guard for level-0 conflicts.
                // Individual conflict atoms may be genuinely contradictory, but
                // the FULL set of level-0 theory assignments should be consistent
                // for a satisfiable formula. If a fresh solver says SAT for all
                // currently-asserted theory atoms, the BCP chain derived an
                // incorrect forced assignment — reject the conflict.
                //
                // PERF: This creates a fresh LRA solver instance per level-0
                // conflict, which is O(atoms) per call. In release builds this
                // causes severe CHC regression (46/55 -> 35/55) because CHC
                // solves hundreds of SMT queries internally. Debug-only.
                #[cfg(debug_assertions)]
                if sat_level == 0 && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        let all_theory_lits: Vec<z4_core::TheoryLit> = trail
                            .iter()
                            .filter_map(|&lit| {
                                let var = lit.variable();
                                let term = self.var_to_term.get(&var.id())?;
                                if !self.theory_atom_set.contains(term) {
                                    return None;
                                }
                                Some(z4_core::TheoryLit::new(*term, lit.is_positive()))
                            })
                            .collect();
                        if let Err(e) = verify_lra_full_state_satisfiable(&all_theory_lits, terms) {
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                total_theory_atoms = all_theory_lits.len(),
                                "BUG(#7935): level-0 conflict rejected by full-state soundness guard"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }

                if let Some(proof) = self.proof.as_mut() {
                    let _ = record_theory_conflict_unsat(
                        proof.tracker,
                        self.terms,
                        proof.negations,
                        &conflict_terms,
                    );
                }

                let clause: Vec<Literal> = conflict_terms
                    .iter()
                    .filter_map(|t| self.term_to_literal(t.term, !t.value))
                    .collect();
                // Soundness guard (#3826): every theory explanation term MUST
                // map to a SAT literal. If any term was dropped by filter_map,
                // the resulting clause is stronger than what the theory proved.
                // Partial clauses block valid SAT assignments, causing false UNSAT.
                if clause.len() < conflict_terms.len() {
                    self.partial_clause_count += 1;
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    tracing::error!(
                        mapped = clause.len(),
                        total = conflict_terms.len(),
                        "BUG(#4666): theory conflict mapped to partial clause; skipping"
                    );
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                if self.debug {
                    safe_eprintln!("[EAGER] Theory check conflict: {} literals", clause.len());
                }
                self.theory_conflict_count += 1;
                // Conflicts reset the batching streak: a conflict IS meaningful
                // theory interaction. Incrementing the streak on conflicts caused
                // false-UNSAT on sat benchmarks (sc-6, sc-8, vpm2-30): the streak
                // grew, triggering batching that deferred theory checks, allowing
                // the SAT solver to accept theory-inconsistent assignments.
                self.zero_propagation_streak = 0;
                self.emit_eager_event(
                    sat_level,
                    asserted_theory_atoms,
                    "conflict",
                    0,
                    propagate_start,
                );
                return ExtPropagateResult::conflict(clause);
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                // Log conflict for debugging false-UNSAT (#6242)
                if sat_level == 0 {
                    tracing::warn!(
                        conflict_len = conflict.literals.len(),
                        asserted_theory_atoms,
                        sat_level,
                        "Farkas conflict at decision level 0 — potential false-UNSAT"
                    );
                    if tracing::enabled!(tracing::Level::WARN) {
                        if let Some(terms) = self.terms {
                            for (i, lit) in conflict.literals.iter().enumerate() {
                                let term_str = format_term_recursive(terms, lit.term, 6);
                                tracing::warn!(
                                    idx = i,
                                    term = ?lit.term,
                                    value = lit.value,
                                    term_str = %term_str,
                                    "  conflict atom"
                                );
                            }
                            if let Some(ref farkas) = conflict.farkas {
                                for (i, coeff) in farkas.coefficients.iter().enumerate() {
                                    tracing::warn!(
                                        idx = i,
                                        coeff = %coeff,
                                        "  Farkas coefficient"
                                    );
                                }
                            }
                        }
                    }
                }
                // Structural Farkas verification (#3175)
                log_conflict_debug(&conflict.literals, "UnsatWithFarkas");
                let mut farkas_valid = true;
                if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        // Missing Farkas annotation (#6535): conflict is sound but
                        // proof certificate cannot be recorded.
                        tracing::debug!(
                            conflict_len = conflict.literals.len(),
                            "Farkas annotation missing in propagate(); conflict clause is sound, skipping proof cert"
                        );
                    } else {
                        tracing::error!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            "BUG(#4666): Farkas conflict verification failed in propagate(); using conflict clause without certificate"
                        );
                    }
                    farkas_valid = false;
                }
                // Semantic Farkas verification (#4515): catches theory solver
                // bugs that produce structurally-valid but logically-wrong
                // certificates. Debug-only: BigRational arithmetic per conflict
                // is too expensive for release builds (W16-5: was 42% of QF_LRA
                // solver time due to exponential equality-alternative search).
                #[cfg(debug_assertions)]
                if farkas_valid && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_theory_conflict_with_farkas_full(&conflict, terms) {
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                "BUG(#4666): Farkas semantic verification failed in propagate(); using conflict clause without certificate"
                            );
                            farkas_valid = false;
                        }
                    }
                }

                // Record Farkas proof data only if the certificate is valid
                if farkas_valid {
                    if let Some(proof) = self.proof.as_mut() {
                        let _ = record_theory_conflict_unsat_with_farkas(
                            proof.tracker,
                            self.terms,
                            proof.negations,
                            &conflict,
                        );
                    }
                }

                // LRA semantic re-check (#6242, #7935): verify conflict atoms
                // are jointly UNSAT via fresh LRA solver.  Promoted to all
                // builds — catches spurious Farkas conflicts causing false-UNSAT.
                if self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_conflict_semantic(&conflict.literals, terms) {
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                "BUG(#6242): LRA conflict (Farkas) semantic check failed; skipping conflict"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }
                // #7935: Full-state soundness guard for level-0 Farkas conflicts.
                // Same logic as the Unsat path above — see detailed comment there.
                // Debug-only: creating a fresh LRA solver per conflict is too
                // expensive for release builds (see PERF note above).
                #[cfg(debug_assertions)]
                if sat_level == 0 && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        let all_theory_lits: Vec<z4_core::TheoryLit> = trail
                            .iter()
                            .filter_map(|&lit| {
                                let var = lit.variable();
                                let term = self.var_to_term.get(&var.id())?;
                                if !self.theory_atom_set.contains(term) {
                                    return None;
                                }
                                Some(z4_core::TheoryLit::new(*term, lit.is_positive()))
                            })
                            .collect();
                        if let Err(e) = verify_lra_full_state_satisfiable(&all_theory_lits, terms) {
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                total_theory_atoms = all_theory_lits.len(),
                                "BUG(#7935): level-0 Farkas conflict rejected by full-state soundness guard"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }

                // UnsatWithFarkas contains Farkas coefficients for interpolation
                // For DPLL purposes, we just need the conflict clause.
                // Even when the Farkas certificate is invalid, the conflict
                // literals are still correct (#5534).
                let clause: Vec<Literal> = conflict
                    .literals
                    .iter()
                    .filter_map(|t| self.term_to_literal(t.term, !t.value))
                    .collect();
                // Soundness guard (#3826): partial clause check (same as Unsat path).
                if clause.len() < conflict.literals.len() {
                    self.partial_clause_count += 1;
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    tracing::error!(
                        mapped = clause.len(),
                        total = conflict.literals.len(),
                        "BUG(#4666): Farkas conflict mapped to partial clause; skipping"
                    );
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                if self.debug {
                    safe_eprintln!(
                        "[EAGER] Theory check conflict with Farkas: {} literals",
                        clause.len()
                    );
                }
                self.theory_conflict_count += 1;
                // Reset streak on Farkas conflict (same as Unsat path).
                self.zero_propagation_streak = 0;
                self.emit_eager_event(
                    sat_level,
                    asserted_theory_atoms,
                    "conflict",
                    0,
                    propagate_start,
                );
                return ExtPropagateResult::conflict(clause);
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in propagate(): {other:?}"),
        }

        // Then check for theory propagations
        let propagations = self.theory.propagate();

        if propagations.is_empty() {
            // #4919: track consecutive zero-propagation check() calls.
            self.zero_propagation_streak += 1;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                check_result_label,
                inline_lemma_clauses.len(),
                propagate_start,
            );
            // After seeing the same expression split many times, stop
            // the SAT solver to hand control back to the split loop (#4919).
            // Previously threshold was 3 which caused premature Unknown on
            // benchmarks like sc-6.induction3 and uart-* where the expression
            // splits need more iterations to resolve (#4919).
            // Raised to 50 to allow the SAT solver more time to find a model
            // with the split atoms properly activated.
            let stop_for_expression_split = self.expr_split_seen_count >= 50
                && matches!(
                    &self.pending_split,
                    Some(TheoryResult::NeedExpressionSplit(_))
                );
            if stop_for_inline_refinement_handoff {
                self.eager_stats.bound_refinement_handoffs += 1;
            }
            let stop = stop_for_expression_split || stop_for_inline_refinement_handoff;
            // #6546: return inline lemma clauses even when no propagations.
            if !inline_lemma_clauses.is_empty() || stop {
                return ExtPropagateResult::clauses(inline_lemma_clauses).with_stop(stop);
            }
            return ExtPropagateResult::none();
        }

        // #4919: propagations produced — reset bound starvation streak.
        self.zero_propagation_streak = 0;

        // #6546: start with inline lemma clauses from check_during_propagate.
        let mut clauses = inline_lemma_clauses;
        let mut propagation_pairs: Vec<(Vec<Literal>, Literal)> = Vec::new();

        for prop in propagations {
            // Verify propagation structure (#4346)
            log_propagation_debug(&prop, "eager");
            if let Err(e) = verify_theory_propagation(&prop) {
                tracing::error!(
                    error = %e,
                    "BUG(#4666): theory propagation verification failed; skipping"
                );
                continue;
            }

            // Semantic propagation verification (#4346, #6242): reason ∧ ¬propagated → ⊥
            // #8782: Demoted to debug-only. Root cause fixed in implied_interval.rs:
            // collect_interval_reasons now uses BoundExplanation (eager explanation)
            // instead of collect_row_reasons_recursive which produced incomplete
            // reasons after simplex basis changes.
            #[cfg(debug_assertions)]
            if let Some(terms) = self.terms {
                const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                    if let Err(e) = verify_propagation_semantic(&prop, terms) {
                        tracing::error!(
                            error = %e,
                            propagated_term = ?prop.literal.term,
                            propagated_value = prop.literal.value,
                            reason_count = prop.reason.len(),
                            "BUG(#6242): propagation semantic verification failed; skipping unsound propagation"
                        );
                        continue;
                    }
                }
            }

            // Convert the propagated literal to SAT
            if let Some(lit) = self.term_to_literal(prop.literal.term, prop.literal.value) {
                let var = lit.variable();

                // Check current assignment
                if let Some(value) = ctx.value(var) {
                    if value != prop.literal.value {
                        // Theory propagated opposite of current assignment - conflict!
                        let mut conflict: Vec<Literal> = prop
                            .reason
                            .iter()
                            .filter_map(|r| self.term_to_literal(r.term, !r.value))
                            .collect();
                        // Soundness guard (#3826): partial clause check. Dropping
                        // reason terms makes the conflict stronger than what the
                        // theory proved.
                        if conflict.len() < prop.reason.len() {
                            self.partial_clause_count += 1;
                            if self.partial_clause_count >= 100 {
                                tracing::error!(
                                    count = self.partial_clause_count,
                                    "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                                );
                            }
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            continue;
                        }
                        // Reason literal falsification guard (#6262): every
                        // reason literal must be falsified. If not, the theory
                        // produced an invalid explanation — skip this conflict.
                        let all_reasons_falsified = conflict.iter().all(|reason_lit| {
                            let rv = reason_lit.variable();
                            ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                        });
                        if !all_reasons_falsified {
                            tracing::warn!(
                                propagated = ?lit,
                                reason_count = conflict.len(),
                                "BUG(#6262): theory propagation conflict has non-falsified reason literal; skipping"
                            );
                            continue;
                        }
                        conflict.push(lit);

                        if self.debug {
                            safe_eprintln!(
                                "[EAGER] Theory propagation conflict: {} literals",
                                conflict.len()
                            );
                        }
                        self.theory_conflict_count += 1;
                        self.emit_eager_event(
                            sat_level,
                            asserted_theory_atoms,
                            "conflict",
                            0,
                            propagate_start,
                        );
                        return ExtPropagateResult::conflict(conflict);
                    }
                    // Already assigned correctly - skip
                    continue;
                }

                // Literal is unassigned - create propagation clause
                // Clause: (propagated_lit ∨ ¬reason1 ∨ ¬reason2 ∨ ...)
                // Propagated literal is placed FIRST for add_theory_propagation.
                let mut clause: Vec<Literal> = Vec::with_capacity(prop.reason.len() + 1);
                clause.push(lit); // propagated literal first
                let reason_count = prop.reason.len();
                for r in &prop.reason {
                    if let Some(reason_lit) = self.term_to_literal(r.term, !r.value) {
                        clause.push(reason_lit);
                    }
                }
                // Soundness guard (#3826): if any reason term failed to map,
                // the propagation clause would be too strong. Skip it.
                if clause.len() - 1 < reason_count {
                    self.partial_clause_count += 1;
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    continue;
                }

                // Reason literal falsification guard (#6262): every reason
                // literal (clause[1..]) must be falsified under the current SAT
                // assignment. If any reason literal is unassigned or satisfied,
                // the theory produced an invalid propagation reason — demote
                // from lightweight propagation to a full theory lemma clause
                // that handles watches correctly.
                let all_reasons_falsified = clause[1..].iter().all(|reason_lit| {
                    let rv = reason_lit.variable();
                    ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                });
                if !all_reasons_falsified {
                    tracing::warn!(
                        propagated = ?lit,
                        reason_count = clause.len() - 1,
                        "BUG(#6262): theory propagation has non-falsified reason literal; demoting to lemma"
                    );
                    // Add as a regular watched clause instead of a propagation.
                    // add_theory_lemma handles watches and BCP correctly for
                    // clauses with arbitrary literal assignment states.
                    clauses.push(clause);
                    continue;
                }

                if self.debug {
                    safe_eprintln!(
                        "[EAGER] Adding propagation clause: {} literals (propagates {:?}={})",
                        clause.len(),
                        var,
                        prop.literal.value
                    );
                }

                // Use lightweight propagation path (#4919): skip watch setup,
                // VSIDS bump, sort/dedup. Clause is stored only as reason.
                propagation_pairs.push((clause, lit));
            }
        }

        let stop_for_expression_split = self.expr_split_seen_count >= 3
            && matches!(
                &self.pending_split,
                Some(TheoryResult::NeedExpressionSplit(_))
            );
        let stop = stop_for_expression_split || stop_for_inline_refinement_handoff;
        if stop_for_inline_refinement_handoff {
            self.eager_stats.bound_refinement_handoffs += 1;
        }

        let total_props = clauses.len() + propagation_pairs.len();
        if total_props == 0 {
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                check_result_label,
                0,
                propagate_start,
            );
            ExtPropagateResult::new(clauses, propagation_pairs, None, stop)
        } else {
            self.theory_propagation_count += total_props as u64;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                "propagated",
                total_props,
                propagate_start,
            );
            ExtPropagateResult::new(clauses, propagation_pairs, None, stop)
        }
    }
}
