// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String theory solving for QF_S.
//!
//! Routes QF_S through `StringSolver` from `z4-strings` crate.
//! The QF_SLIA pipeline is in `strings_lia.rs`.
//! String analysis helpers (length bounds, alphabet, candidates) are in
//! `strings_analysis.rs`.

use z4_core::term::{Constant, TermData};
use z4_core::{StringLemma, TermId, Tseitin};
use z4_sat::SatResult;
use z4_strings::StringSolver;

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::DpllT;

use super::super::Executor;
use super::skolem_cache::ExecutorSkolemCache;
use super::strings_analysis::MAX_CONSECUTIVE_DUPLICATE_LEMMAS;
use super::{debug_auflia_enabled, MAX_STRING_LEMMA_ITERATIONS};

// String analysis helpers (collect_decomposition_concat_terms,
// detect_bounded_string_vars, collect_alphabet, generate_candidates,
// LengthBound, MAX_PIVOT_CANDIDATES) live in strings_analysis.rs.

impl Executor {
    /// Solve QF_S using the string theory solver.
    ///
    /// Uses step-based DPLL(T) with `StringSolver` for theory checking.
    /// The string solver detects constant conflicts (x = "a" ∧ x = "b"),
    /// containment cycles, and disequality violations.
    ///
    /// Uses `solve_step()` (lazy theory checking after full SAT assignment)
    /// instead of `solve_eager()` (eager theory propagation during BCP).
    /// This enables future split/lemma handling for Phase C variable reasoning.
    pub(in crate::executor) fn solve_strings(&mut self) -> Result<SolveResult> {
        use crate::SolveStepResult;

        let proof_enabled = self.produce_proofs_enabled();

        if proof_enabled {
            self.proof_tracker.set_theory("Strings");
            for (idx, &assertion) in self.ctx.assertions.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(assertion, Some(format!("h{idx}")));
            }
        }

        // Lift ITEs from equalities (same as EUF path)
        let mut lifted_assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        lifted_assertions = self.fold_ground_string_ops(&lifted_assertions);
        if lifted_assertions.iter().any(|&term| {
            matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Bool(false))
            )
        }) {
            return Ok(SolveResult::Unsat);
        }
        lifted_assertions.retain(|&term| {
            !matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Bool(true))
            )
        });
        if lifted_assertions.is_empty() {
            self.skip_model_eval = true;
            self.last_model = Some(super::super::model::Model {
                sat_model: Vec::new(),
                term_to_var: hashbrown::HashMap::new(),
                euf_model: None,
                array_model: None,
                lra_model: None,
                lia_model: None,
                bv_model: None,
                fp_model: None,
                string_model: None,
                seq_model: None,
            });
            return Ok(SolveResult::Sat);
        }

        // Pre-register eager str.contains decompositions (Phase 2, #3402).
        // Creates skolem decompositions before Tseitin so the SAT solver sees
        // them from iteration 0, avoiding the CoreSolver-recreated-each-iteration bug.
        let mut skolem_cache = ExecutorSkolemCache::new();
        let mut decomposed_vars = hashbrown::HashSet::new();
        let mut contains_decomposed_vars = hashbrown::HashSet::new();
        let contains_decomps = self.preregister_contains_decompositions(
            &lifted_assertions,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let preregistered_reduced_term_ids =
            self.collect_decomposition_concat_terms(&contains_decomps);
        lifted_assertions.extend(contains_decomps);

        // Run Tseitin transformation
        let tseitin = Tseitin::new(&self.ctx.terms);
        let tseitin_result = tseitin.transform_all(&lifted_assertions);

        // Tseitin non-vacuity: non-empty assertions must produce clauses (#4714)
        debug_assert!(
            lifted_assertions.is_empty() || !tseitin_result.clauses.is_empty(),
            "BUG: Tseitin produced 0 clauses from {} assertions in Strings",
            lifted_assertions.len()
        );

        let mut negations: hashbrown::HashMap<TermId, TermId> = hashbrown::HashMap::new();
        if proof_enabled {
            for &term in tseitin_result.var_to_term.values() {
                let not_term = self.ctx.terms.mk_not(term);
                negations.insert(term, not_term);
            }
        }

        // Reuse the preprocessing skolem cache across runtime lemmas.
        // Track last emitted lemma to detect consecutive non-progress loops (#3375, #3429).
        // Only stall when the SAME lemma is requested in consecutive iterations (no
        // intervening new lemmas changed the context). Previously this used a HashSet
        // which permanently marked lemmas, incorrectly treating re-requests after
        // intervening VarSplit/LengthSplit as duplicates.
        let mut last_lemma: Option<StringLemma> = None;
        let mut duplicate_streak = 0usize;
        let mut dynamic_reduced_term_ids: Vec<TermId> = Vec::new();

        let mut string_lemma_requests = 0usize;

        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Create string solver and DPLL. Pre-register empty string so
        // endpoint-empty inferences work even when the formula has no
        // explicit "" literal.
        let empty_id = self.ctx.terms.mk_string(String::new());
        let mut theory = StringSolver::new(&self.ctx.terms);
        theory.set_empty_string_id(empty_id);
        for &tid in &preregistered_reduced_term_ids {
            theory.mark_reduced(tid);
        }
        for &tid in &dynamic_reduced_term_ids {
            theory.mark_reduced(tid);
        }
        let mut dpll = if proof_enabled {
            DpllT::from_tseitin_with_proof(&self.ctx.terms, &tseitin_result, theory)
        } else {
            DpllT::from_tseitin(&self.ctx.terms, &tseitin_result, theory)
        };
        self.apply_random_seed_to_dpll(&mut dpll);
        self.apply_progress_to_dpll(&mut dpll);
        dpll.set_max_learned_clauses(self.learned_clause_limit);
        dpll.set_max_clause_db_bytes(self.clause_db_bytes_limit);
        if let Some(seed) = self.random_seed {
            dpll.sat_solver_mut().set_random_seed(seed);
        }

        let mut step_result = if proof_enabled {
            dpll.solve_eager_step(Some((&mut self.proof_tracker, &negations)))?
        } else {
            dpll.solve_eager_step(None)?
        };
        let mut sat_reason = dpll.sat_unknown_reason();

        // Inner loop: handle string lemmas inline by preserving SAT state,
        // adding lemma clauses, and re-solving. All other results return
        // immediately (QF_S does not use arithmetic splits).
        loop {
            match step_result {
                SolveStepResult::Done(solve_result) => {
                    // Soundness guard (#6273): SAT-level UNSAT after adding
                    // string lemma clauses may be false.
                    if matches!(solve_result, SatResult::Unsat) && string_lemma_requests > 0 {
                        collect_sat_stats!(self, dpll.sat_solver());
                        Self::record_sat_unknown_reason(&mut self.last_unknown_reason, sat_reason);
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }

                    let string_model = if matches!(solve_result, SatResult::Sat(_)) {
                        Some(dpll.theory_solver().extract_model())
                    } else {
                        None
                    };

                    // Collect statistics and SAT unknown reason (#4622)
                    collect_sat_stats!(self, dpll.sat_solver());

                    if proof_enabled && matches!(solve_result, SatResult::Unsat) {
                        self.last_clause_trace = dpll.take_clause_trace();
                        // Use the full DPLL mapping, not the initial Tseitin map:
                        // string lemmas can allocate fresh SAT vars mid-loop.
                        self.last_var_to_term = Some(dpll.clone_var_to_term_snapshot());
                        self.last_negations = Some(negations.clone());
                        self.last_clausification_proofs = None;
                        self.last_original_clause_theory_proofs = None;
                    }

                    Self::record_sat_unknown_reason(&mut self.last_unknown_reason, sat_reason);
                    return self.solve_and_store_model_full(
                        solve_result,
                        &tseitin_result,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        string_model,
                        None,
                    );
                }
                // QF_S does not use arithmetic splits or model equalities.
                SolveStepResult::NeedBoundRefinements(_)
                | SolveStepResult::NeedSplit(_)
                | SolveStepResult::NeedDisequalitySplit(_)
                | SolveStepResult::NeedExpressionSplit(_)
                | SolveStepResult::NeedLemmas(_)
                | SolveStepResult::NeedModelEquality(_)
                | SolveStepResult::NeedModelEqualities(_) => {
                    return Ok(SolveResult::Unknown);
                }
                SolveStepResult::NeedStringLemma(lemma) => {
                    string_lemma_requests += 1;

                    // Safety net: detect CONSECUTIVE duplicate lemma requests (#3375, #3429).
                    // A lemma is only a stall if it's the same as the immediately preceding
                    // one (no intervening new lemma changed the context). Permanent dedup
                    // via HashSet incorrectly blocked re-requests that become productive
                    // after VarSplit/LengthSplit decomposition changes the SAT model.
                    if last_lemma.as_ref() == Some(&lemma) {
                        duplicate_streak += 1;
                    } else {
                        duplicate_streak = 0;
                    }
                    last_lemma = Some(lemma.clone());

                    // Preserve SAT progress while dropping the current theory/term borrow.
                    // After this point self.ctx.terms is no longer borrowed, so we can
                    // call &mut self methods and check abort/limits.
                    let sat_state = dpll.into_sat_state();

                    if self.should_abort_theory_loop() {
                        return Ok(SolveResult::Unknown);
                    }
                    if string_lemma_requests >= MAX_STRING_LEMMA_ITERATIONS {
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }
                    if duplicate_streak >= MAX_CONSECUTIVE_DUPLICATE_LEMMAS {
                        if debug_auflia_enabled() {
                            safe_eprintln!(
                                "[QF_S] Lemma {}: duplicate-streak {} for {:?} lemma (x={:?}, y={:?}, off={}) — stalled, returning Unknown",
                                string_lemma_requests,
                                duplicate_streak + 1,
                                lemma.kind,
                                lemma.x,
                                lemma.y,
                                lemma.char_offset,
                            );
                        }
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }
                    for tid in self.string_lemma_reduced_terms(&lemma, &mut skolem_cache) {
                        if !dynamic_reduced_term_ids.contains(&tid) {
                            dynamic_reduced_term_ids.push(tid);
                        }
                    }
                    let clauses = self.create_string_lemma_clauses(&lemma, &mut skolem_cache);
                    if proof_enabled {
                        for clause in &clauses {
                            for &atom in clause {
                                let not_atom = self.ctx.terms.mk_not(atom);
                                negations.insert(atom, not_atom);
                            }
                        }
                    }
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[QF_S] Lemma {}: string {:?} (x={:?}, y={:?}, off={}, {} clauses)",
                            string_lemma_requests,
                            lemma.kind,
                            lemma.x,
                            lemma.y,
                            lemma.char_offset,
                            clauses.len()
                        );
                    }
                    let empty_id = self.ctx.terms.mk_string(String::new());
                    let mut theory = StringSolver::new(&self.ctx.terms);
                    theory.set_empty_string_id(empty_id);
                    for &tid in &dynamic_reduced_term_ids {
                        theory.mark_reduced(tid);
                    }
                    dpll = DpllT::from_sat_state(&self.ctx.terms, theory, sat_state);
                    self.apply_progress_to_dpll(&mut dpll);
                    dpll.set_max_learned_clauses(self.learned_clause_limit);
                    dpll.set_max_clause_db_bytes(self.clause_db_bytes_limit);
                    if let Some(seed) = self.random_seed {
                        dpll.sat_solver_mut().set_random_seed(seed);
                    }
                    // Skip BVE/probing/subsumption on incremental re-solves.
                    dpll.sat_solver_mut().set_preprocess_enabled(false);
                    for clause in &clauses {
                        if proof_enabled {
                            dpll.apply_string_lemma_with_proof_tracking(
                                clause,
                                &mut self.proof_tracker,
                            );
                        } else {
                            dpll.apply_string_lemma(clause);
                        }
                    }
                    step_result = if proof_enabled {
                        dpll.solve_eager_step(Some((&mut self.proof_tracker, &negations)))?
                    } else {
                        dpll.solve_eager_step(None)?
                    };
                    sat_reason = dpll.sat_unknown_reason();
                }
            }
        }
    }

    // QF_SLIA pipeline (solve_strings_lia, solve_strings_lia_with_assumptions,
    // solve_strings_lia_preprocessed) moved to strings_lia.rs (#7006).
}
