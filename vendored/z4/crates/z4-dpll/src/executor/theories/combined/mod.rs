// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined theory solving: UF+LRA, UF+NRA, AUFLIA, AUFLRA, BV+LIA.
//!
//! LIRA and AUFLIRA (mixed Int + Real) methods are in `lira`.

mod lira;

use crate::combined_solvers::combiner::TheoryCombiner;
use crate::combined_solvers::UfNraSolver;
use crate::executor::theories::solve_harness::{ProofProblemAssertionProvenance, TheoryModels};
use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalTheoryState;
use z4_core::TermId;

use super::super::Executor;
use super::{MAX_SPLITS_LIA, MAX_SPLITS_LRA};

fn empty_hash_set<T>() -> hashbrown::HashSet<T>
where
    T: Eq + std::hash::Hash,
{
    hashbrown::HashSet::new()
}

impl Executor {
    /// Pre-configure the persistent SAT solver with Z3-style search tuning
    /// for the incremental split-loop pipeline (#4919 Phase 6).
    ///
    /// The old `solve_split_loop_pipeline!` applied these via `pre_solve` callbacks.
    /// The incremental macro creates the solver internally, so we pre-seed
    /// the IncrementalTheoryState with a configured solver that the macro
    /// will detect and reuse via `pipeline_incremental_setup!`.
    fn configure_sat_search_tuning(
        &mut self,
        geometric_initial: f64,
        geometric_factor: f64,
        random_var_freq: f64,
    ) {
        use z4_sat::Solver as SatSolver;
        let proof_enabled = self.produce_proofs_enabled();
        let random_seed = self.current_random_seed();
        let should_record_random_seed = self
            .incr_theory_state
            .as_ref()
            .is_none_or(|state| state.persistent_sat.is_none());
        if should_record_random_seed {
            self.record_applied_sat_random_seed_for_test(random_seed);
        }
        let state = self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        if state.persistent_sat.is_none() {
            let mut sat = SatSolver::new(0);
            sat.set_random_seed(random_seed);
            sat.set_geometric_restarts(geometric_initial, geometric_factor);
            sat.set_random_var_freq(random_var_freq);
            if let Some(seed) = self.random_seed {
                sat.set_random_seed(seed);
            }
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if proof_enabled {
                sat.enable_clause_trace();
            }
            state.persistent_sat = Some(sat);
        }
    }

    /// Solve using combined EUF + LRA theory with disequality split support (#6129).
    ///
    /// Uses an isolated incremental split loop so disequality and model-equality
    /// continuations do not rebuild the SAT layer between iterations.
    pub(in crate::executor) fn solve_uf_lra(&mut self) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_isolated_incremental_state(None, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "UFLRA",
                persistent_sat_field: persistent_sat,
                create_theory: TheoryCombiner::uf_lra(&this.ctx.terms),
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, lra) = theory.extract_euf_lra_models();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                // #5462 Packet 4: enable eager theory-SAT interleaving for UFLRA.
                // Combined check runs local-only during BCP; full Nelson-Oppen
                // fixpoint runs once after SAT via needs_final_check_after_sat().
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined EUF + NRA theory with disequality split support.
    ///
    /// Structurally identical to `solve_uf_lra`, substituting UfNraSolver for UfLraSolver.
    /// NraSolver wraps LraSolver internally with tangent plane and sign lemma refinement
    /// for nonlinear products. The Nelson-Oppen combination with EUF is identical.
    pub(in crate::executor) fn solve_uf_nra(&mut self) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_isolated_incremental_state(None, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "UFNRA",
                persistent_sat_field: persistent_sat,
                create_theory: UfNraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, lra) = theory.extract_models();
                    TheoryModels {
                        euf: Some(euf),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                // #5462 Packet 4: enable eager theory-SAT interleaving for UFNRA.
                // Same two-stage pattern as UFLRA: local-only BCP checks, full
                // Nelson-Oppen fixpoint deferred to needs_final_check_after_sat().
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LIA theory
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for integer variables.
    pub(in crate::executor) fn solve_auf_lia(&mut self) -> Result<SolveResult> {
        // Fast path: if the formula has no substantive integer arithmetic
        // constraints (no comparisons, no +/-/*/mod/div, no integer constants),
        // delegate to Array+EUF which avoids the expensive N-O combination
        // with LIA. This handles QF_AUFLIA formulas where Int is used only
        // as the Array index/value sort with no arithmetic reasoning (#6546).
        //
        // In incremental mode, keep pure-UF/Int formulas on the rebuilding
        // AUFLIA path instead of the persistent ArrayEUF fast path. Reusing the
        // no-split incremental state across a pop()+re-push contradiction cycle
        // can retain stale scoped reasoning and produce a false SAT model
        // (#6813). Rebuilding the combined solver each check-sat preserves
        // soundness while we keep the pure fast path for non-incremental solves.
        if !self.incremental_mode
            && !crate::term_helpers::has_substantive_int_constraints(
                &self.ctx.terms,
                &self.ctx.assertions,
            )
        {
            return self.solve_array_euf();
        }

        let (preprocessed_assertions, proof_provenance) =
            self.preprocess_auflia_assertions_with_proof_provenance();

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.5, 0.02);
            solve_incremental_split_loop_pipeline!(this,
                tag: "AUFLIA",
                persistent_sat_field: persistent_sat,
                create_theory: TheoryCombiner::auf_lia(&this.ctx.terms),
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, arr, lia) = theory.extract_all_models_auflia();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory
                        .take_learned_state()
                        .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                    let ds = theory.take_dioph_state().unwrap_or_default();
                    (lc, hc, ds)
                },
                // #6846: Use lazy path for AUFLIA. The eager extension drops
                // theory conflicts when model equality terms lack SAT variable
                // mappings (_ext_partial > 0), causing Unknown on formulas that
                // need N-O model equalities (add5, add6, read7).
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LIA theory with assumptions.
    ///
    /// This is the assumption-based version of [`Self::solve_auf_lia`], enabling
    /// `check-sat-assuming` for DT+arithmetic formulas that require integer splits.
    /// Fixes #1771: check-sat-assuming now handles NeedSplit like regular check-sat.
    ///
    /// # Arguments
    /// * `assertions` - Base assertions (including DT axioms)
    /// * `assumptions` - Assumption terms to activate
    ///
    /// # Returns
    /// * `SolveResult::Sat` - satisfiable under assumptions
    /// * `SolveResult::Unsat` - unsatisfiable (core stored in `last_assumption_core`)
    /// * `SolveResult::Unknown` - could not determine (e.g., split limit reached)
    pub(in crate::executor) fn solve_auf_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        // Preprocess assertions and assumptions through the full LIA normalization
        // family: variable substitution, SOM, ITE lifting, mod/div elimination (#6737).
        let artifacts = self.preprocess_mixed_arith_assumptions(assertions, assumptions);
        let var_subst = artifacts.var_subst;
        let final_assumptions = artifacts.assumptions;

        // Preserve original assertions for fill-only equality recovery on SAT.
        let original_assertions: Vec<TermId> = assertions.to_vec();
        let original_problem_assertions = original_assertions.clone();

        // Eager array axioms for soundness (#4304, #5086, #6282).
        // Include assumption terms in the reachable set so assumption-only
        // array operations get axioms in incremental mode (#6736).
        let assumption_terms: Vec<TermId> = final_assumptions.iter().map(|(t, _)| *t).collect();
        let mut final_assertions = artifacts.assertions;
        {
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at_with_roots(axiom_start, &assumption_terms);
            let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();
            let generated_axioms = self.ctx.terms.expand_select_store_all(&generated_axioms);
            final_assertions.extend(generated_axioms);
        }
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &final_assertions,
            artifacts.assertion_sources,
        );

        // Use isolated incremental state with the new incremental assumption
        // split-loop macro (#6689 Packet 4). The persistent SAT solver keeps
        // learned clauses + LIA state across split iterations directly — no
        // manual preservation needed.
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(final_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.5, 0.02);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "AUFLIA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: TheoryCombiner::auf_lia(&this.ctx.terms),
                extract_models: |theory| {
                    let model_roots: Vec<TermId> = this
                        .ctx
                        .assertions
                        .iter()
                        .copied()
                        .chain(final_assumptions.iter().map(|(term, _)| *term))
                        .collect();
                    theory.scope_euf_model_to_roots(&model_roots);
                    let (euf, arr, mut lia) = theory.extract_all_models_auflia();
                    theory.clear_euf_model_scope();
                    // Recover substituted Int values and fill-only equalities (#6737)
                    if let Some(model) = lia.as_mut() {
                        super::lia::recover_substituted_lia_values(
                            &this.ctx.terms, &var_subst, model,
                        );
                        super::lia::recover_lia_equalities_from_assertions(
                            &this.ctx.terms, &original_assertions, model,
                        );
                    }
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory
                        .take_learned_state()
                        .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                    let ds = theory.take_dioph_state().unwrap_or_default();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LRA theory with disequality split support (#6129).
    ///
    /// Uses the incremental split-loop pipeline so `NeedDisequalitySplit` from LRA
    /// disequalities can be handled via SAT-level case splits while reusing
    /// incremental SAT state across iterations.
    pub(in crate::executor) fn solve_auf_lra(&mut self) -> Result<SolveResult> {
        // NOTE: expand_select_store is NOT applied here because solve_auf_lra
        // does not have ITE lifting. The ITEs from expansion would not be properly
        // handled by the Tseitin encoder without lifting. See solve_auf_lia for
        // the full AUFLIA pipeline with expansion + ITE lifting (#6282).

        // Eager array axioms for AUFLRA (#4304, #5086, #6282).
        // Unlike AUFLIA, AUFLRA keeps eager ROW because the lazy ArraySolver
        // cannot derive index disequalities that require LRA reasoning
        // (e.g., y = x + 0.5 ⇒ x ≠ y). The eager ROW encoding puts the
        // disjunction (i = j ∨ ROW2-consequence) into SAT where LRA resolves it.
        //
        // Drain generated axioms to prevent phantom accumulation in push/pop (#6733).
        let axiom_start = self.ctx.assertions.len();
        self.run_array_axiom_full_fixpoint();
        let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();

        let original_assertions = self.ctx.assertions.clone();
        let mut assertions = original_assertions.clone();
        assertions.extend(generated_axioms);
        let proof_provenance =
            ProofProblemAssertionProvenance::passthrough(&original_assertions, &assertions);
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "AUFLRA",
                persistent_sat_field: persistent_sat,
                create_theory: TheoryCombiner::auf_lra(&this.ctx.terms),
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, arr, lra) = theory.extract_all_models_auflra();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (Vec::new(), empty_hash_set(), z4_lia::DiophState::default())
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve mixed BV + LIA formulas where the two theories are independent (#5356).
    ///
    /// Strategy: try the BV solver first (which handles `extract`, `concat`, etc.
    /// via eager bit-blasting). If it returns SAT, model validation checks that the
    /// Int constraints are also satisfied. If validation passes, the result is correct.
    /// If validation fails (model validation error from contradictory Int constraints),
    /// fall back to AUFLIA which handles Int constraints correctly (but treats BV ops
    /// as uninterpreted).
    ///
    /// This gives us BV completeness for SAT formulas while preserving Int soundness.
    pub(in crate::executor) fn solve_bv_lia_indep(&mut self) -> Result<SolveResult> {
        use crate::executor::theories::bv::BvSolveConfig;
        use crate::executor_types::ExecutorError;

        // Try BV solver first — it can evaluate extract/concat/etc.
        let bv_result = match self.solve_bv_core(BvSolveConfig::qf_bv(), &[]) {
            Ok(result) => result,
            Err(ExecutorError::ModelValidation(_)) => {
                // BV produced a SAT model but Int constraints were violated.
                // Fall back to AUFLIA which handles Int correctly.
                return self.solve_auf_lia();
            }
            Err(e) => return Err(e),
        };

        match bv_result {
            SolveResult::Sat => Ok(SolveResult::Sat),
            SolveResult::Unsat => Ok(SolveResult::Unsat),
            SolveResult::Unknown => {
                // BV solver couldn't decide (e.g., model could not be validated
                // but wasn't a hard violation). Fall back to AUFLIA.
                self.solve_auf_lia()
            }
        }
    }

    /// Assumption-based version of [`solve_bv_lia_indep`] for `check-sat-assuming`.
    pub(in crate::executor) fn solve_bv_lia_indep_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        use crate::executor::theories::bv::BvSolveConfig;
        use crate::executor_types::ExecutorError;

        let bv_result = match self.solve_bv_core(BvSolveConfig::qf_bv(), assumptions) {
            Ok(result) => result,
            Err(ExecutorError::ModelValidation(_)) => {
                return self.solve_auf_lia_with_assumptions(assertions, assumptions);
            }
            Err(e) => return Err(e),
        };

        match bv_result {
            SolveResult::Sat => Ok(SolveResult::Sat),
            SolveResult::Unsat => Ok(SolveResult::Unsat),
            SolveResult::Unknown => self.solve_auf_lia_with_assumptions(assertions, assumptions),
        }
    }
}
