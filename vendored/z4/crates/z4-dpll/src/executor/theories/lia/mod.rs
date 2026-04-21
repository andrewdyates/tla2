// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear Integer Arithmetic (LIA) and Non-Linear Integer Arithmetic (NIA) solving.

#[cfg(test)]
mod tests;

use std::sync::atomic::Ordering;
use std::time::Instant;

use z4_core::TermId;
use z4_lia::{LiaModel, LiaSolver};
use z4_nia::NiaSolver;

use super::super::Executor;
// Re-export so `super::lia::recover_*` paths in combined.rs continue to work.
pub(in crate::executor) use super::lia_eval::{
    recover_lia_equalities_from_assertions, recover_substituted_lia_values,
};
use super::MAX_SPLITS_LIA;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::VariableSubstitution;

impl Executor {
    /// Solve QF_LIA through the dedicated LIA split-loop pipeline.
    ///
    /// Standalone QF_LIA uses eager theory-SAT interleaving on the dedicated
    /// `lia_*` SAT/Tseitin state so bound and simplex propagations can prune
    /// search during BCP. Incremental push/pop sessions stay on the lazy arm
    /// because the eager split-loop currently requires isolated scope depth 0.
    pub(in crate::executor) fn solve_lia(&mut self) -> Result<SolveResult> {
        self.solve_lia_incremental()
    }

    /// Solve QF_LIA incrementally using SAT scope selectors.
    ///
    /// Maintains persistent Tseitin mappings and SAT solver across check-sat calls.
    /// Scopes branch-and-bound split clauses to each `check-sat` via push/pop.
    /// Uses `solve_incremental_split_loop_pipeline!` for the DPLL(T) loop with
    /// branch-and-bound splits (NeedSplit, NeedDisequalitySplit, NeedExpressionSplit).
    pub(in crate::executor) fn solve_lia_incremental(&mut self) -> Result<SolveResult> {
        let original_problem_assertions = self.ctx.assertions.clone();
        let artifacts = self.preprocess_lia_artifacts();
        let current_scope_depth = self
            .incr_theory_state
            .as_ref()
            .map_or(0, |state| state.scope_depth);
        let source_depths = self.ctx.active_assertion_min_scope_depths();
        let mut derived_assertion_entries = Vec::new();
        for (&term, source_sets) in &artifacts.assertion_sources {
            for sources in source_sets {
                let activation_depth = sources
                    .iter()
                    .map(|source| {
                        source_depths
                            .get(source)
                            .copied()
                            .unwrap_or(current_scope_depth)
                    })
                    .max()
                    .unwrap_or(current_scope_depth);
                derived_assertion_entries.push((term, activation_depth, sources.clone()));
            }
        }

        {
            let state = self
                .incr_theory_state
                .get_or_insert_with(crate::incremental_state::IncrementalTheoryState::new);
            state.replace_lia_derived_assertions(derived_assertion_entries);
            state.retain_encoded_assertions(&artifacts.assertions);
        }

        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &artifacts.assertions,
            artifacts.assertion_sources.clone(),
        );

        // Packet 1 (#6698): Suppress minimization while the preprocessed
        // assertions are installed. The minimizer must run against the original
        // user-facing formula after substituted variables are recovered.
        let saved_style = self.counterexample_style();
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        self.set_counterexample_style(crate::CounterexampleStyle::Any);
        self.proof_problem_assertion_provenance = Some(proof_provenance);

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, artifacts.assertions);
        let mut result = self.solve_lia_incremental_inner(Some(&artifacts.var_subst));

        // Restore original assertions and counterexample style before model
        // recovery and validation against the user-visible formula.
        self.ctx.assertions = original_assertions;
        self.set_counterexample_style(saved_style);
        if !matches!(result, Ok(SolveResult::Unsat)) {
            self.proof_problem_assertion_provenance = saved_proof_provenance;
        }

        if matches!(result, Ok(SolveResult::Sat)) {
            if let Some(model) = self
                .last_model
                .as_mut()
                .and_then(|model| model.lia_model.as_mut())
            {
                recover_substituted_lia_values(&self.ctx.terms, &artifacts.var_subst, model);
                recover_lia_equalities_from_assertions(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                    model,
                );
            }

            if self.minimize_counterexamples_enabled() && self.last_assumptions.is_none() {
                self.minimize_model_sat_preserving();
            }
            self.last_model_validated = false;
            result = self.finalize_sat_model_validation();
        }

        result
    }

    /// Solve QF_LIA with assumptions through the dedicated LIA pipeline (#6728).
    ///
    /// Applies the same preprocessing family as `solve_lia_incremental()`:
    /// VariableSubstitution, NormalizeArithSom, ITE lifting, mod/div elimination.
    /// Assumptions get the same treatment while preserving original-term identity
    /// for UNSAT-core and proof reporting.
    pub(in crate::executor) fn solve_lia_with_assumptions(
        &mut self,
        _assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        // Note: _assertions param preserved for API parity with other assumption
        // solvers. Assertions come from self.ctx.assertions via preprocess_lia_artifacts().

        // Validate: all assumptions must be Bool-sorted.
        // Non-Bool assumptions are user errors that should surface as InternalError
        // (the API layer catches Err and maps to Unknown/InternalError).
        for &a in assumptions {
            if *self.ctx.terms.sort(a) != z4_core::Sort::Bool {
                return Err(crate::executor_types::ExecutorError::Dpll(
                    crate::DpllError::UnexpectedTheoryResult,
                ));
            }
        }

        // Preprocess assertions (same family as plain check-sat)
        let mut artifacts = self.preprocess_lia_artifacts();

        // Preprocess assumptions using the same VariableSubstitution
        let assume_result = self.preprocess_lia_assumptions(assumptions, &mut artifacts.var_subst);

        // Merge constraint assertions from assumption mod/div elimination
        let mut all_assertions = artifacts.assertions;
        all_assertions.extend(assume_result.extra_assertions);

        let var_subst = artifacts.var_subst;
        let final_assumptions = assume_result.assumptions;
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            self.ctx.assertions.clone(),
            &all_assertions,
            artifacts.assertion_sources.clone(),
        );

        self.with_deferred_postprocessing(all_assertions, proof_provenance, |this| {
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "LIA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: LiaSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    use super::solve_harness::TheoryModels;
                    let mut lia = theory.extract_model();
                    if let Some(model) = lia.as_mut() {
                        recover_substituted_lia_values(&this.ctx.terms, &var_subst, model);
                        recover_lia_equalities_from_assertions(
                            &this.ctx.terms,
                            &this.ctx.assertions,
                            model,
                        );
                    }
                    TheoryModels { lia, ..TheoryModels::default() }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(
                        std::mem::take(lc),
                        std::mem::take(hc),
                    );
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(Ordering::Relaxed))
                    || solve_deadline.is_some_and(|dl| Instant::now() >= dl)
                }
            )
        })
    }

    fn solve_lia_incremental_inner(
        &mut self,
        var_subst: Option<&VariableSubstitution>,
    ) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;

        // #6853: LIA preprocessing can change the assertion set between
        // check-sats, creating different Tseitin encodings each time.
        // Accumulated global definition clauses from prior check-sats
        // over-constrain the variable space, causing false UNSAT when
        // combined with the current formula's activation clauses.
        //
        // Fix: reset the LIA-specific SAT solver and encoding state so
        // each check-sat starts clean. The LIA pipeline uses dedicated
        // lia_* fields (not the shared fields) to avoid interference
        // with EUF/LRA's persistent state.
        self.incr_theory_state
            .get_or_insert_with(crate::incremental_state::IncrementalTheoryState::new)
            .reset_lia_sat();

        // Only the standalone QF_LIA lane gets eager theory propagation.
        // Once a session has entered push/pop incremental mode, keep using
        // the lazy arm even if the scope depth later returns to 0.
        if !self.incremental_mode {
            return solve_incremental_split_loop_pipeline!(self,
                tag: "LIA",
                persistent_sat_field: lia_persistent_sat,
                tseitin_field: lia_tseitin_state,
                encoded_field: lia_encoded_assertions,
                activation_scope_field: lia_assertion_activation_scope,
                create_theory: LiaSolver::new(&self.ctx.terms),
                extract_models: |theory| {
                    use super::solve_harness::TheoryModels;
                    let mut lia = theory.extract_model();
                    if let (Some(var_subst), Some(model)) = (var_subst, lia.as_mut()) {
                        recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
                    }
                    TheoryModels { lia, ..TheoryModels::default() }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(
                        std::mem::take(lc),
                        std::mem::take(hc),
                    );
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(Ordering::Relaxed))
                    || solve_deadline.is_some_and(|dl| Instant::now() >= dl)
                }
            );
        }

        solve_incremental_split_loop_pipeline!(self,
            tag: "LIA",
            persistent_sat_field: lia_persistent_sat,
            tseitin_field: lia_tseitin_state,
            encoded_field: lia_encoded_assertions,
            activation_scope_field: lia_assertion_activation_scope,
            create_theory: LiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                let mut lia = theory.extract_model();
                if let (Some(var_subst), Some(model)) = (var_subst, lia.as_mut()) {
                    recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
                }
                TheoryModels { lia, ..TheoryModels::default() }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(
                    std::mem::take(lc),
                    std::mem::take(hc),
                );
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || solve_deadline.is_some_and(|dl| Instant::now() >= dl)
            }
        )
    }

    /// Solve using non-linear integer arithmetic (NIA) theory.
    ///
    /// Uses the split-loop pipeline so that NeedSplit from the underlying
    /// LIA branch-and-bound solver is handled correctly. Without splits,
    /// NIA immediately returns Unknown on any NeedSplit (#7920).
    pub(in crate::executor) fn solve_nia(&mut self) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;

        solve_incremental_split_loop_pipeline!(self,
            tag: "NIA",
            persistent_sat_field: persistent_sat,
            create_theory: NiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                let lia_model = theory
                    .extract_model()
                    .map(|m| LiaModel { values: m.values });
                TheoryModels {
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(
                    std::mem::take(lc),
                    std::mem::take(hc),
                );
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || solve_deadline.is_some_and(|dl| Instant::now() >= dl)
            }
        )
    }
}
