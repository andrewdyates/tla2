// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIRA and AUFLIRA combined theory solving (mixed Int + Real arithmetic).
//!
//! Non-LIRA theory combinations (UF+LRA, UF+NRA, AUFLIA, AUFLRA, BV+LIA)
//! are in the parent module.

use crate::combined_solvers::{AufLiraSolver, LiraSolver};
use crate::executor::theories::solve_harness::{ProofProblemAssertionProvenance, TheoryModels};
use crate::executor_types::{Result, SolveResult};
use z4_core::TermId;

use super::super::super::Executor;
use super::super::MAX_SPLITS_MIXED;

impl Executor {
    /// Solve using combined LIA + LRA theory with assumptions (QF_LIRA).
    ///
    /// This is the assumption-based version of [`Self::solve_lira`], enabling
    /// split-aware `check-sat-assuming` for mixed Int/Real problems.
    ///
    /// Fixes #1835: `check-sat-assuming` must handle `NeedSplit`/`NeedDisequalitySplit`
    /// for LIRA-family logics instead of returning `unknown`.
    pub(in crate::executor) fn solve_lira_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        // Preprocess assertions and assumptions through the full LIA normalization
        // family: variable substitution, SOM, ITE lifting, mod/div elimination (#6737).
        let artifacts = self.preprocess_mixed_arith_assumptions(assertions, assumptions);
        let var_subst = artifacts.var_subst;
        let final_assumptions = artifacts.assumptions;
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &artifacts.assertions,
            artifacts.assertion_sources,
        );

        // Preserve original assertions for fill-only equality recovery on SAT.
        let original_assertions: Vec<TermId> = assertions.to_vec();

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(artifacts.assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "LIRA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: LiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (mut lia, lra) = theory.extract_models();
                    // Recover substituted Int values and fill-only equalities (#6737)
                    if let Some(model) = lia.as_mut() {
                        super::super::lia::recover_substituted_lia_values(
                            &this.ctx.terms, &var_subst, model,
                        );
                        super::super::lia::recover_lia_equalities_from_assertions(
                            &this.ctx.terms, &original_assertions, model,
                        );
                    }
                    TheoryModels {
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
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
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LIA + LRA theory with assumptions (QF_AUFLIRA).
    ///
    /// Fixes #1835: `check-sat-assuming` must handle integer/disequality splits for AUFLIRA.
    pub(in crate::executor) fn solve_auflira_with_assumptions(
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

        let assumption_terms: Vec<TermId> = final_assumptions.iter().map(|(t, _)| *t).collect();
        let mut final_assertions = artifacts.assertions;

        // Eager array axioms for AUFLIRA-ASSUME (#4304, #5086, #6282).
        // Keeps eager ROW because LRA index arithmetic disequalities
        // cannot be derived by the lazy ArraySolver alone.
        // Include assumption terms in the reachable set (#6736).
        {
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at_with_roots(axiom_start, &assumption_terms);
            final_assertions.extend(self.ctx.assertions.drain(axiom_start..));
        }
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &final_assertions,
            artifacts.assertion_sources,
        );

        // Use isolated incremental state with the new incremental assumption
        // split-loop macro (#6689 Packet 4). LIA learned state is now preserved
        // across split iterations — an improvement over the legacy path.
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(final_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "AUFLIRA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: AufLiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, arr, mut lia, lra) = theory.extract_all_models();
                    // Recover substituted Int values and fill-only equalities (#6737)
                    if let Some(model) = lia.as_mut() {
                        super::super::lia::recover_substituted_lia_values(
                            &this.ctx.terms, &var_subst, model,
                        );
                        super::super::lia::recover_lia_equalities_from_assertions(
                            &this.ctx.terms, &original_assertions, model,
                        );
                    }
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
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
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined LIA + LRA theory (QF_LIRA)
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for mixed Int+Real problems.
    pub(in crate::executor) fn solve_lira(&mut self) -> Result<SolveResult> {
        let (preprocessed_assertions, proof_provenance) =
            self.preprocess_mod_div_assertions_with_proof_provenance(&self.ctx.assertions.clone());

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "LIRA",
                persistent_sat_field: persistent_sat,
                create_theory: LiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (lia, lra) = theory.extract_models();
                    TheoryModels {
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                // #5462: LIRA stays on lazy path. Cross-sort NeedSplit requires
                // the N-O fixpoint to run inside the SAT solve (extension check),
                // but the eager arm's theory recreation loses cross-sort state
                // between iterations. The extension fix (returning Sat for
                // NeedSplit) helps but doesn't fully resolve multi-split SAT
                // problems that depend on cross-sort bound propagation.
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LIA + LRA theory (QF_AUFLIRA)
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for mixed Int+Real problems.
    pub(in crate::executor) fn solve_auflira(&mut self) -> Result<SolveResult> {
        let (mut preprocessed_assertions, mut proof_provenance) =
            self.preprocess_mod_div_assertions_with_proof_provenance(&self.ctx.assertions.clone());

        // NOTE: expand_select_store is NOT applied here — solve_auflira does not
        // have ITE lifting. See solve_auf_lia for the full pipeline (#6282).

        // Eager array axioms for soundness (#4304, #5086, #6282)
        {
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at(axiom_start);
            preprocessed_assertions.extend(self.ctx.assertions.drain(axiom_start..));
        }
        proof_provenance = ProofProblemAssertionProvenance::from_sources(
            proof_provenance.original_problem_assertions,
            &preprocessed_assertions,
            proof_provenance.assertion_sources,
        );

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "AUFLIRA",
                persistent_sat_field: persistent_sat,
                create_theory: AufLiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, arr, lia, lra) = theory.extract_all_models();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
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
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }
}
