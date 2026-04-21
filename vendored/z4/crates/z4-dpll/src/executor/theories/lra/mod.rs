// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear Real Arithmetic (LRA) solving.

use z4_core::TermId;
use z4_lra::LraSolver;
use z4_sat::Solver as SatSolver;

use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalTheoryState;
use crate::preprocess::{FlattenAnd, NormalizeArithSom, PreprocessingPass};
use crate::PhaseTimer;

use super::super::Executor;
use super::MAX_SPLITS_LRA;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

impl Executor {
    fn preprocess_lra_assertions(&mut self) -> Vec<TermId> {
        // Keep the dedicated QF_LRA entrypoint aligned with the generic
        // arithmetic preprocessing used by the shared theory harness.
        let mut assertions = self.ctx.assertions.clone();
        let mut flatten_pass = FlattenAnd::new();
        flatten_pass.apply(&mut self.ctx.terms, &mut assertions);

        let mut som_pass = NormalizeArithSom::new();
        som_pass.apply(&mut self.ctx.terms, &mut assertions);

        let assertions = self.ctx.terms.decompose_arithmetic_eq_all(&assertions);
        let assertions = self.ctx.terms.decompose_disequality_all(&assertions);
        let assertions = self.ctx.terms.rewrite_cardinality_constraints(&assertions);
        self.ctx.terms.lift_arithmetic_ite_all(&assertions)
    }

    pub(in crate::executor) fn solve_lra(&mut self) -> Result<SolveResult> {
        // Push/pop incremental mode uses the persistent no-split incremental
        // pipeline (solve_incremental_theory_pipeline!). Standalone QF_LRA
        // uses the incremental split-loop path for disequality splits. Both
        // routes are proof-capable on committed HEAD; the difference is
        // routing, not proof availability.
        if self.incremental_mode {
            return self.solve_lra_incremental();
        }

        self.solve_lra_standalone_incremental()
    }

    /// Solve QF_LRA using the incremental split-loop pipeline with a local state.
    ///
    /// This uses `solve_incremental_split_loop_pipeline!` (the same macro as QF_LIA)
    /// to eliminate the full DpllT rebuild on each NeedDisequalitySplit. The SAT solver
    /// persists across split iterations, retaining all learned clauses, VSIDS scores,
    /// and phase saving.
    ///
    /// State isolation (#4919 design): Uses a temporary `IncrementalTheoryState` that
    /// is swapped into `self.incr_theory_state` for the duration of the solve, then
    /// discarded. This prevents the split-loop path from contaminating the push/pop
    /// incremental state when proof-enabled scripts route here (#6660).
    fn solve_lra_standalone_incremental(&mut self) -> Result<SolveResult> {
        let mut preprocess_time = std::time::Duration::default();
        let lifted_assertions = {
            let _preprocess_timer = PhaseTimer::new(&mut preprocess_time);
            self.preprocess_lra_assertions()
        };

        // Swap in a temporary isolated state for the standalone solve.
        // The macro reads from self.incr_theory_state, so we temporarily
        // replace it. The original state is restored after the solve.
        let saved_state = self.incr_theory_state.take();
        let mut temp_state = IncrementalTheoryState::new();

        // Pre-create the SAT solver with Z3-style geometric restarts and
        // random variable frequency. The macro's pipeline_incremental_setup!
        // will find this solver via state.persistent_sat and reuse it
        // (calling ensure_num_vars to resize). Without this, the standalone
        // path uses CaDiCaL-style stabilization restarts which are less
        // effective for theory-heavy QF_LRA benchmarks.
        {
            let random_seed = self.current_random_seed();
            let mut sat = SatSolver::new(0);
            sat.set_random_seed(random_seed);
            sat.set_geometric_restarts(100.0, 1.1);
            sat.set_random_var_freq(0.01);
            if let Some(seed) = self.random_seed {
                sat.set_random_seed(seed);
            }
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            z4_sat::TlaTraceable::maybe_enable_tla_trace_from_env(&mut sat);
            if self.produce_proofs_enabled() {
                sat.enable_clause_trace();
            }
            temp_state.persistent_sat = Some(sat);
        }
        self.incr_theory_state = Some(temp_state);

        // Install preprocessed assertions for the macro to read.
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, lifted_assertions);

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;

        let result = solve_incremental_split_loop_pipeline!(self,
            tag: "LRA",
            persistent_sat_field: persistent_sat,
            create_theory: LraSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                use super::solve_harness::TheoryModels;
                TheoryModels {
                    lra: Some(theory.extract_model()),
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LRA,
            pre_theory_import: |_theory, _lc, _hc, _ds| {
                // LRA has no integer-specific learned state to import.
            },
            post_theory_export: |_theory| {
                // LRA has no integer-specific learned state to export.
                (vec![], Default::default(), Default::default())
            },
            // #6590 Packet 3: Keep LraSolver alive across iterations with warm
            // simplex basis. soft_reset clears assertion/bound state; values
            // preserved by soft_reset_warm once correctness is verified.
            persistent_theory: true,
            // #6586: Enable eager theory-SAT interleaving via TheoryExtension.
            eager_extension: true,
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
            }
        );

        // Restore original state: discard the temporary state, put the original back.
        self.incr_theory_state = saved_state;
        self.ctx.assertions = original_assertions;

        self.last_statistics
            .set_float("time.construct.preprocess", preprocess_time.as_secs_f64());
        result
    }

    /// Solve QF_LRA incrementally using SAT scope selectors.
    ///
    /// This method maintains a persistent SAT solver and TseitinState that retain
    /// learned clauses and term-to-var mappings across check-sat calls.
    /// Uses SAT scope selectors (push/pop) for correct scoping of assertion activations
    /// while keeping definitional clauses global for sound cached term→var reuse (#1432).
    pub(in crate::executor) fn solve_lra_incremental(&mut self) -> Result<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "LRA",
            create_theory: LraSolver::new(&self.ctx.terms),
            extract_models: |theory| TheoryModels {
                lra: Some(theory.extract_model()),
                ..TheoryModels::default()
            },
            track_theory_stats: true,
            set_unknown_on_error: true,
            pre_sat_solve: |sat_solver, _term_to_var| {
                sat_solver.set_geometric_restarts(100.0, 1.1);
                sat_solver.set_random_var_freq(0.01);
            }
        )
    }
}
