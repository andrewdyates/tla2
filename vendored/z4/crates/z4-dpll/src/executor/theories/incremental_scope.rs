// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental scope helpers for combined theory solving.
//!
//! These helpers manage temporary assertion swaps and deferred model
//! postprocessing during combined theory routes (AUFLIA, LIRA, AUFLIRA).
//! Extracted from `combined.rs` to keep the solve routes focused on
//! theory-specific logic (#6731).

use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalTheoryState;
use z4_core::TermId;

use super::super::Executor;
use super::solve_harness::ProofProblemAssertionProvenance;

impl Executor {
    /// Run a closure with a fresh `IncrementalTheoryState`, restoring the
    /// original state afterward.
    ///
    /// Combined theory routes (UF+LRA, AUFLIA, …) each need an isolated
    /// split-loop that does not interfere with the outer incremental state
    /// used by `push`/`pop`.
    ///
    /// If `assertions` is `Some(new_assertions)`, the executor assertion list
    /// is also temporarily replaced for the duration of the closure.
    pub(in crate::executor) fn with_isolated_incremental_state<F>(
        &mut self,
        assertions: Option<Vec<TermId>>,
        f: F,
    ) -> Result<SolveResult>
    where
        F: FnOnce(&mut Self) -> Result<SolveResult>,
    {
        let saved_state = self.incr_theory_state.take();
        self.incr_theory_state = Some(IncrementalTheoryState::new());
        let saved_assertions = assertions
            .map(|new_assertions| std::mem::replace(&mut self.ctx.assertions, new_assertions));
        let result = f(self);
        if let Some(original_assertions) = saved_assertions {
            self.ctx.assertions = original_assertions;
        }
        self.incr_theory_state = saved_state;
        result
    }

    /// Solve with temporary preprocessed assertions while deferring model
    /// postprocessing (minimization + validation) to the outer executor boundary.
    ///
    /// Combined theory routes (AUFLIA, LIRA, AUFLIRA) install preprocessed
    /// assertions before solving, but model validation must run against the
    /// *original* assertion set. This helper:
    ///
    /// 1. Saves and replaces assertions with `temporary_assertions`
    /// 2. Suppresses inner minimization (`CounterexampleStyle::Any`) and inner
    ///    validation (`skip_model_eval = true`) so `solve_and_store_model_with_theories`
    ///    stores the model without postprocessing
    /// 3. Calls `with_isolated_incremental_state(None, f)` for the actual solve
    /// 4. Restores assertions and flags after the solve returns
    /// 5. Leaves `last_model_validated = false` so `check_sat()` /
    ///    `check_sat_assuming()` runs validation on the restored assertions
    ///
    /// Fixes #6731: inner validation against preprocessed assertions degraded
    /// trivially SAT AUFLIA formulas to `unknown`.
    pub(in crate::executor) fn with_deferred_postprocessing<F>(
        &mut self,
        temporary_assertions: Vec<TermId>,
        proof_provenance: ProofProblemAssertionProvenance,
        f: F,
    ) -> Result<SolveResult>
    where
        F: FnOnce(&mut Self) -> Result<SolveResult>,
    {
        // Save assertion-view-sensitive state
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, temporary_assertions);
        let saved_style = self.counterexample_style;
        let saved_skip = self.skip_model_eval;
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();

        // Suppress inner minimization (CounterexampleStyle::Any makes
        // minimize_counterexamples_enabled() return false) and inner
        // validation (skip_model_eval makes finalize_sat_model_validation
        // return Ok(Sat) immediately).
        self.counterexample_style = crate::CounterexampleStyle::Any;
        self.skip_model_eval = true;
        self.proof_problem_assertion_provenance = Some(proof_provenance);

        // Solve with isolated incremental state (None = no second assertion swap)
        let result = self.with_isolated_incremental_state(None, f);

        // Restore original state
        self.ctx.assertions = saved_assertions;
        self.counterexample_style = saved_style;
        self.skip_model_eval = saved_skip;
        if !matches!(result, Ok(SolveResult::Unsat)) {
            self.proof_problem_assertion_provenance = saved_proof_provenance;
        }

        // Run deferred minimization against restored assertions if applicable
        if matches!(result, Ok(SolveResult::Sat))
            && self.minimize_counterexamples_enabled()
            && self.last_assumptions.is_none()
        {
            self.minimize_model_sat_preserving();
        }

        // Ensure outer boundary runs validation on restored assertions
        self.last_model_validated = false;

        result
    }
}
