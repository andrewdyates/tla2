// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portfolio solver for CHC
//!
//! Runs multiple CHC solving engines and returns the first result.
//! This mirrors the strategy used by Golem (CHC-COMP 2024 winner).
//!
//! # Engines
//!
//! - **PDR**: Property-Directed Reachability - good for proving safety
//! - **BMC**: Bounded Model Checking - good for finding bugs
//! - **LAWI**: Lazy Abstraction with Interpolants
//!
//! # Strategy
//!
//! Different engines excel at different problems:
//! - PDR: Strong at finding inductive invariants (UNSAT cases)
//! - BMC: Strong at finding counterexamples (SAT cases)
//!
//! Running both in parallel returns whichever finishes first.

mod accept;
mod bv_unsafe;
#[allow(dead_code)]
mod engines;
#[allow(dead_code)]
pub(crate) mod features;
mod preprocess;
mod schedule;
pub(crate) mod selector;
pub(crate) mod singleloop_safe;
mod trivial;
#[cfg(test)]
mod trl_validation_tests;
mod types;
mod validation;

use preprocess::problem_contains_recursive_bv_sorts;
pub(crate) use preprocess::PreprocessSummary;
#[cfg(test)]
use schedule::panic_message;
use types::EngineResult;
pub use types::{EngineConfig, PortfolioConfig, PortfolioResult};
use validation::{SafePrecheckResult, ValidationBudget, ValidationResult};

use crate::transform::{
    BackTranslator, BvToIntAbstractor, DeadParamEliminator, IdentityBackTranslator,
    TransformationPipeline,
};
use crate::{ChcProblem, ChcSort};

/// Portfolio solver for CHC problems
pub struct PortfolioSolver {
    /// Original problem (for validation)
    original_problem: ChcProblem,
    /// Transformed problem (for solving) - same as original if no preprocessing
    problem: ChcProblem,
    /// Back-translator for converting results back to original vocabulary
    back_translator: Box<dyn BackTranslator>,
    config: PortfolioConfig,
    /// Whether the original problem contains recursive BV sorts.
    /// When true, Unsafe results are confirmed against the original problem
    /// before the portfolio accepts them.
    bv_abstracted: bool,
}

impl Drop for PortfolioSolver {
    fn drop(&mut self) {
        // Use iterative teardown to avoid recursive Arc<ChcExpr> Drop
        // which can overflow the stack on deeply nested expression trees (#6847).
        std::mem::take(&mut self.original_problem).iterative_drop();
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl PortfolioSolver {
    fn should_try_algebraic_prepass(&self) -> bool {
        // Algebraic synthesis is fast (<100ms) and should run even with
        // timeouts. It handles polynomial invariants that engines cannot
        // discover (e.g., accumulator sum = i*(i-1)/2). Part of #7897.

        #[cfg(test)]
        if schedule::FORCE_SOLVER_THREAD_SPAWN_FAILURE.with(std::cell::Cell::get) {
            return false;
        }

        true
    }

    /// Try algebraic invariant synthesis from polynomial closed forms.
    ///
    /// First attempts on the original problem (Int-sorted predicates).
    /// If the problem has BV sorts, applies BvToBool + BvToInt + DeadParamElim
    /// (without LocalVarEliminator, which hides the self-loop structure) and
    /// retries on the Int-abstracted version. Part of #7931, #7170, #5651.
    ///
    /// Returns `Some(PortfolioResult::Safe(..))` if an invariant is found,
    /// `Some(PortfolioResult::Unsafe(..))` if algebraic synthesis proves
    /// bad states are reachable, or `None` if not applicable.
    fn try_algebraic_prepass(&self) -> Option<PortfolioResult> {
        use crate::algebraic_invariant::AlgebraicResult;
        use crate::pdr::counterexample::Counterexample;

        // Phase 1: try on original problem (works for Int-sorted CHC).
        match crate::algebraic_invariant::try_algebraic_solve(
            &self.original_problem,
            self.config.verbose,
        ) {
            AlgebraicResult::Safe(model) => {
                if self.config.verbose {
                    safe_eprintln!("Portfolio: Algebraic invariant synthesis succeeded (original)");
                }
                return self
                    .validate_algebraic_model(model)
                    .map(PortfolioResult::Safe);
            }
            AlgebraicResult::Unsafe => {
                if self.config.verbose {
                    safe_eprintln!("Portfolio: Algebraic synthesis detected UNSAFE (original)");
                }
                return Some(PortfolioResult::Unsafe(Counterexample {
                    steps: Vec::new(),
                    witness: None,
                }));
            }
            AlgebraicResult::NotApplicable => {}
        }

        // Phase 2: for BV problems, apply BvToInt abstraction (no BvToBool)
        // and retry. The recurrence module's strip_bv_wrapping removes
        // ITE/mod wrappers so analyze_transition sees the underlying linear
        // structure. Part of #7931.
        //
        // Check the ORIGINAL problem for BV sorts, not self.bv_abstracted:
        // bv_abstracted is false when BvToBool successfully bitblasts all BV
        // sorts during preprocessing, but the algebraic prepass needs the
        // BvToInt path regardless (BvToBool produces 96 Bool args which
        // algebraic synthesis cannot handle).
        if problem_contains_recursive_bv_sorts(&self.original_problem) {
            let bv_to_int_problem = self.bv_to_int_for_algebraic();
            match crate::algebraic_invariant::try_algebraic_solve(
                &bv_to_int_problem,
                self.config.verbose,
            ) {
                AlgebraicResult::Safe(model) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Algebraic invariant synthesis succeeded (BV-to-Int)"
                        );
                    }
                    return self
                        .validate_algebraic_model(model)
                        .map(PortfolioResult::Safe);
                }
                AlgebraicResult::Unsafe => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Algebraic synthesis detected UNSAFE (BV-to-Int)"
                        );
                    }
                    return Some(PortfolioResult::Unsafe(Counterexample {
                        steps: Vec::new(),
                        witness: None,
                    }));
                }
                AlgebraicResult::NotApplicable => {}
            }
        }

        None
    }

    /// Apply BvToInt + DeadParamElim to the original problem,
    /// WITHOUT BvToBool, LocalVarEliminator, or ClauseInliner.
    ///
    /// BvToBool would bitblast BV32 into 32 Bool arguments per variable,
    /// producing predicates with ~96 arguments that algebraic synthesis
    /// cannot analyze. BvToInt converts BV ops to Int with ITE/mod wrappers
    /// that strip_bv_wrapping (in recurrence::analyze_transition) removes.
    /// LocalVarEliminator rewrites head vars into compound expressions,
    /// hiding the simple self-loop form that algebraic extraction needs.
    /// Part of #7931.
    fn bv_to_int_for_algebraic(&self) -> ChcProblem {
        let pipeline = TransformationPipeline::new()
            .with(BvToIntAbstractor::new().with_verbose(self.config.verbose))
            .with(DeadParamEliminator::new().with_verbose(self.config.verbose));
        let result = pipeline.transform(self.original_problem.clone());
        result.problem
    }

    /// Validate an algebraic model and return it if valid.
    ///
    /// SOUNDNESS AUDIT (#7912, Gap C): Algebraic synthesis has its own
    /// internal validation (validate_model_with_algebraic_fallback) which
    /// checks body AND NOT(head) is UNSAT for every clause -- a complete
    /// inductive invariant check. This is strictly stronger than portfolio-level
    /// validate_safe_query_only() (which only checks query clauses) and
    /// equivalent to validate_safe() (which uses PDR's verify_model).
    ///
    /// Portfolio-level validate_safe() is intentionally NOT added here:
    /// 1. PDR's verify_model_with_budget may reject valid NIA invariants
    ///    (e.g., sum <= n*n) where SMT returns Unknown within 1.5s budget.
    /// 2. validate_safe_query_only() creates a PdrSolver instance which
    ///    can be expensive for the NIA problems algebraic synthesis targets.
    /// 3. The algebraic validator handles NIA incompleteness via concrete
    ///    evaluation fallback (#7688), which PDR's verifier does not.
    fn validate_algebraic_model(
        &self,
        model: crate::InvariantModel,
    ) -> Option<crate::InvariantModel> {
        // Defense-in-depth (#7912): query-only validation in debug builds
        // confirms the model excludes bad states, even though algebraic
        // validation already checked all clauses.
        //
        // Skip for problems with Array-sorted predicates: the portfolio's
        // query-only validation path (PdrSolver.verify_model_query_only)
        // does not handle Array-sorted variables correctly. The algebraic
        // validator has already verified all clauses via SMT.
        let has_array_preds = self.original_problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::Array(_, _)))
        });
        if !has_array_preds {
            debug_assert!(
                !matches!(
                    self.validate_safe_query_only(&model),
                    SafePrecheckResult::Invalid(_)
                ),
                "BUG: algebraic synthesis model failed portfolio query-only validation"
            );
        }
        Some(model)
    }

    fn should_run_engines_on_original_problem(&self) -> bool {
        self.problem.predicates().is_empty() && !self.original_problem.predicates().is_empty()
    }

    fn engine_problem(&self) -> &ChcProblem {
        if self.should_run_engines_on_original_problem() {
            &self.original_problem
        } else {
            &self.problem
        }
    }

    /// Create a new portfolio solver
    ///
    /// If `enable_preprocessing` is true, applies ClauseInliner to reduce
    /// the problem size before solving.
    pub(crate) fn new(problem: ChcProblem, config: PortfolioConfig) -> Self {
        if config.enable_preprocessing {
            let summary = PreprocessSummary::build(problem, config.verbose);
            Self::from_summary(summary, config)
        } else {
            let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
            Self {
                original_problem: problem.clone(),
                problem,
                back_translator: Box::new(IdentityBackTranslator),
                config,
                bv_abstracted,
            }
        }
    }

    /// Create a portfolio solver from a pre-computed preprocessing summary.
    ///
    /// Used by the adaptive layer to avoid re-running preprocessing when it
    /// needs to inspect post-preprocess features for routing (#5877).
    pub(crate) fn from_summary(summary: PreprocessSummary, config: PortfolioConfig) -> Self {
        Self {
            original_problem: summary.original_problem,
            problem: summary.transformed_problem,
            back_translator: summary.back_translator,
            config,
            bv_abstracted: summary.bv_abstracted,
        }
    }

    /// Solve the CHC problem using the portfolio strategy.
    ///
    /// Returns the raw `PortfolioResult` (a type alias for `ChcEngineResult`).
    /// All Safe results have been validated by `validate_result` within
    /// `solve_parallel`/`solve_sequential`/`try_solve_trivial`.
    ///
    /// For the verified public API, use `AdaptivePortfolio::solve()` which
    /// wraps results in `VerifiedChcResult`. Part of #5746.
    pub fn solve(&self) -> PortfolioResult {
        if self.config.engines.is_empty() {
            return PortfolioResult::Unknown;
        }

        // Check for trivial problems (e.g., all predicates inlined away)
        if let Some(result) = self.try_solve_trivial() {
            return result;
        }

        if z4_core::TermStore::global_memory_exceeded() {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Global memory budget already exceeded before engine launch"
                );
            }
            return PortfolioResult::Unknown;
        }

        // Fast algebraic invariant synthesis from polynomial closed forms.
        // Runs on the ORIGINAL problem shape, not the fully preprocessed one:
        // LocalVarEliminator rewrites head vars into expressions, which hides
        // the simple self-loop form the algebraic extractor expects.
        // Part of #7170, #5651, #1753.
        if self.should_try_algebraic_prepass() {
            if let Some(result) = self.try_algebraic_prepass() {
                return result;
            }
        }

        if self.config.parallel && self.config.engines.len() > 1 {
            self.solve_parallel()
        } else {
            self.solve_sequential()
        }
    }

    /// Panic-safe variant of [`solve`](Self::solve).
    ///
    /// Catches z4-internal panics and returns them as [`ChcError::Internal`].
    /// Non-z4 panics propagate normally via `resume_unwind`.
    ///
    /// # Errors
    ///
    /// Returns [`ChcError::Internal`] if a z4-classified panic is caught.
    pub fn try_solve(&self) -> crate::ChcResult<PortfolioResult> {
        z4_core::catch_z4_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.solve())),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
    }

    // validate_safe, validate_safe_with_mode, tautological_negated_query_reason,
    // validate_safe_query_only, canonical_arg_sort, validate_unsafe,
    // validate_result, convert_engine_result are in validation.rs
}

#[cfg(test)]
mod tests;
