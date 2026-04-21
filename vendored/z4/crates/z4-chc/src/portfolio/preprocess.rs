// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing pipeline for CHC portfolio solving.
//!
//! Builds a [`PreprocessSummary`] capturing the transformed problem and metadata
//! needed by the adaptive routing layer and portfolio engine dispatch.

use crate::transform::{
    BackTranslator, BvToBoolBitBlaster, BvToIntAbstractor, ClauseInliner, CompositeBackTranslator,
    DeadParamEliminator, IdentityBackTranslator, LocalVarEliminator, TransformationPipeline,
};
use crate::{ChcProblem, ChcSort};

pub(crate) fn sort_contains_recursive_bv(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::BitVec(_) => true,
        ChcSort::Array(key, value) => {
            sort_contains_recursive_bv(key.as_ref()) || sort_contains_recursive_bv(value.as_ref())
        }
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::Uninterpreted(_)
        | ChcSort::Datatype { .. } => false,
    }
}

pub(crate) fn problem_contains_recursive_bv_sorts(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(sort_contains_recursive_bv)
}

/// Summary of preprocessing results for reuse between adaptive routing and solving.
///
/// After BvToBool/BvToInt/ClauseInliner/etc., this captures the transformed
/// problem plus metadata needed to route to the correct engine portfolio.
/// Part of #5877: avoids re-running preprocessing when the adaptive layer
/// needs post-preprocess classification.
pub(crate) struct PreprocessSummary {
    pub(crate) original_problem: ChcProblem,
    pub(crate) transformed_problem: ChcProblem,
    pub(crate) back_translator: Box<dyn BackTranslator>,
    pub(crate) bv_abstracted: bool,
}

impl PreprocessSummary {
    /// Run the standard preprocessing pipeline and compute metadata.
    pub(crate) fn build(problem: ChcProblem, verbose: bool) -> Self {
        // Stage 0: Remove dead params BEFORE bit-blasting (saves 8× per dead BV(8))
        let pre_pipeline =
            TransformationPipeline::new().with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(problem.clone());

        // Stage 1: BvToBool (exact bit-blasting) on pre-cleaned problem
        let bvtobool_pipeline =
            TransformationPipeline::new().with(BvToBoolBitBlaster::new().with_verbose(verbose));
        let bvtobool_result = bvtobool_pipeline.transform(pre_result.problem);

        // BvToBool is exact: if it eliminated all BV sorts, the problem is
        // faithfully represented in Bool domain. BvToInt (stage 2) only
        // handles BV sorts that survived BvToBool (width > 64 or Array
        // sub-sorts). Only BvToInt introduces an over-approximation.
        let bv_remains_after_bitblast =
            problem_contains_recursive_bv_sorts(&bvtobool_result.problem);

        // Stage 2: BvToInt + cleanup (may over-approximate remaining BV sorts)
        let cleanup_pipeline = TransformationPipeline::new()
            .with(BvToIntAbstractor::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(ClauseInliner::new().with_verbose(verbose));
        // Note: BvToInt-only path (skipping BvToBool) was tested (#5877) but
        // regresses BV score from 17/205 to ~1/205 — the ITE-heavy modular
        // arithmetic encoding from BvToInt overwhelms LIA engines. Recovering
        // harder BV benchmarks (nested4, simple) requires native BV theory in
        // PDR (like Z3 Spacer) rather than a routing change.
        let result = cleanup_pipeline.transform(bvtobool_result.problem);

        // (#7048) Mod/div expansion is done per-engine (PDR) rather than at portfolio
        // level, because Euclidean axioms add fresh variables that can hurt PDKind/TPA
        // convergence on benchmarks like const_mod_3, dillig22_m, s_multipl_17.

        // Compose back-translators: cleanup (innermost) then bvtobool then pre-elim (outermost)
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![
                result.back_translator,
                bvtobool_result.back_translator,
                pre_result.back_translator,
            ],
        });

        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = result.problem.clauses().len();
            let orig_preds = problem.predicates().len();
            let new_preds = result.problem.predicates().len();
            safe_eprintln!(
                "Portfolio: Preprocessing reduced {} clauses -> {}, {} predicates -> {}",
                orig_clauses,
                new_clauses,
                orig_preds,
                new_preds
            );
        }
        // Only set bv_abstracted if BvToInt had to handle BV sorts that
        // BvToBool couldn't (exact) bit-blast. BvToBool is exact, so if it
        // handled everything, no over-approximation is in effect.
        let bv_abstracted = bv_remains_after_bitblast;
        // Detect pure-Boolean state: all predicate args are Bool or Int after
        // preprocessing. This is the signature of a successfully bit-blasted BV
        // problem that should skip interpolation-heavy engines (#5877).
        let pure_boolean_after_preprocess = result.problem.predicates().iter().all(|p| {
            p.arg_sorts
                .iter()
                .all(|s| matches!(s, ChcSort::Bool | ChcSort::Int))
        });
        if verbose {
            if bv_abstracted {
                safe_eprintln!(
                    "Portfolio: Original problem contains recursive BV sorts — Unsafe results require original-domain confirmation"
                );
            }
            if pure_boolean_after_preprocess {
                safe_eprintln!(
                    "Portfolio: Post-preprocess problem is pure Boolean+Int — Boolean lane eligible"
                );
            }
        }
        Self {
            original_problem: problem,
            transformed_problem: result.problem,
            back_translator,
            bv_abstracted,
        }
    }

    /// Build a BvToInt-only preprocessing pipeline (no BvToBool bit-blasting).
    ///
    /// Converts BV predicates to integer arithmetic, preserving the original
    /// variable count (no state-space explosion). Used as a parallel lane
    /// alongside BvToBool: BvToInt produces compact LIA problems solvable by
    /// TPA/PDR/PDKIND, while BvToBool works for problems needing bit-level
    /// reasoning (#5877).
    pub(crate) fn build_int_only(problem: ChcProblem, verbose: bool) -> Self {
        // Stage 0: Remove dead params BEFORE BvToInt (reduces arity before conversion)
        let pre_pipeline =
            TransformationPipeline::new().with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(problem.clone());

        // Use exact BvToInt here so Safe results remain sound in the original
        // BV domain. The relaxed encoding is unsound under signed overflow
        // (#6848) and must stay test-only.
        let pipeline = TransformationPipeline::new()
            .with(BvToIntAbstractor::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(ClauseInliner::new().with_verbose(verbose));
        let result = pipeline.transform(pre_result.problem);
        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = result.problem.clauses().len();
            safe_eprintln!(
                "Portfolio: BvToInt-only preprocessing: {} clauses -> {}",
                orig_clauses,
                new_clauses
            );
        }
        let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
        // Compose back-translators: pipeline (inner) then pre-elim (outer)
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![result.back_translator, pre_result.back_translator],
        });
        Self {
            original_problem: problem,
            transformed_problem: result.problem,
            back_translator,
            bv_abstracted,
        }
    }

    /// Build a relaxed BvToInt preprocessing pipeline (no modular wrapping).
    ///
    /// Maps BV arithmetic to unbounded integer arithmetic, producing simpler LIA
    /// constraints without the mod/div overhead of exact BvToInt. This enables
    /// faster invariant discovery for BV64 problems where overflow is uncommon
    /// (#4198).
    ///
    /// **Soundness**: relaxed BvToInt is UNSOUND under signed overflow (#6848).
    /// Callers MUST validate Safe results against the original BV problem before
    /// accepting them. Invalid invariants (where overflow matters) will fail
    /// validation and fall through to the exact path.
    pub(crate) fn build_int_relaxed(problem: ChcProblem, verbose: bool) -> Self {
        let pre_pipeline =
            TransformationPipeline::new().with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(problem.clone());

        let pipeline = TransformationPipeline::new()
            .with(
                BvToIntAbstractor::new()
                    .with_verbose(verbose)
                    .with_relaxed(true),
            )
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(ClauseInliner::new().with_verbose(verbose));
        let result = pipeline.transform(pre_result.problem);
        if verbose {
            safe_eprintln!(
                "Portfolio: BvToInt-relaxed preprocessing: {} clauses -> {}",
                problem.clauses().len(),
                result.problem.clauses().len()
            );
        }
        let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![result.back_translator, pre_result.back_translator],
        });
        Self {
            original_problem: problem,
            transformed_problem: result.problem,
            back_translator,
            bv_abstracted,
        }
    }

    /// Build a BV-native preprocessing pipeline (no BV transforms at all).
    ///
    /// Preserves the original BV sorts and operations, applying only non-BV
    /// transforms (local var elimination, dead param elimination, clause
    /// inlining). The resulting problem retains BV-sorted predicate arguments,
    /// allowing PDR to operate on BV expressions natively via the SMT solver's
    /// BV theory. This matches Z3 Spacer's default behavior where
    /// `xform.bit_blast = false` (#5877 Wave 3).
    ///
    /// Key difference from `build_int_only`: `bv_abstracted` is set to `false`
    /// because the problem is NOT abstracted — BV sorts are preserved. Unsafe
    /// results do not require confirmation against the original problem since
    /// the solver operates in the original domain.
    pub(crate) fn build_bv_native(problem: ChcProblem, verbose: bool) -> Self {
        // #5877: For BV-native single-predicate problems with large transition
        // relations (e.g., bist_cell has 10000 nodes), the preprocessing
        // transforms (LocalVarEliminator, DeadParamEliminator, ClauseInliner)
        // can be extremely slow — each transform walks and potentially rebuilds
        // the entire expression tree. Skip preprocessing for simple BV-native
        // problems (1 predicate, few clauses) where inlining provides no benefit.
        let is_simple = problem.predicates().len() == 1
            && problem.clauses().len() <= 5
            && problem.has_bv_sorts();
        if is_simple {
            if verbose {
                safe_eprintln!(
                    "Portfolio: BV-native skipping preprocessing (simple problem, {} clauses)",
                    problem.clauses().len()
                );
            }
            return Self {
                original_problem: problem.clone(),
                transformed_problem: problem,
                back_translator: Box::new(IdentityBackTranslator),
                bv_abstracted: false,
            };
        }
        let _t_total = std::time::Instant::now();
        let pipeline = TransformationPipeline::new()
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(ClauseInliner::new().with_verbose(verbose));
        let result = pipeline.transform(problem.clone());
        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = result.problem.clauses().len();
            safe_eprintln!(
                "Portfolio: BV-native preprocessing (no BV transforms): {} clauses -> {} ({:?})",
                orig_clauses,
                new_clauses,
                _t_total.elapsed()
            );
        }
        // bv_abstracted is false: the problem retains original BV sorts.
        // Unsafe results are already in the original domain — no confirmation
        // against the original problem is needed.
        Self {
            original_problem: problem,
            transformed_problem: result.problem,
            back_translator: result.back_translator,
            bv_abstracted: false,
        }
    }
}
