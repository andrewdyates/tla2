// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unified result type for all CHC engines.
//!
//! All CHC solving engines (PDR, BMC, TPA, IMC, Kind, PDKind, TRL, CEGAR,
//! Decomposition) return `ChcEngineResult`. This eliminates 9 per-engine
//! result enums that previously duplicated the same Safe/Unsafe/Unknown
//! variants. Part of #2791.

use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use rustc_hash::FxHashMap;

/// Unified result from any CHC solving engine.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solver results must be checked — ignoring Safe/Unsafe loses correctness"]
pub enum ChcEngineResult {
    /// Safe: the system satisfies its specification.
    /// Contains an inductive invariant model (may be empty if the engine
    /// proves safety without producing an explicit invariant, e.g. TRL).
    Safe(InvariantModel),
    /// Unsafe: the system violates its specification.
    /// Contains a counterexample trace.
    Unsafe(Counterexample),
    /// Unknown: the engine could not determine the result within its budget.
    Unknown,
    /// Not applicable: the engine cannot handle this problem class
    /// (e.g., IMC/Kind on multi-predicate problems, Decomposition on
    /// non-decomposable problems).
    NotApplicable,
}

impl std::fmt::Display for ChcEngineResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe(model) => {
                write!(f, "safe (invariant with {} predicates)", model.len())
            }
            Self::Unsafe(cex) => {
                write!(f, "unsafe (counterexample at depth {})", cex.steps.len())
            }
            Self::Unknown => write!(f, "unknown"),
            Self::NotApplicable => write!(f, "not applicable"),
        }
    }
}

/// An invariant model that has been validated by the portfolio.
///
/// Private inner field ensures callers outside z4-chc cannot construct
/// verified invariants directly — they must come through the portfolio's
/// validation pipeline. Within z4-chc, the `pub(crate)` constructor
/// restricts creation to validated code paths.
///
/// Part of #5746: structural verification invariant Phase 2.
#[derive(Debug, Clone)]
#[must_use = "verified invariants should not be discarded"]
pub struct VerifiedInvariant {
    model: InvariantModel,
}

impl VerifiedInvariant {
    /// Wrap a validated invariant model.
    ///
    /// Only callable within z4-chc. All callers MUST verify the model
    /// through the portfolio's validation pipeline before calling this.
    pub(crate) fn from_validated(model: InvariantModel) -> Self {
        Self { model }
    }

    /// Get the underlying invariant model.
    pub fn model(&self) -> &InvariantModel {
        &self.model
    }

    /// Consume the wrapper and return the underlying `InvariantModel`.
    ///
    /// **Trust boundary:** The returned `InvariantModel` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// the portfolio's validation pipeline). Prefer using [`.model()`](Self::model)
    /// to borrow the inner model without stripping the verification wrapper.
    pub fn into_inner(self) -> InvariantModel {
        self.model
    }
}

/// A counterexample that has been validated by the portfolio.
///
/// Private inner field ensures callers outside z4-chc cannot construct
/// verified counterexamples directly — they must come through the portfolio's
/// validation pipeline (validate_unsafe → verify_counterexample).
///
/// Part of #5750: structural verification invariant Phase 5.
#[derive(Debug, Clone)]
#[must_use = "verified counterexamples should not be discarded"]
pub struct VerifiedCounterexample {
    cex: Counterexample,
}

impl VerifiedCounterexample {
    /// Wrap a validated counterexample.
    ///
    /// Only callable within z4-chc. All callers MUST verify the counterexample
    /// through verify_counterexample() before calling this.
    pub(crate) fn from_validated(cex: Counterexample) -> Self {
        Self { cex }
    }

    /// Get the underlying counterexample.
    pub fn counterexample(&self) -> &Counterexample {
        &self.cex
    }

    /// Consume the wrapper and return the underlying `Counterexample`.
    ///
    /// **Trust boundary:** The returned `Counterexample` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// `verify_counterexample()`). Prefer using
    /// [`.counterexample()`](Self::counterexample) to borrow without stripping
    /// the verification wrapper.
    pub fn into_inner(self) -> Counterexample {
        self.cex
    }
}

/// Marker proving `Unknown` was produced by the verification pipeline.
///
/// Cannot be constructed outside z4-chc — the private field prevents external
/// code from writing `VerifiedChcResult::Unknown(VerifiedUnknownMarker(...))`.
/// This closes the last external-construction bypass on `VerifiedChcResult`:
/// `Safe` and `Unsafe` are already protected by `VerifiedInvariant` and
/// `VerifiedCounterexample` having private fields.
#[derive(Debug, Clone)]
pub struct VerifiedUnknownMarker(pub(crate) ());

impl std::fmt::Display for VerifiedUnknownMarker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unknown (verified)")
    }
}

impl VerifiedUnknownMarker {
    pub(crate) fn new() -> Self {
        Self(())
    }
}

/// CHC result where Safe invariants and Unsafe counterexamples have been
/// validated by the portfolio.
///
/// This is the public return type of the portfolio solver. External callers
/// receive `VerifiedChcResult` instead of raw `ChcEngineResult`, ensuring
/// both Safe results and Unsafe counterexamples have passed validation.
///
/// All three variants are construction-sealed: external code cannot create
/// any variant without going through the verification pipeline.
/// - `Safe`: requires `VerifiedInvariant` (private field)
/// - `Unsafe`: requires `VerifiedCounterexample` (private field)
/// - `Unknown`: requires `VerifiedUnknownMarker` (private field)
///
/// Part of #5746 + #5750: structural verification invariant Phases 2 + 5.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solver results must be checked — ignoring Safe/Unsafe loses correctness"]
pub enum VerifiedChcResult {
    /// Safe: the system satisfies its specification.
    /// The invariant has been validated by the portfolio.
    Safe(VerifiedInvariant),
    /// Unsafe: the system violates its specification.
    /// The counterexample has been validated by the portfolio.
    Unsafe(VerifiedCounterexample),
    /// Unknown: the solver could not determine the result within its budget.
    /// The marker ensures this variant was produced by the verification pipeline.
    Unknown(VerifiedUnknownMarker),
}

impl std::fmt::Display for VerifiedChcResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe(inv) => {
                write!(
                    f,
                    "safe (verified invariant with {} predicates)",
                    inv.model().len()
                )
            }
            Self::Unsafe(cex) => {
                write!(
                    f,
                    "unsafe (verified counterexample at depth {})",
                    cex.counterexample().steps.len()
                )
            }
            Self::Unknown(_) => write!(f, "unknown"),
        }
    }
}

/// Evidence of how a ChcEngineResult was validated before promotion to
/// VerifiedChcResult.
///
/// Every path from ChcEngineResult to VerifiedChcResult MUST supply evidence.
/// This makes the validation claim auditable: grep for `ValidationEvidence::`
/// construction sites to find every path that produces verified results.
///
/// Part of #5746: structural verification invariant Phase 2.
#[derive(Debug, Clone)]
pub(crate) enum ValidationEvidence {
    /// Full verification: init + transition + query clauses checked with a
    /// fresh verifier and standard budget.
    /// Used by: portfolio full validation and adaptive direct Safe validation.
    FullVerification,

    /// Counterexample validated via fresh PDR verification.
    /// Used by: AdaptivePortfolio::finalize_verified_result() before exposing
    /// VerifiedChcResult::Unsafe from the public verified API.
    CounterexampleVerification,

    /// Query-only verification for k-inductive engines (Kind, PDKind).
    /// Query clauses checked. Transition clauses not required because the engine's
    /// k-induction proof already establishes transition safety.
    /// Used by: AdaptivePortfolio::try_kind() via validate_kind_result_query_only()
    QueryOnly,

    /// Trivial problem: no predicate occurrences in clause bodies.
    /// All query constraints checked for satisfiability via direct SMT.
    /// No loop invariant needed — the problem has no loops.
    /// Used by: AdaptivePortfolio::solve_entry_exit_only()
    TrivialProblem,

    /// Algebraic synthesis proved unsafe: the algebraically-derived invariant
    /// is valid (init and transition hold) but concrete evaluation proved the
    /// query clause admits bad states. No counterexample trace is available,
    /// but the constructive proof (closed-form recurrence + concrete witness)
    /// is sound.
    /// Used by: AdaptivePortfolio::solve_internal() algebraic prepass
    AlgebraicUnsafe,

    /// BMC counterexample: the bounded model checker found a satisfying
    /// assignment to the reachability encoding (init ∧ trans^k ∧ query).
    /// The counterexample is constructive — the SMT solver produced a model
    /// for the exact BMC formula — so independent re-verification is not
    /// needed. Re-verification would re-solve the same BMC problem in a fresh
    /// PdrSolver context, which times out for deep counterexamples (depth >=22)
    /// due to the 2s/30s verification budget.
    /// Used by: solve_complex_loop BMC probe, portfolio BMC engine
    BmcCounterexample,
}

impl VerifiedChcResult {
    /// Promote a validated engine result to a verified result.
    ///
    /// Caller MUST supply evidence of what validation was performed.
    /// Replaces the old `from_validated_engine_result` (no evidence) to make
    /// every verification path auditable. Part of #5746.
    pub(crate) fn from_validated(result: ChcEngineResult, evidence: ValidationEvidence) -> Self {
        tracing::debug!(
            "Promoting to VerifiedChcResult with evidence: {:?}",
            evidence
        );
        match result {
            ChcEngineResult::Safe(model) => Self::Safe(VerifiedInvariant::from_validated(model)),
            ChcEngineResult::Unsafe(cex) => {
                Self::Unsafe(VerifiedCounterexample::from_validated(cex))
            }
            ChcEngineResult::Unknown | ChcEngineResult::NotApplicable => {
                Self::Unknown(VerifiedUnknownMarker::new())
            }
        }
    }

    /// Returns `true` if the result is `Safe`.
    #[inline]
    pub fn is_safe(&self) -> bool {
        matches!(self, Self::Safe(_))
    }

    /// Returns `true` if the result is `Unsafe`.
    #[inline]
    pub fn is_unsafe(&self) -> bool {
        matches!(self, Self::Unsafe(_))
    }

    /// Returns `true` if the result is `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    /// Get the verified invariant if the result is `Safe`.
    #[inline]
    pub fn safe_invariant(&self) -> Option<&VerifiedInvariant> {
        match self {
            Self::Safe(inv) => Some(inv),
            _ => None,
        }
    }

    /// Get the verified counterexample if the result is `Unsafe`.
    #[inline]
    pub fn unsafe_counterexample(&self) -> Option<&VerifiedCounterexample> {
        match self {
            Self::Unsafe(cex) => Some(cex),
            _ => None,
        }
    }
}

/// Build an `InvariantModel` for a single-predicate problem from a `ChcExpr` invariant.
///
/// Handles the variable renaming from engine-internal `v0, v1, ...` format to
/// the canonical PDR format `__p{pred_index}_a{arg_index}`. Returns `None` if
/// the problem has no predicates or if variable counts don't match.
pub(crate) fn build_single_pred_model(
    problem: &ChcProblem,
    invariant: ChcExpr,
) -> Option<InvariantModel> {
    let pred = problem.predicates().first()?.clone();

    let engine_vars: Vec<_> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
        .collect();
    let pdr_vars: Vec<_> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{i}", pred.id.index()), sort.clone()))
        .collect();

    if engine_vars.len() != pdr_vars.len() {
        return None;
    }

    let subst: Vec<_> = engine_vars
        .into_iter()
        .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
        .collect();
    let formula = invariant.substitute(&subst);

    let mut model = InvariantModel::new();
    model.set(pred.id, PredicateInterpretation::new(pdr_vars, formula));
    Some(model)
}

/// Build a skeleton counterexample with `depth + 1` steps and no assignments.
///
/// Used by engines that prove unsafety but don't produce detailed traces
/// (IMC, Kind, PDKind).
pub(crate) fn skeleton_counterexample(problem: &ChcProblem, depth: usize) -> Counterexample {
    let pred = problem
        .predicates()
        .first()
        .map_or(PredicateId::new(0), |p| p.id);
    let steps = (0..=depth)
        .map(|_| CounterexampleStep {
            predicate: pred,
            assignments: FxHashMap::default(),
        })
        .collect();
    Counterexample {
        steps,
        witness: None,
    }
}
