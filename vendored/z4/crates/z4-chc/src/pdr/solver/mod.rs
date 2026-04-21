// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR solver implementation.
//!
//! This is the main PDR (Property-Directed Reachability) / IC3 algorithm implementation.
//! The algorithm maintains frames (over-approximations of reachable states) and
//! refines them by blocking counterexample states using SMT queries.
//!
//! ## Lemma Generalization
//!
//! This implementation uses the "drop literal" technique for lemma generalization.
//! When blocking a state, instead of just negating the exact state formula, we try
//! to find a more general blocking clause by:
//! 1. Extracting conjuncts from the state formula
//! 2. Trying to drop each conjunct while maintaining inductiveness
//! 3. Using the most general lemma that doesn't block initial states

// Complex types for counterexample trace reconstruction
#![allow(clippy::type_complexity)]

/// Gate for incremental PDR (#6358: per-predicate prop_solver).
///
/// When `true` AND `problem_is_pure_lia`, blocking queries use the per-predicate
/// `PredicatePropSolver` (one persistent SAT solver per predicate, Z3 Spacer
/// pattern). Non-pure-LIA problems bypass incremental entirely — no double-solve.
///
/// Enabled: benchmarks show +1 SAT (27→28, 15s timeout) with zero wrong answers.
/// Disabled per #6583: incremental PDR regressed from 39/55 to 28/55 SAT.
/// The try-and-fallthrough architecture doubles query cost without phase hints.
/// Re-enable after Z3-style assumption-based incremental redesign.
pub(super) const INCREMENTAL_PDR_ENABLED: bool = false;

mod algebraic;
mod blocking;
pub(super) mod caches;
#[allow(dead_code)]
pub(crate) mod convergence_monitor;
mod core;
mod cube_extraction;
mod edge_summary;
mod entry_failure;
mod expr;
mod helpers;
mod hyperedge;
pub(super) mod inductiveness;
mod invariant_check;
mod invariant_discovery;
mod invariants;
mod model;
mod model_building;
mod must_reachability;
pub(super) mod prop_solver;
mod solve;
mod startup;
mod stats;
mod strengthen;
mod tla_trace;

#[cfg(test)]
pub(in crate::pdr::solver) mod test_helpers;

use self::helpers::{
    build_canonical_predicate_vars, build_frame_predicate_lemma_counts, build_predicate_users,
    build_push_cache_deps, compute_push_cache_signature, compute_reachable_predicates,
    detect_triangular_pattern,
};

use crate::convex_closure::ConvexClosure;
use crate::farkas::compute_interpolant;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::proof_interpolation::{
    compute_interpolant_from_lia_farkas, extract_interpolant_from_precomputed_farkas,
};
use crate::smt::{PersistentExecutorSmtContext, SmtContext, SmtResult, SmtValue};
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ChcResult, ChcSort, ChcVar, HornClause, PredicateId,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BinaryHeap, VecDeque};
use std::fs;
use std::path::Path;
use std::sync::Arc;
use z4_sat::TlaTraceWriter;

#[cfg(test)]
use self::invariants::parity_mod2_opposite_blocking;
use self::invariants::{extract_negated_parity_constraint, extract_parity_constraint};
use super::config::{luby, PdrConfig};
use super::counterexample::{
    Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry, WitnessBuilder,
};
use super::cube;
use super::derivation::DerivationStore;
use super::frame::{Frame, Lemma, MustSummaries, PdrResult};
use super::generalize_adapter::PdrGeneralizerAdapter;
use super::interpolation_failure::{
    InterpolationDiagnostics, InterpolationFailure, InterpolationStats,
};
use super::lemma_cluster::{filter_out_lit, filter_out_lit_with_eq_retry};
use super::model::{InvariantModel, PredicateInterpretation};
use super::obligation::{PriorityPob, ProofObligation};
use super::reach_fact::{ReachFact, ReachFactId, ReachFactStore};
use super::reach_solver::ReachSolverStore;
use super::scc::{tarjan_scc, SCCInfo};
use super::types::{
    BlockResult, BoundType, InitResult, PredecessorState, RelationType, StrengthenResult,
};
use super::verification::CexVerificationResult;
use crate::generalize::{
    BoundExpansionGeneralizer, BvBitDecompositionGeneralizer, BvBitGroupGeneralizer,
    BvFlagGuardGeneralizer, ConstantSumGeneralizer, DenominatorSimplificationGeneralizer,
    DropLiteralGeneralizer, FarkasGeneralizer, GeneralizerPipeline, ImplicationGeneralizer,
    InitBoundWeakeningGeneralizer, LemmaGeneralizer, LiteralWeakeningGeneralizer,
    RelationalEqualityGeneralizer, RelevantVariableProjectionGeneralizer,
    SingleVariableRangeGeneralizer, TemplateGeneralizer, UnsatCoreGeneralizer,
};

/// Result of checking if a candidate is self-inductive with model extraction.
enum InductiveCheckResult {
    Inductive,
    NotInductive(FxHashMap<String, SmtValue>),
    Unknown,
}

/// Result of attempting to discharge an entry SAT model (Entry-CEGAR).
///
/// Used by `is_entry_inductive` to distinguish:
/// - reachable predecessor states (true violation of entry-inductiveness)
/// - unreachable predecessor states (spurious; refine predecessor frames and retry)
/// - Unknown (conservative: reject)
enum EntryCegarDischarge {
    Reachable,
    Unreachable,
    Unknown,
}

/// Conservative failure classes from `is_entry_inductive`.
///
/// These are tracked as counters for Unknown triage and CHC local-maximum analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EntryInductiveFailureReason {
    Cancelled,
    HeadInstantiationFailed,
    SatHyperedge,
    UnexpectedSelfEdge,
    CubeExtractionFailed,
    ReachFactIntersection,
    EntryCegarDisabled,
    EntryCegarBudgetExhausted,
    DischargeReachable,
    DischargeUnknown,
    SmtUnknownRejected,
    RefinementLimitExceeded,
}

impl std::fmt::Display for EntryInductiveFailureReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl EntryInductiveFailureReason {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Cancelled => "cancelled",
            Self::HeadInstantiationFailed => "head_instantiation_failed",
            Self::SatHyperedge => "sat_hyperedge",
            Self::UnexpectedSelfEdge => "unexpected_self_edge",
            Self::CubeExtractionFailed => "cube_extraction_failed",
            Self::ReachFactIntersection => "reach_fact_intersection",
            Self::EntryCegarDisabled => "entry_cegar_disabled",
            Self::EntryCegarBudgetExhausted => "entry_cegar_budget_exhausted",
            Self::DischargeReachable => "discharge_reachable",
            Self::DischargeUnknown => "discharge_unknown",
            Self::SmtUnknownRejected => "smt_unknown_rejected",
            Self::RefinementLimitExceeded => "refinement_limit_exceeded",
        }
    }
}

/// TLA2 trace-related state for runtime PDR validation.
///
/// Groups the 3 fields needed for TLA2 trace emission into a single struct,
/// reducing PdrSolver field count. Accessed from `tla_trace.rs`, `solve.rs`,
/// and `model.rs`.
#[derive(Default)]
pub(super) struct TracingState {
    /// Optional TLA2 trace writer for runtime validation of PDR transitions.
    pub tla_trace: Option<TlaTraceWriter>,
    /// Snapshot of the currently-active proof obligation's identity fields.
    pub active_pob: Option<(usize, usize, usize)>, // (predicate_index, level, depth)
    /// The current query level being strengthened by the main PDR loop.
    pub query_level: Option<usize>,
}

/// Restart-related state for Luby restarts (#1270).
///
/// Groups the 5 fields needed for the restart mechanism into a single struct,
/// reducing PdrSolver field count. Almost exclusively accessed from `solve.rs`.
pub(super) struct RestartState {
    /// Total lemmas learned since last restart (for Luby restart threshold).
    pub lemmas_since_restart: usize,
    /// Current restart threshold (Luby scaled).
    pub restart_threshold: usize,
    /// Current Luby index (0-indexed, incremented at each restart).
    pub luby_index: u32,
    /// Total restart count (for logging).
    pub restart_count: usize,
    /// Whether `apply_lemma_hints(HintStage::Stuck)` has been called (#2393).
    pub stuck_hints_applied: bool,
}

impl RestartState {
    fn new(restart_threshold_init: usize) -> Self {
        Self {
            lemmas_since_restart: 0,
            restart_threshold: restart_threshold_init,
            luby_index: 0,
            restart_count: 0,
            stuck_hints_applied: false,
        }
    }
}

/// Convergence monitor for detecting PDR stagnation.
///
/// Tracks per-iteration progress metrics (lemma velocity, frame advancement)
/// and detects when the solver is spending time without making progress. The
/// main loop can respond by escalating internal generalization modes before
/// eventually returning `Unknown` under a budget.
///
/// Reference: SATzilla (Xu et al. 2008), MachSMT (Scott et al. 2021) — feature-based
/// algorithm selection. This is the runtime convergence counterpart: instead of
/// selecting statically based on problem features, we monitor convergence during
/// solving and bail early when the current approach stalls.
pub(super) struct ConvergenceMonitor {
    /// Wall-clock time when the solve loop started.
    pub solve_start: std::time::Instant,
    /// Wall-clock time of the most recent frame advancement (push_frame).
    pub last_frame_advance: std::time::Instant,
    /// Total lemma count at the start of each window.
    pub window_lemma_count: usize,
    /// Iteration count at the start of each window.
    pub window_start_iteration: usize,
    /// Number of frames at the start of each window.
    pub window_frame_count: usize,
    /// Number of strengthen() calls that returned Safe or Continue (progress)
    /// in the current window.
    pub window_productive_strengthens: usize,
    /// Number of strengthen() calls total in the current window.
    pub window_total_strengthens: usize,
    /// Cumulative count of stagnation windows detected.
    /// The main loop uses this count for internal mode escalation and eventual
    /// bailout once all escalation levels are exhausted.
    pub consecutive_stagnant_windows: usize,
}

impl ConvergenceMonitor {
    /// Window size in iterations for measuring convergence rate.
    const WINDOW_SIZE: usize = 20;

    /// Maximum consecutive stagnant windows before the monitor reaches its
    /// bailout threshold. The main loop may spend these windows escalating
    /// internal modes before honoring the bailout.
    ///
    /// Raised from 3 to 8: the solve_timeout already enforces the total budget.
    /// Premature stagnation abort causes regressions under high system load
    /// where wall-clock stall detection fires before the solver has had enough
    /// CPU time. The convergence monitor should be a very loose heuristic.
    const MAX_STAGNANT_WINDOWS: usize = 8;

    /// Maximum wall-clock seconds without frame advancement before declaring stagnation.
    /// If PDR hasn't advanced a frame in this many seconds while iterating,
    /// it's likely stuck in a fruitless blocking/rejection cycle.
    ///
    /// Raised from 8 to 30: under high system load (4x CPU oversubscription),
    /// 8 wall-clock seconds may be only 2s of CPU time. PDR should be allowed
    /// to use its full solve_timeout budget. The frame stall is now a last-resort
    /// detector for truly stuck solvers, not a tight gate.
    const FRAME_STALL_SECS: u64 = 30;

    pub(super) fn new() -> Self {
        let now = std::time::Instant::now();
        Self {
            solve_start: now,
            last_frame_advance: now,
            window_lemma_count: 0,
            window_start_iteration: 0,
            window_frame_count: 0,
            window_productive_strengthens: 0,
            window_total_strengthens: 0,
            consecutive_stagnant_windows: 0,
        }
    }

    /// Record a frame advancement event.
    pub(super) fn note_frame_advance(&mut self) {
        self.last_frame_advance = std::time::Instant::now();
    }

    /// Record a strengthen() outcome.
    pub(super) fn note_strengthen(&mut self, productive: bool) {
        self.window_total_strengthens += 1;
        if productive {
            self.window_productive_strengthens += 1;
        }
    }

    /// Restart the active convergence window after an internal mode switch.
    ///
    /// Keeps the cumulative stagnant-window count intact so the main loop can
    /// still tell whether this was the first, second, or third escalation.
    pub(crate) fn note_generalization_escalation(
        &mut self,
        current_iteration: usize,
        current_lemma_count: usize,
        current_frame_count: usize,
    ) {
        self.last_frame_advance = std::time::Instant::now();
        self.window_lemma_count = current_lemma_count;
        self.window_start_iteration = current_iteration;
        self.window_frame_count = current_frame_count;
        self.window_productive_strengthens = 0;
        self.window_total_strengthens = 0;
    }

    /// Check if the current window is complete and evaluate stagnation.
    ///
    /// Returns `true` once the monitor has reached its bailout threshold.
    /// `current_iteration`: the solver's iteration counter.
    /// `current_lemma_count`: total lemmas across all frames right now.
    /// `current_frame_count`: number of frames right now.
    /// `has_solve_timeout`: whether the solver has a wall-clock timeout set.
    ///   Convergence monitoring only activates when running under a budget
    ///   (portfolio or solve_timeout), not for standalone CLI usage.
    #[allow(dead_code)]
    pub(super) fn check_stagnation(
        &mut self,
        current_iteration: usize,
        current_lemma_count: usize,
        current_frame_count: usize,
        has_solve_timeout: bool,
    ) -> bool {
        // Only activate when running under a budget (portfolio/solve_timeout).
        // Standalone CLI runs have unlimited time and shouldn't bail early.
        if !has_solve_timeout {
            return false;
        }

        // Check frame stall: no frame advancement in FRAME_STALL_SECS
        // while we've done at least WINDOW_SIZE iterations total.
        if current_iteration >= Self::WINDOW_SIZE {
            let secs_since_frame = self.last_frame_advance.elapsed().as_secs();
            if secs_since_frame >= Self::FRAME_STALL_SECS {
                // Frame stall detected — but only count it if we also have
                // no lemma velocity (to avoid false positives during heavy
                // model verification phases where frames don't advance but
                // lemmas are being learned).
                let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
                let iter_delta = current_iteration.saturating_sub(self.window_start_iteration);
                if iter_delta > 0 && lemma_delta == 0 {
                    return true;
                }
            }
        }

        // Check window-based stagnation: every WINDOW_SIZE iterations
        let iters_in_window = current_iteration.saturating_sub(self.window_start_iteration);
        if iters_in_window < Self::WINDOW_SIZE {
            return false;
        }

        // Window complete — evaluate progress
        let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
        let frame_delta = current_frame_count.saturating_sub(self.window_frame_count);

        let is_stagnant =
            lemma_delta == 0 && frame_delta == 0 && self.window_productive_strengthens == 0;

        if is_stagnant {
            self.consecutive_stagnant_windows += 1;
        } else {
            self.consecutive_stagnant_windows = 0;
        }

        // Reset window
        self.window_lemma_count = current_lemma_count;
        self.window_start_iteration = current_iteration;
        self.window_frame_count = current_frame_count;
        self.window_productive_strengthens = 0;
        self.window_total_strengthens = 0;

        self.consecutive_stagnant_windows >= Self::MAX_STAGNANT_WINDOWS
    }

    /// Elapsed wall-clock time since solve started.
    pub(super) fn elapsed(&self) -> std::time::Duration {
        self.solve_start.elapsed()
    }

    /// Time since last frame advancement.
    pub(super) fn time_since_frame_advance(&self) -> std::time::Duration {
        self.last_frame_advance.elapsed()
    }
}

/// Active generalization strategy controlling how aggressively the pipeline
/// drops conjuncts and applies weakening phases (#7911).
///
/// The strategy is selected by `escalate_generalization_strategy` /
/// `de_escalate_generalization_strategy` based on convergence progress.
/// Higher levels enable more pipeline stages and raise the drop-literal
/// failure limit, trading SMT query cost for stronger generalization.
///
/// Reference: Z3 Spacer uses a similar graduated approach where
/// generalization aggressiveness adapts based on solver progress
/// (`reference/z3/src/muz/spacer/spacer_generalizers.cpp`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum GeneralizationStrategy {
    /// Minimal pipeline: UnsatCore + DropLiteral only, failure_limit=5.
    Conservative,
    /// Standard pipeline: all Phase 0-2 generalizers, failure_limit=10.
    Default,
    /// Extended pipeline: standard + relational generalizers, failure_limit=20.
    Aggressive,
    /// Maximum pipeline: all generalizers, failure_limit=50, two fixpoint passes.
    MaxAggressive,
}

impl GeneralizationStrategy {
    pub(crate) fn drop_literal_failure_limit(self) -> usize {
        match self {
            Self::Conservative => 5,
            Self::Default => 10,
            Self::Aggressive => 20,
            Self::MaxAggressive => 50,
        }
    }
    pub(crate) fn use_early_aggressive_generalizers(self) -> bool {
        !matches!(self, Self::Conservative)
    }
    pub(crate) fn use_relational_generalizers(self) -> bool {
        matches!(self, Self::Aggressive | Self::MaxAggressive)
    }
    pub(crate) fn use_bound_expansion(self) -> bool {
        matches!(self, Self::Default | Self::Aggressive | Self::MaxAggressive)
    }
    pub(crate) fn fixpoint_passes(self) -> usize {
        match self {
            Self::MaxAggressive => 2,
            _ => 1,
        }
    }
    pub(crate) fn from_escalation_level(level: usize) -> Self {
        match level {
            0 => Self::Default,
            1 | 2 => Self::Aggressive,
            _ => Self::MaxAggressive,
        }
    }
}

impl std::fmt::Display for GeneralizationStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conservative => write!(f, "conservative"),
            Self::Default => write!(f, "default"),
            Self::Aggressive => write!(f, "aggressive"),
            Self::MaxAggressive => write!(f, "max-aggressive"),
        }
    }
}

/// A single strategy change event recorded for post-hoc analysis (#7918).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StrategyEvent {
    /// Solver iteration at which the strategy change occurred.
    pub iteration: usize,
    /// Strategy level *before* the change (0-3).
    pub from_level: usize,
    /// Strategy level *after* the change.
    pub to_level: usize,
    /// `true` for escalation, `false` for de-escalation.
    pub is_escalation: bool,
}

/// A convergence-window snapshot captured at a stagnation-check boundary (#7918).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WindowSnapshot {
    /// Sequential window index (0-based).
    pub window_index: usize,
    /// Total lemmas across all frames when the window closed.
    pub total_lemma_count: usize,
    /// Whether this window was classified as stagnant.
    pub was_stagnant: bool,
    /// Active strategy level during this window (0-3).
    pub strategy_level: usize,
}

#[allow(dead_code)]
/// Aggregate telemetry for generalization strategy adaptation (#7918).
///
/// Tracks escalation/de-escalation events, per-window convergence snapshots,
/// and stagnation counts for data-driven threshold tuning.
#[derive(Debug, Clone, Default)]
pub(crate) struct StrategyTelemetry {
    /// Ordered log of all strategy change events during the solve.
    pub events: Vec<StrategyEvent>,
    /// Total number of escalations.
    pub escalation_count: usize,
    /// Total number of de-escalations.
    pub de_escalation_count: usize,
    /// Strategy level active when the solve completed (0-3).
    pub final_strategy_level: usize,
    /// Total stagnation events detected across all windows.
    pub total_stagnation_events: usize,
    /// Per-window snapshots for offline analysis.
    pub window_snapshots: Vec<WindowSnapshot>,
}

impl StrategyTelemetry {
    /// Record an escalation event.
    pub(crate) fn record_escalation(
        &mut self,
        iteration: usize,
        from_level: usize,
        to_level: usize,
    ) {
        self.escalation_count += 1;
        self.events.push(StrategyEvent {
            iteration,
            from_level,
            to_level,
            is_escalation: true,
        });
    }

    /// Record a de-escalation event.
    pub(crate) fn record_de_escalation(
        &mut self,
        iteration: usize,
        from_level: usize,
        to_level: usize,
    ) {
        self.de_escalation_count += 1;
        self.events.push(StrategyEvent {
            iteration,
            from_level,
            to_level,
            is_escalation: false,
        });
    }

    /// Record a window snapshot at a stagnation-check boundary.
    pub(crate) fn record_window_snapshot(
        &mut self,
        total_lemma_count: usize,
        was_stagnant: bool,
        strategy_level: usize,
    ) {
        let window_index = self.window_snapshots.len();
        self.window_snapshots.push(WindowSnapshot {
            window_index,
            total_lemma_count,
            was_stagnant,
            strategy_level,
        });
    }

    /// Record that a stagnation event was detected.
    pub(crate) fn record_stagnation_event(&mut self) {
        self.total_stagnation_events += 1;
    }

    /// Format a human-readable summary for verbose logging.
    pub(crate) fn summary(&self) -> String {
        format!(
            "escalations={}, de_escalations={}, final_level={}, stagnation_events={}, windows={}",
            self.escalation_count,
            self.de_escalation_count,
            self.final_strategy_level,
            self.total_stagnation_events,
            self.window_snapshots.len(),
        )
    }
}

/// Telemetry counters for solver diagnostics and offline triage.
///
/// Groups write-mostly counters that track interpolation quality,
/// failure modes, and query counts. Reduces PdrSolver field count.
#[derive(Default)]
pub(super) struct PdrTelemetry {
    /// Aggregate success/failure counts for the 5-method interpolation cascade.
    /// Printed in verbose mode at solve end; used for diagnosing interpolation quality.
    pub interpolation_stats: InterpolationStats,
    /// Number of SAT predecessor queries where cube extraction failed.
    pub sat_no_cube_events: usize,
    /// Entry-inductiveness conservative-failure counters by reason class.
    pub entry_inductive_failure_counts: FxHashMap<EntryInductiveFailureReason, usize>,
    /// Counter for verification queries.
    pub verification_queries: usize,
    /// Counter for generalization attempts.
    pub generalization_attempts: usize,
    /// Entry CEGAR discharge outcomes: [reachable, unreachable, unknown].
    pub entry_cegar_discharge_outcomes: [usize; 3],
    /// Number of transition clauses skipped by BV soft degradation (#5643).
    /// Incremented when budget exhaustion causes a BV transition clause to be
    /// skipped instead of rejected. Non-zero means the model was not fully
    /// verified for inductiveness — only query clauses were hard-checked.
    pub bv_soft_degradation_skips: usize,
    /// Rotation counter for clause iteration order diversity (#5877).
    /// Incremented on each blocking call. Used to rotate the starting index
    /// of clause enumeration so that different transition branches fire across
    /// successive blocking attempts, preventing the "first SAT wins" bias.
    pub clause_rotation_counter: usize,
    /// Strategy adaptation telemetry for data-driven threshold tuning (#7918).
    pub strategy: StrategyTelemetry,
}

/// Degradation counters for fixed-point verification failures.
///
/// Groups the counters and progress signature that track how close the solver
/// is to giving up on model verification. `consecutive_unlearnable` is reset
/// when learning progress changes between failures; the counters are then
/// checked against thresholds and reported
/// in stats/TLA+ traces. Primary consumer: `model.rs` (write),
/// `solve.rs` + `stats.rs` + `tla_trace.rs` (read).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(super) struct VerificationProgressSignature {
    /// Total learned lemmas across all frames.
    pub lemma_count: usize,
    /// Total must-summary entries across all levels/predicates.
    pub must_summary_count: usize,
    /// Total stored reach facts.
    pub reach_fact_count: usize,
}

#[derive(Default)]
pub(super) struct VerificationCounters {
    /// Consecutive fixed-point verification failures where we couldn't learn.
    /// Reset to 0 when the progress signature changes; threshold triggers give-up.
    pub consecutive_unlearnable: usize,
    /// Total verification UNKNOWN results (pre_state = Bool(false)).
    /// Never reset; threshold triggers give-up.
    pub total_unknowns: usize,
    /// Total model verification failures across all fixed-point attempts.
    /// Never reset; caps total work spent on model verification.
    pub total_model_failures: usize,
    /// Learning progress at the most recent model verification failure.
    pub last_unlearnable_progress: VerificationProgressSignature,
    /// Frame-1 lemma count at last failed direct safety proof attempt.
    /// Only retry when new lemmas discovered since last failure (#5480).
    pub last_direct_safety_lemma_count: usize,
}

/// Proof obligation queue management.
///
/// Groups the 5 fields for obligation scheduling and deduplication into a single
/// struct, reducing PdrSolver field count. Primary consumer: `core.rs` (enqueue/pop),
/// with `solve.rs` (restart cleanup), `model.rs` (dedup), `stats.rs` and
/// `tla_trace.rs` (size queries).
#[derive(Default)]
pub(super) struct ObligationQueue {
    /// Queue of proof obligations (DFS mode).
    pub deque: VecDeque<ProofObligation>,
    /// Priority queue of obligations (level-priority mode).
    pub heap: BinaryHeap<PriorityPob>,
    /// Monotonic counter for deterministic tie-breaking of obligations.
    pub next_id: u64,
    /// Set when a proof obligation enqueue is dropped due to queue capacity.
    ///
    /// This is a per-strengthen-call degradation signal: once set, the current
    /// strengthen attempt must not return `Safe`/`Continue`, because obligation
    /// exploration became incomplete.
    pub overflowed: bool,
    /// Dedup set for fixed-point verification obligations (#1293).
    /// Keys are (predicate, level, state_hash). Prevents re-queueing identical POBs
    /// when fixed-point verification fails and we enqueue the CEX for predecessor recursion.
    /// Cleared when frames change in a way that could make an obligation learnable.
    pub fixed_point_pob_seen: FxHashSet<(PredicateId, usize, u64)>,
}

/// Under-approximation (must-reachability) state for PDR.
///
/// Groups the 5 fields needed for must-reachability tracking: reach facts,
/// reach solvers, must summaries, and derivations. These fields are almost
/// always accessed together (e.g., `insert_reach_fact_bounded` → add to
/// `reach_solvers` → update `must_summaries`). Reduces PdrSolver field count.
///
/// Primary consumers: `must_reachability.rs`, `hyperedge.rs`, `solve.rs`,
/// `model.rs`, `blocking/utils.rs`, `inductiveness/mod.rs`, various
/// `invariant_discovery/` and `expr/sampling/` modules.
pub(super) struct ReachabilityState {
    /// Under-approximations (must summaries) with explicit provenance tracking.
    ///
    /// Stores two categories of entries:
    /// - **Backed**: proven reachable states with a corresponding `ReachFact` / witness chain
    /// - **Unbacked**: heuristic seeds (e.g., loop-closure enrichment) without proof
    ///
    /// Proof-critical consumers (hyperedge UNSAFE detection) use backed-only summaries.
    /// (Spacer technique for faster convergence - see #2247 for provenance design)
    pub must_summaries: MustSummaries,
    /// Concrete reachability facts with justification chains (Spacer reach_fact).
    pub reach_facts: ReachFactStore,
    /// Indicates reach-fact storage saturation; solver must degrade to `Unknown`.
    pub reach_facts_saturated: bool,
    /// Per-predicate incremental reach solvers for fast must-reachability intersection checks.
    /// See `designs/2026-01-29-reach-fact-caching-for-sat-discovery.md`.
    pub reach_solvers: ReachSolverStore,
    /// Derivation store for tracking multi-body clause progress (Spacer derivation).
    /// See `designs/2026-01-28-derivation-tracking-reachfacts.md`.
    pub derivations: DerivationStore,
}

impl ReachabilityState {
    pub(super) fn new() -> Self {
        Self {
            must_summaries: MustSummaries::new(),
            reach_facts: ReachFactStore::new(),
            reach_facts_saturated: false,
            reach_solvers: ReachSolverStore::new(),
            derivations: DerivationStore::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum ArraySessionKey {
    HeadFact {
        clause_index: usize,
    },
    SingleBody {
        clause_index: usize,
    },
    PrevLevelInit {
        clause_index: usize,
        fact_index: usize,
    },
}

/// PDR solver state
pub struct PdrSolver {
    /// The CHC problem being solved
    pub(super) problem: ChcProblem,
    /// Configuration
    pub(super) config: PdrConfig,
    /// Consolidated cache subsystem (static lookups + bounded dynamic caches, #3590).
    pub(super) caches: caches::PdrCacheStore,
    /// Frames F_0, F_1, ..., F_N (over-approximations / blocking lemmas)
    pub(super) frames: Vec<Frame>,
    // --- Obligation queue (#3301) ---
    pub(super) obligations: ObligationQueue,
    /// Number of iterations performed
    iterations: usize,
    /// SMT context for queries
    pub(super) smt: SmtContext,
    /// Clause-scoped persistent executor sessions for array-heavy blocking queries (#6047).
    pub(super) array_clause_sessions: FxHashMap<ArraySessionKey, PersistentExecutorSmtContext>,
    /// Model-based projection engine (for predecessor generalization)
    mbp: crate::mbp::Mbp,
    // --- Reachability state (must-summaries, reach facts, derivations, #3301) ---
    pub(super) reachability: ReachabilityState,
    // --- Verification degradation counters (#3301) ---
    pub(super) verification: VerificationCounters,
    /// Convex closure computation engine
    convex_closure_engine: ConvexClosure,
    /// SCC information for cyclic predicate handling
    scc_info: SCCInfo,

    // --- Restart state (#1270) ---
    pub(super) restart: RestartState,

    // --- Tracing state (TLA2 runtime validation, #3301) ---
    pub(super) tracing: TracingState,
    /// Deadline computed from `config.solve_timeout` at the start of `solve()`.
    pub(in crate::pdr) solve_deadline: Option<std::time::Instant>,

    // --- Telemetry counters (#2450, #3301) ---
    pub(super) telemetry: PdrTelemetry,

    // --- Convergence monitoring ---
    /// Tracks per-iteration progress metrics for stagnation detection.
    /// When the solver is running under a portfolio budget and progress stalls,
    /// the main loop can escalate internal modes before eventually returning
    /// `Unknown` so budget can be redirected.
    pub(super) convergence: ConvergenceMonitor,
    /// Current internal generalization escalation level (0-3).
    pub(crate) generalization_escalation_level: usize,
    /// Active generalization strategy (#7911).
    pub(crate) generalization_strategy: GeneralizationStrategy,
    /// Set when `solve()` exits because convergence stagnation exhausted all
    /// available internal mode escalations.
    pub(crate) terminated_by_stagnation: bool,
    /// Lemma quality metrics for convergence health assessment (#7906).
    pub(super) lemma_quality: convergence_monitor::LemmaQualityMetrics,
    /// Problem size hint for adaptive convergence thresholds (#7906).
    pub(super) problem_size_hint: convergence_monitor::ProblemSizeHint,

    // --- Per-predicate persistent solvers (#6358) ---
    /// One persistent incremental solver per predicate. Each `PredicatePropSolver`
    /// owns a single SAT solver with activation-guarded background segments for
    /// different query families (blocking, predecessor, inductiveness). This
    /// matches the Z3 Spacer `prop_solver` pattern: one solver per predicate,
    /// not per query lane.
    ///
    /// Gated by `INCREMENTAL_PDR_ENABLED`. When false, all queries go directly
    /// to the non-incremental `self.smt` path.
    pub(super) prop_solvers: FxHashMap<PredicateId, prop_solver::PredicatePropSolver>,

    // --- Problem feature flags (#6366, #6480) ---
    /// Whether the problem has any Array-sorted predicate parameters.
    /// Computed once at construction from predicate sorts. When `false`, all
    /// array-specific overhead (scalarization, `contains_array_ops()` walks,
    /// array clause sessions) is bypassed.
    pub(super) uses_arrays: bool,
    /// Whether all clause expressions are pure LIA (no ITE, mod, or div) after
    /// preprocessing such as OR/ITE splitting.
    /// When `true`, incremental SAT results from DPLL(T) are trustworthy
    /// for all blocking sites. When `false`, only Unsat is trusted (#6480).
    pub(super) problem_is_pure_lia: bool,
    /// Whether the problem is pure integer arithmetic (LIA + ITE + mod/div, no BV/arrays/UF).
    /// Weaker condition than `problem_is_pure_lia` that still enables incremental PDR.
    /// The original `problem_is_pure_lia` (no ITE/mod/div) was too conservative for
    /// benchmarks like dillig02_m, s_multipl_17, gj2007_m_1/2 where Z3 succeeds (#5970).
    pub(super) problem_is_integer_arithmetic: bool,

    /// Remaining budget for executor cross-checks (#5970 overhead regression).
    /// Cross-checks (#6787) prevent false-UNSAT but add ~50-100ms per query.
    /// Budget starts at 5s and is decremented on each cross-check call.
    /// When exhausted, verification proceeds without cross-checks.
    pub(super) cross_check_budget: std::time::Duration,

    /// True when the startup fixpoint loop detected convergence (frame[0] = frame[1]).
    /// Used by check_invariants_prove_safety to build convergence_proven models
    /// that skip the expensive inductiveness verification cascade. (#5970)
    pub(super) startup_converged: bool,

    /// Invariants that failed entry-inductiveness but may pass after frame
    /// strengthening (#5970 deferred retry). Each entry:
    /// (predicate, formula, target_level, retry_count).
    /// Retried after invariant discovery when frames may have new lemmas.
    pub(super) deferred_entry_invariants: Vec<(PredicateId, ChcExpr, usize, u8)>,

    /// Invariants that failed self-inductiveness but may pass with frame-strengthened
    /// checks after the frame grows. Retried with frame context during startup fixpoint.
    /// Each entry: (predicate, formula, target_level, retry_count).
    pub(super) deferred_self_inductive_invariants: Vec<(PredicateId, ChcExpr, usize, u8)>,

    /// Cache of recently-rejected invariants to avoid rediscovering and re-checking
    /// the same formula that already failed init-validity or self-inductiveness.
    /// Key: (predicate, formula). Cleared on push_frame (level advance) since
    /// frame strengthening may make previously-rejected invariants valid.
    /// Bounded at 512 entries to prevent memory growth (#7006).
    pub(super) rejected_invariants: FxHashSet<(PredicateId, ChcExpr)>,
    /// Pre-elimination error clause constraints (#1362 phases_m).
    pub(super) original_error_constraints: FxHashMap<usize, ChcExpr>,
}

impl PdrSolver {
    /// Escalate the active generalization strategy after convergence stagnation.
    ///
    /// Level 0 is the baseline production profile. Each call moves to the next
    /// more aggressive internal mode and returns `true`. Returns `false` once
    /// the highest configured level has already been reached.
    pub(crate) fn escalate_generalization_strategy(&mut self) -> bool {
        // Respect max_escalation_level cap (#7930). For DT+BV problems,
        // escalation is unproductive — PDR should return Unknown quickly
        // so budget goes to engines better suited for these problems.
        if self.generalization_escalation_level >= self.config.max_escalation_level {
            return false;
        }
        let from_level = self.generalization_escalation_level;
        let next_level = match self.generalization_escalation_level {
            0 => {
                self.config.use_farkas_combination = true;
                self.config.use_range_weakening = true;
                1
            }
            1 => {
                self.config.use_relational_equality = true;
                self.config.use_convex_closure = true;
                2
            }
            2 => {
                self.config.use_negated_equality_splits = true;
                self.config.max_frames = self.config.max_frames.max(200);
                3
            }
            _ => return false,
        };

        self.generalization_escalation_level = next_level;
        self.generalization_strategy = GeneralizationStrategy::from_escalation_level(next_level);

        // Record telemetry (#7918).
        self.telemetry
            .strategy
            .record_escalation(self.iterations, from_level, next_level);

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Escalating generalization strategy to level {} at iteration {} \
                 ({} stagnant windows, {}s since last frame advance): \
                 range_weakening={}, farkas={}, relational_equality={}, \
                 convex_closure={}, negated_equality_splits={}, max_frames={}",
                self.generalization_escalation_level,
                self.iterations,
                self.convergence.consecutive_stagnant_windows,
                self.convergence.time_since_frame_advance().as_secs(),
                self.config.use_range_weakening,
                self.config.use_farkas_combination,
                self.config.use_relational_equality,
                self.config.use_convex_closure,
                self.config.use_negated_equality_splits,
                self.config.max_frames,
            );
        }

        true
    }

    /// De-escalate generalization when near convergence (#7911).
    pub(crate) fn de_escalate_generalization_strategy(&mut self) -> bool {
        if self.generalization_strategy == GeneralizationStrategy::Conservative
            || self.generalization_strategy == GeneralizationStrategy::Default
        {
            return false;
        }
        let from_level = self.generalization_escalation_level;
        let new_level = from_level.saturating_sub(1);
        let new_strategy = if new_level == 0 {
            GeneralizationStrategy::Conservative
        } else {
            GeneralizationStrategy::from_escalation_level(new_level)
        };
        self.generalization_escalation_level = new_level;
        self.generalization_strategy = new_strategy;
        self.telemetry
            .strategy
            .record_de_escalation(self.iterations, from_level, new_level);
        if self.config.verbose {
            safe_eprintln!(
                "PDR: De-escalating generalization to {} (level {}) at iter {} (near-convergence)",
                self.generalization_strategy,
                self.generalization_escalation_level,
                self.iterations,
            );
        }
        true
    }
}

impl Drop for PdrSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
        // Iteratively drop all fields that may contain deep ChcExpr trees.
        // original_error_constraints holds cloned error clause constraints
        // which can be as deep as the original problem (#6847).
        for (_, expr) in std::mem::take(&mut self.original_error_constraints) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr, _, _) in std::mem::take(&mut self.deferred_entry_invariants) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr, _, _) in std::mem::take(&mut self.deferred_self_inductive_invariants) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr) in std::mem::take(&mut self.rejected_invariants) {
            ChcExpr::iterative_drop(expr);
        }
    }
}

/// Stub implementations for zone-merged observability methods.
impl PdrSolver {
    /// Emit a lemma lifecycle tracing event (stub).
    pub(super) fn emit_lemma_lifecycle_event(
        &mut self,
        _action: &str,
        _source: &str,
        _predicate: PredicateId,
        _level: usize,
        _formula: &ChcExpr,
    ) {
    }

    /// Try to concretize a proof obligation (stub — #4782).
    pub(super) fn try_concretize_pob(
        &mut self,
        _pob: &ProofObligation,
        _model: &Option<FxHashMap<String, SmtValue>>,
    ) -> bool {
        false
    }

    /// Record a point-block for concretize heuristic (stub — #4782).
    pub(super) fn record_point_block_for_concretize(
        &mut self,
        _predicate: PredicateId,
        _level: usize,
    ) {
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_tests/mod.rs"]
mod tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_tests_entry_domain.rs"]
mod entry_domain_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_spot_check_tests.rs"]
mod spot_check_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_solve_coverage_tests.rs"]
mod solve_coverage_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_entry_failure_stats_tests.rs"]
mod entry_failure_stats_tests;

#[cfg(test)]
mod generalization_strategy_tests {
    use super::GeneralizationStrategy;

    #[test]
    fn test_from_escalation_level() {
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(0),
            GeneralizationStrategy::Default
        );
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(1),
            GeneralizationStrategy::Aggressive
        );
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(3),
            GeneralizationStrategy::MaxAggressive
        );
    }

    #[test]
    fn test_failure_limits_monotonic() {
        let c = GeneralizationStrategy::Conservative.drop_literal_failure_limit();
        let d = GeneralizationStrategy::Default.drop_literal_failure_limit();
        let a = GeneralizationStrategy::Aggressive.drop_literal_failure_limit();
        let m = GeneralizationStrategy::MaxAggressive.drop_literal_failure_limit();
        assert!(c < d && d < a && a < m);
    }

    #[test]
    fn test_pipeline_composition_flags() {
        assert!(!GeneralizationStrategy::Conservative.use_early_aggressive_generalizers());
        assert!(GeneralizationStrategy::Default.use_early_aggressive_generalizers());
        assert!(!GeneralizationStrategy::Conservative.use_relational_generalizers());
        assert!(!GeneralizationStrategy::Default.use_relational_generalizers());
        assert!(GeneralizationStrategy::Aggressive.use_relational_generalizers());
        assert!(!GeneralizationStrategy::Conservative.use_bound_expansion());
        assert!(GeneralizationStrategy::Default.use_bound_expansion());
    }

    #[test]
    fn test_fixpoint_passes() {
        assert_eq!(GeneralizationStrategy::Default.fixpoint_passes(), 1);
        assert_eq!(GeneralizationStrategy::MaxAggressive.fixpoint_passes(), 2);
    }

    #[test]
    fn test_display() {
        assert_eq!(
            format!("{}", GeneralizationStrategy::Conservative),
            "conservative"
        );
        assert_eq!(format!("{}", GeneralizationStrategy::Default), "default");
        assert_eq!(
            format!("{}", GeneralizationStrategy::Aggressive),
            "aggressive"
        );
        assert_eq!(
            format!("{}", GeneralizationStrategy::MaxAggressive),
            "max-aggressive"
        );
    }

    #[test]
    fn test_max_escalation_level_default() {
        use crate::pdr::PdrConfig;
        let config = PdrConfig::default();
        assert_eq!(
            config.max_escalation_level, 3,
            "default should allow all escalation levels"
        );
    }

    #[test]
    fn test_max_escalation_level_dt_cap() {
        use crate::pdr::PdrConfig;
        let config = PdrConfig {
            max_escalation_level: 0,
            ..PdrConfig::default()
        };
        assert_eq!(config.max_escalation_level, 0, "DT cap should be 0");
    }
}
