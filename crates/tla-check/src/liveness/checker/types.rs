// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Data types, type aliases, and debug flags for liveness checking.
//!
//! Extracted from `checker/mod.rs` to reduce file size. These types are
//! consumed by the checker submodules (scc_checks, checks, plan, eval)
//! and re-exported from `mod.rs` to maintain the existing public API.

#[cfg(test)]
use super::super::behavior_graph::BehaviorGraphNode;
use super::super::live_expr::LiveExpr;
use crate::state::State;
use crate::storage::{ActionBitmaskLookup, StateBitmaskLookup};

/// Precomputed edge list for an SCC: (from_node, from_state, [(to_node, to_state)]).
/// Built once per SCC and reused across PEM checks to avoid redundant State clones.
/// Test-only: production witness construction uses bitmask lookups (#2572).
#[cfg(test)]
pub(crate) type SccEdgeList = Vec<(BehaviorGraphNode, State, Vec<(BehaviorGraphNode, State)>)>;

// debug_flag! macro defined in crate::debug_env (via #[macro_use])

debug_flag!(pub(crate) debug_scc, "TLA2_DEBUG_SCC");
debug_flag!(pub(crate) debug_action_pred, "TLA2_DEBUG_ACTION_PRED");
debug_flag!(pub(crate) debug_changed, "TLA2_DEBUG_CHANGED");
debug_flag!(pub(crate) debug_subscript, "TLA2_DEBUG_SUBSCRIPT");
debug_flag!(pub(crate) debug_bindings, "TLA2_DEBUG_BINDINGS");

/// A path segment in a counterexample trace: list of (state, tableau_node_index) pairs
pub(crate) type CounterexamplePath = Vec<(State, usize)>;
/// A fingerprint-only counterexample path used when concrete state replay is
/// deferred to the caller.
pub(crate) type CounterexampleFingerprintPath = Vec<(crate::state::Fingerprint, usize)>;

/// Result of liveness checking
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LivenessResult {
    /// No liveness violation found
    Satisfied,
    /// Liveness violation found - includes counterexample
    Violated {
        /// Prefix of the counterexample (finite path to the cycle)
        prefix: Vec<(State, usize)>,
        /// The cycle itself (back edge goes from last to first)
        cycle: Vec<(State, usize)>,
    },
    /// Liveness violation found, but the checker intentionally avoided
    /// retaining a full state cache and is returning fingerprint paths only.
    ViolatedFingerprints {
        /// Prefix of the counterexample (finite path to the cycle)
        prefix: CounterexampleFingerprintPath,
        /// The cycle itself (back edge goes from last to first)
        cycle: CounterexampleFingerprintPath,
    },
    /// Internal runtime failure during liveness checking.
    ///
    /// This variant covers:
    /// - Tarjan SCC algorithm invariant violations
    /// - SCC constraint check failures
    /// - Counterexample construction failures
    RuntimeFailure {
        /// Description of the internal error
        reason: String,
    },
    /// Evaluation error during liveness checking (e.g., check mask population).
    ///
    /// Unlike `RuntimeFailure`, this preserves the typed `EvalError` so callers
    /// can detect `ExitRequested` and convert it to `LimitReached(Exit)` via
    /// `check_error_to_result`. Part of #2815 Phase B.
    EvalFailure {
        /// The evaluation error
        error: crate::error::EvalError,
    },
}

/// Constraints derived from fairness and temporal property patterns.
///
/// This corresponds to TLC's AE/EA checks (see `Liveness.classifyExpr`).
/// Test-only: used by `from_formula` test path and test helpers.
#[cfg(test)]
#[derive(Debug, Clone, Default)]
pub struct LivenessConstraints {
    /// State-level checks of the form `[]<>S` (must hold infinitely often).
    pub ae_state: Vec<LiveExpr>,
    /// Action-level checks of the form `[]<>A` (must occur infinitely often).
    pub ae_action: Vec<LiveExpr>,
    /// State-level checks of the form `<>[]S` (eventually always true states on suffix).
    pub ea_state: Vec<LiveExpr>,
    /// Action-level checks of the form `<>[]A` (eventually always true on the suffix).
    pub ea_action: Vec<LiveExpr>,
}

/// A PEM (Possible Error Model) plan storing index vectors into shared check bins.
///
/// Mirrors TLC's `PossibleErrorModel`: stores indices into the parent
/// `GroupedLivenessPlan`'s shared check arrays rather than owning expressions.
#[allow(clippy::struct_field_names)]
#[derive(Debug, Clone)]
pub struct PemPlan {
    /// Indices into parent's `check_action` for `<>[]A` checks
    pub ea_action_idx: Vec<usize>,
    /// Indices into parent's `check_state` for `<>[]S` checks
    pub ea_state_idx: Vec<usize>,
    /// Indices into parent's `check_state` for `[]<>S` checks
    pub ae_state_idx: Vec<usize>,
    /// Indices into parent's `check_action` for `[]<>A` checks
    pub ae_action_idx: Vec<usize>,
}

/// A grouped liveness plan: one tableau shared by multiple PEM disjuncts.
///
/// Mirrors TLC's `OrderOfSolution`: clauses with syntactically equivalent
/// temporal formulas (`tf`) are grouped so we build only one tableau and
/// explore the behavior graph once per group.
#[derive(Debug, Clone)]
pub struct GroupedLivenessPlan {
    /// The temporal formula for this group (what the tableau is built from).
    pub tf: LiveExpr,
    /// Shared deduplicated state-level check expressions.
    pub check_state: Vec<LiveExpr>,
    /// Shared deduplicated action-level check expressions.
    pub check_action: Vec<LiveExpr>,
    /// PEM disjuncts - each represents one DNF clause's constraint indices.
    pub pems: Vec<PemPlan>,
}

/// Precomputed inline leaf results for one liveness property (bitmask-only).
///
/// Each fingerprint's entry in the bitmask maps has bit `tag` set when the
/// result for that tag is TRUE. Presence of the fingerprint in the map means
/// all tags have been evaluated (even if all results are false, giving 0).
/// This replaces the per-tag `FxHashMap<(Fingerprint, u32), bool>` maps,
/// reducing memory from O(S×L) to O(S) for state results and O(T×L) to O(T)
/// for action results.
#[derive(Clone, Copy)]
pub(crate) struct InlineCheckResults<'a> {
    pub max_tag: u32,
    /// Read-only state tag bitmask lookup. Bit `tag` set when `(fp, tag) → true`.
    /// Fingerprint presence means all tags evaluated.
    pub state_bitmasks: &'a dyn StateBitmaskLookup,
    /// Read-only action tag bitmask lookup. Bit `tag` set when
    /// `(from_fp, to_fp, tag) → true`. Key presence means all tags evaluated.
    pub action_bitmasks: &'a dyn ActionBitmaskLookup,
}

/// Statistics for liveness checking
#[derive(Debug, Clone, Default)]
pub struct LivenessStats {
    /// Number of states explored
    pub states_explored: usize,
    /// Number of behavior graph nodes created
    pub graph_nodes: usize,
    /// Number of transitions in behavior graph
    pub graph_edges: usize,
    /// Number of consistency checks performed
    pub consistency_checks: usize,
    /// Subscript cache hits
    pub subscript_cache_hits: u64,
    /// Subscript cache misses
    pub subscript_cache_misses: u64,
    /// Subscript cache evictions
    pub subscript_cache_evictions: u64,
    /// ENABLED cache hits
    pub enabled_cache_hits: u64,
    /// ENABLED cache misses
    pub enabled_cache_misses: u64,
    /// ENABLED cache evictions
    pub enabled_cache_evictions: u64,
    /// Consistency cache hits
    pub consistency_cache_hits: u64,
    /// Consistency cache misses
    pub consistency_cache_misses: u64,
    /// State-env cache hits
    pub state_env_cache_hits: u64,
    /// State-env cache misses
    pub state_env_cache_misses: u64,
    /// Microseconds spent adding initial states
    pub init_state_time_us: u64,
    /// Microseconds spent adding successor states
    pub add_successors_time_us: u64,
    /// Microseconds spent computing state successors
    pub get_successors_time_us: u64,
    /// Microseconds spent cloning states from graph
    pub state_clone_time_us: u64,
}
