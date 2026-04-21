// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver state layout: hot/cold field separation for BCP cache locality (#5090).
//!
//! Field order is significant: `#[repr(C)]` locks the memory layout so
//! BCP-hot fields occupy the first cache lines of the struct. Hot fields
//! are grouped first, warm fields next, cold fields last.
//! See `cold.rs` for the full field classification.

use super::*;

/// The CDCL SAT solver.
///
/// `#[repr(C)]` ensures deterministic field layout for cache locality (#5090).
/// BCP-hot fields are first so they occupy the initial cache lines.
#[repr(C)]
pub struct Solver {
    // ══════════════════════════════════════════════════════════════════════
    // HOT: BCP inner loop (accessed every propagation)
    // ══════════════════════════════════════════════════════════════════════
    /// Literal values indexed by literal index (CaDiCaL-style).
    /// `vals[lit.index()]` is 1 (true), -1 (false), or 0 (unassigned).
    /// Sole source of truth for assignment state (#3758 Phase 3).
    pub(super) vals: Vec<i8>,
    /// Watched literal lists
    pub(super) watches: WatchedLists,
    /// Unified inline clause arena (CaDiCaL-style, #3904).
    /// Contiguous header+literal storage for single-cache-line BCP.
    pub(super) arena: ClauseArena,
    /// Trail (sequence of assigned literals)
    pub(super) trail: Vec<Literal>,
    /// Trail limit for each decision level (index into trail)
    pub(super) trail_lim: Vec<usize>,
    /// Propagation queue head (index into trail)
    pub(super) qhead: usize,
    /// Current decision level
    pub(super) decision_level: u32,
    /// Per-variable AoS data: level + trail_pos + reason packed in 16 bytes.
    /// CaDiCaL-style: 4 variables per cache line for conflict analysis locality.
    /// Replaces separate `level`, `reason`, `trail_pos` arrays (#5090).
    pub(super) var_data: Vec<VarData>,
    /// Reusable SoA buffer for deferred watchers during propagation
    pub(super) deferred_watch_list: WatchList,
    /// Deferred replacement watches: (target_literal, watcher) pairs collected
    /// during BCP when a long clause finds an unassigned replacement literal.
    /// Instead of immediately adding the new watch to the replacement literal's
    /// watch list (which pollutes the cache during the hot BCP scan), entries
    /// are buffered here and flushed after the current literal's watch list
    /// processing completes. Kissat proplit.h pattern (#8041).
    pub(super) deferred_replacement_watches: Vec<(Literal, Watcher)>,
    /// Number of variables
    pub(super) num_vars: usize,
    /// Number of user-visible variables (excludes internal scope selectors)
    pub(super) user_num_vars: usize,
    /// Whether an empty clause has been added (formula is UNSAT)
    pub(super) has_empty_clause: bool,
    /// Statistics: number of propagations
    pub(super) num_propagations: u64,
    pub(super) no_conflict_until: usize,
    /// Search ticks per mode [0=focused, 1=stable]. Counts cache-line work in BCP.
    /// CaDiCaL restart.cpp:27, propagate.cpp:473.
    pub(super) search_ticks: [u64; 2],
    /// Whether we're in stable mode (infrequent restarts) vs focused mode (frequent restarts)
    pub(super) stable_mode: bool,
    /// Heuristic currently driving branch-variable selection.
    pub(super) active_branch_heuristic: BranchHeuristic,
    /// Whether we're currently in probing mode (level 1 propagation)
    pub(super) probing_mode: bool,
    /// Cached identity for the most recent propagation conflict.
    /// LRAT hint collection consults this instead of scanning the whole arena
    /// when the immediate `ClauseRef -> clause_id` mapping is unavailable.
    /// The ref gates the cache so stale IDs are never reused across conflicts.
    pub(super) last_conflict_clause_ref: Option<ClauseRef>,
    pub(super) last_conflict_clause_id: u64,
    // ══════════════════════════════════════════════════════════════════════
    // WARM: per-conflict / per-decision
    // ══════════════════════════════════════════════════════════════════════
    /// Total number of conflicts (for clause deletion scheduling)
    pub(super) num_conflicts: u64,
    /// Number of conflicts since last restart
    pub(super) conflicts_since_restart: u64,
    /// Statistics: number of decisions
    pub(super) num_decisions: u64,
    /// Variable selection heuristic
    pub(super) vsids: VSIDS,
    /// Conflict analyzer
    pub(super) conflict: ConflictAnalyzer,
    /// Phase saving: last polarity of each variable.
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    /// Kissat-style i8 avoids Option matching overhead in the hot path.
    pub(super) phase: Vec<i8>,
    /// Target phases: phases at longest conflict-free trail (for stable mode).
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    pub(super) target_phase: Vec<i8>,
    /// Best phases: best assignment seen (for rephasing).
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    pub(super) best_phase: Vec<i8>,
    /// Trail length when target phases were saved
    pub(super) target_trail_len: usize,
    /// Trail length when best phases were saved
    pub(super) best_trail_len: usize,
    /// When true, enqueue() skips phase saving. Set during vivification
    /// and lucky phase probing where decisions are artificial.
    /// CaDiCaL: `searching_lucky_phases` (internal.hpp).
    pub(super) suppress_phase_saving: bool,
    /// When true, `should_reduce_db()` returns false. Set during backbone
    /// probing to prevent clause deletion from invalidating the DRAT proof
    /// chain for backbone units (#7929). Without this, `reduce_db` can
    /// delete learned clauses from the probe that the backbone unit's RUP
    /// derivation depends on.
    pub(super) suppress_reduce_db: bool,
    /// Proof mediator (optional, supports DRAT and LRAT outputs).
    pub(super) proof_manager: Option<ProofManager>,
    /// Snapshot of proof mode at solve entry, for debug stability assertions.
    #[cfg(debug_assertions)]
    pub(super) solve_proof_mode: Option<bool>,
    /// Whether chronological backtracking is enabled
    pub(super) chrono_enabled: bool,
    /// Whether to use trail reuse heuristic for chrono BT (CaDiCaL-style)
    pub(super) chrono_reuse_trail: bool,
    /// Pure telemetry counters (write-only from hot paths, read for stats display).
    pub(crate) stats: solver_stats::SolverStats,
    /// Number of original (non-learned) clauses
    pub(super) num_original_clauses: usize,
    /// Number of units derived at level 0 (for propfixed tracking)
    pub(super) fixed_count: i64,
    /// Proof clause ID for inprocessing-derived units that have no `ClauseRef` reason.
    /// Indexed by `var.index()`. 0 means no provenance. Set when `emit_add` returns
    /// a proof clause ID but the unit is enqueued with `reason=None` (#4611).
    pub(super) unit_proof_id: Vec<u64>,
    /// Clause-indexed reason markers (epoch-stamped, avoids per-pass bool allocations).
    pub(super) reason_clause_marks: Vec<u32>,
    /// Current epoch for `reason_clause_marks`.
    pub(super) reason_clause_epoch: u32,
    /// Monotonic counter incremented on every reason-edge mutation (#3518).
    /// Compared against `reason_marks_synced_epoch` to skip redundant rebuilds.
    pub(super) reason_graph_epoch: u64,
    /// Last `reason_graph_epoch` value at which `reason_clause_marks` was rebuilt.
    pub(super) reason_marks_synced_epoch: u64,
    /// Persistent buffer for VMTF-sorted variable bumping (reused across conflicts).
    /// Eliminates per-conflict allocation in focused mode (CaDiCaL analyze.cpp:189).
    pub(super) bump_sort_buf: Vec<usize>,
    /// Persistent seen buffer for backbone analysis (reused across per-conflict calls).
    /// Eliminates per-call vec![false; num_vars] allocation in backbone_analyze_binary.
    /// CaDiCaL backbone.cpp:202-254 uses a persistent marks array.
    pub(super) backbone_seen: Vec<bool>,
    // Glue recomputation (CaDiCaL-style, analyze.cpp:206-240)
    pub(super) glue_stamp: Vec<u32>,
    pub(super) glue_stamp_counter: u32,
    // Block-level clause shrinking (CaDiCaL-style, shrink.cpp)
    pub(super) shrink_stamp: Vec<u32>,
    pub(super) shrink_stamp_counter: u32,
    pub(super) shrink_enabled: bool,
    pub(super) reap: reap::Reap,
    // Workspace vectors for per-conflict shrink allocations (reused via take/return)
    pub(super) ws_shrink_entries: Vec<(u32, usize, usize)>,
    pub(super) ws_shrink_result: Vec<Literal>,
    pub(super) ws_shrink_block_lits: Vec<Literal>,
    pub(super) ws_shrink_chain: Vec<u64>,
    pub(crate) tiers: tier_state::TierState,
    pub(crate) min: minimization_state::MinimizationState,
    pub(crate) phase_init: phase_init_state::PhaseInitState,
    pub(super) pending_theory_conflict: Option<ClauseRef>,
    /// Clauses marked pending-garbage (deferred HBR subsumption deletion).
    /// Incremented in probe_propagate, decremented in collect_level0_garbage.
    pub(super) pending_garbage_count: u32,
    /// True when watches have been disconnected for watch-free BVE
    /// (CaDiCaL fastelim.cpp:463 reset_watches pattern). While true,
    /// add_clause_watched skips watch attachment and BCP must not run.
    pub(super) watches_disconnected: bool,
    /// When true, `delete_clause_checked` skips the per-deletion O(num_vars)
    /// stale reason scan and instead pushes affected variable indices onto
    /// `stale_reasons`. Caller MUST call `clear_stale_reasons()` after the
    /// batch completes. This reduces bulk-deletion cost from
    /// O(deleted × num_vars) to O(stale_count).
    pub(super) defer_stale_reason_cleanup: bool,
    /// Minimal trail rewind after inprocessing (#8095).
    ///
    /// Tracks the earliest trail position affected during an inprocessing round.
    /// When a new unit is derived (enqueued on the trail) or a reason clause is
    /// deleted, this is updated to the minimum of the current value and the
    /// affected trail position. After inprocessing, `rebuild_watches` uses this
    /// to set `qhead` instead of rewinding to 0, avoiding O(trail × avg_watches)
    /// re-propagation of unaffected assignments.
    ///
    /// `None` means no trail positions were affected during the current
    /// inprocessing round (no new units, no deleted reasons). In that case,
    /// `qhead` is left at the trail length (no re-propagation needed beyond
    /// what was already propagated).
    pub(super) earliest_affected_trail_pos: Option<usize>,
    /// Variable indices with potentially stale reason references, collected
    /// during deferred-mode clause deletion. Bounded by the number of clause
    /// deletions per inprocessing round (typically hundreds, vs 100K+ total
    /// variables). Cleared by `clear_stale_reasons()`.
    pub(super) stale_reasons: Vec<u32>,
    /// Whether hyper-binary resolution is enabled during probing
    pub(super) hbr_enabled: bool,
    /// Reusable buffer for HBR clause literals (avoids allocation in hot loop)
    pub(super) hbr_lits: Vec<Literal>,
    /// Parent literal during probing, indexed by variable.
    pub(super) probe_parent: Vec<Option<Literal>>,
    /// Per-variable lifecycle state machine (CaDiCaL flags.hpp).
    /// Replaces the previous `eliminated: Vec<bool>` (#3906).
    pub(super) var_lifecycle: lifecycle::VarLifecycle,
    /// Shared mark array for inprocessing tautology/duplicate checks.
    pub(super) lit_marks: LitMarks,
    /// Per-variable subsume dirty bits (CaDiCaL flags.subsume).
    /// True = variable appeared in a clause added since last subsumption round.
    /// Used for incremental scheduling: only clauses with >= 2 dirty vars are candidates.
    pub(super) subsume_dirty: Vec<bool>,
    /// Centralized inprocessing scheduling: one `TechniqueControl` per technique.
    /// Replaces the flat `next_*` + `*_enabled` fields (#3546).
    pub(super) inproc_ctrl: inproc_control::InprocessingControls,
    /// Preprocessing quick mode: skip HTR, probing, conditioning, subsumption.
    /// CaDiCaL defaults to 0 full preprocessing rounds (internal.cpp:805).
    /// Quick path runs only: congruence, backbone, sweep, decompose, factor,
    /// fastelim. Heavy passes fire in the first inprocessing round (~2K conflicts).
    pub(super) preprocessing_quick_mode: bool,
    // Inprocessing engines (cold, separated for cache locality — #5090)
    /// All inprocessing engine instances, grouped into a sub-struct to keep
    /// them out of the Solver's hot BCP cache lines.
    pub(crate) inproc: inproc_engines::InprocessingEngines,
    // ══════════════════════════════════════════════════════════════════════
    // JIT: compiled BCP formula (FC-SAT, behind feature gate)
    // ══════════════════════════════════════════════════════════════════════
    #[cfg(feature = "jit")]
    pub(crate) compiled_formula: Option<z4_jit::CompiledFormula>,
    /// JIT staging trail: encoded literals written by JIT, applied to solver after call.
    #[cfg(feature = "jit")]
    pub(super) jit_staging_trail: Vec<u32>,
    /// JIT staging reasons: per-variable reason clause IDs written by JIT.
    #[cfg(feature = "jit")]
    pub(super) jit_staging_reasons: Vec<u32>,
    /// JIT clause guards: per-clause deletion bits for inprocessing support.
    #[cfg(feature = "jit")]
    pub(super) jit_guards: z4_jit::ClauseGuards,
    /// JIT propagation head: tracks which trail literals have been JIT-scanned.
    /// Separate from `qhead` (which standard BCP uses) so that every literal
    /// gets both JIT and 2WL treatment in the interleaved hybrid loop.
    #[cfg(feature = "jit")]
    pub(super) jit_qhead: usize,
    // ══════════════════════════════════════════════════════════════════════
    // COLD: boxed restart/proof/incremental/tracing state
    // ══════════════════════════════════════════════════════════════════════
    /// Boxed cold tail containing restart, proof, incremental, and tracing state.
    pub(super) cold: Box<cold::ColdState>,
}

/// Discriminated reason kind for a variable (#8034).
///
/// Used by conflict analysis and minimization to handle binary literal
/// reasons inline without arena access.
pub(crate) enum ReasonKind {
    /// Decision variable (no reason).
    Decision,
    /// Clause reason: arena offset.
    Clause(ClauseRef),
    /// Binary literal reason: the OTHER (false) literal from the binary clause.
    /// Stored as a tagged literal in `VarData.reason` (Kissat fastassign.h:12-19).
    BinaryLiteral(Literal),
}

impl Solver {
    /// Get the reason clause for a variable, or None if it's a decision variable
    /// or has a binary literal reason (#8034).
    ///
    /// Binary literal reasons return `None` because they have no `ClauseRef`.
    /// Callers that need to distinguish decisions from binary reasons should
    /// use `var_reason_kind()`.
    #[inline(always)]
    pub(crate) fn var_reason(&self, var_idx: usize) -> Option<ClauseRef> {
        let r = self.var_data[var_idx].reason;
        if r == NO_REASON || is_binary_literal_reason(r) {
            None
        } else {
            Some(ClauseRef(r))
        }
    }

    /// Get the discriminated reason kind for a variable (#8034).
    ///
    /// Returns `Decision` for unassigned or decision variables, `Clause` for
    /// clause reasons, or `BinaryLiteral` for binary literal reasons.
    #[inline(always)]
    pub(crate) fn var_reason_kind(&self, var_idx: usize) -> ReasonKind {
        let r = self.var_data[var_idx].reason;
        if r == NO_REASON {
            ReasonKind::Decision
        } else if is_binary_literal_reason(r) {
            ReasonKind::BinaryLiteral(Literal(binary_reason_lit(r)))
        } else {
            ReasonKind::Clause(ClauseRef(r))
        }
    }
}
