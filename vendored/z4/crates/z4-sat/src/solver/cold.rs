// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boxed cold solver state for BCP cache locality (#5090).
//!
//! The hot and warm portions of `Solver` stay inline in `state.rs`. The full
//! cold tail lives here behind a single box so restart/proof/incremental/
//! tracing state no longer inflates the main solver shell.

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModeLock {
    None,
    Stable,
}

/// Flat arena for the immutable original-clause ledger.
///
/// Replaces `Vec<Vec<Literal>>` to eliminate N separate heap allocations
/// and N Vec headers (24 bytes each). All literals are stored contiguously
/// with a parallel offset table for O(1) clause access.
///
/// Memory savings for 40K clauses: ~960KB (from ~2.0MB to ~640KB).
pub(crate) struct OriginalLedger {
    /// All original clause literals stored contiguously.
    literals: Vec<Literal>,
    /// Start offset (into `literals`) of each clause. Length = num_clauses.
    /// Clause `i` spans `literals[offsets[i] as usize .. end]` where
    /// `end = offsets[i+1]` (or `literals.len()` for the last clause).
    offsets: Vec<u32>,
}

impl OriginalLedger {
    pub(crate) fn new() -> Self {
        Self {
            literals: Vec::new(),
            offsets: Vec::new(),
        }
    }

    /// Append a clause to the ledger.
    #[inline]
    pub(crate) fn push_clause(&mut self, lits: &[Literal]) {
        debug_assert!(
            u32::try_from(self.literals.len()).is_ok(),
            "BUG: OriginalLedger literal count overflows u32"
        );
        self.offsets.push(self.literals.len() as u32);
        self.literals.extend_from_slice(lits);
    }

    /// Get clause at `index` as a slice.
    #[inline]
    pub(crate) fn clause(&self, index: usize) -> &[Literal] {
        debug_assert!(
            index < self.offsets.len(),
            "BUG: clause index out of bounds"
        );
        let start = self.offsets[index] as usize;
        let end = if index + 1 < self.offsets.len() {
            self.offsets[index + 1] as usize
        } else {
            self.literals.len()
        };
        &self.literals[start..end]
    }

    /// Number of clauses in the ledger.
    #[inline]
    pub(crate) fn num_clauses(&self) -> usize {
        self.offsets.len()
    }

    /// Whether the ledger is empty.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.offsets.is_empty()
    }

    /// Iterate over all clauses as slices.
    pub(crate) fn iter_clauses(&self) -> OriginalLedgerIter<'_> {
        OriginalLedgerIter {
            ledger: self,
            index: 0,
        }
    }

    /// Iterate over clauses starting from `start` index.
    pub(crate) fn iter_clauses_from(&self, start: usize) -> OriginalLedgerIter<'_> {
        debug_assert!(
            start <= self.offsets.len(),
            "BUG: iter_clauses_from start ({start}) > num_clauses ({})",
            self.offsets.len()
        );
        OriginalLedgerIter {
            ledger: self,
            index: start,
        }
    }

    /// Heap bytes used by this ledger (for memory stats).
    #[cfg(test)]
    pub(crate) fn heap_bytes(&self) -> usize {
        self.literals.capacity() * size_of::<Literal>() + self.offsets.capacity() * size_of::<u32>()
    }

    /// Collect all clauses to Vec<Vec<Literal>> (for tests/debug).
    #[cfg(test)]
    pub(crate) fn to_vec_of_vecs(&self) -> Vec<Vec<Literal>> {
        self.iter_clauses().map(<[Literal]>::to_vec).collect()
    }
}

/// Iterator over clauses in an `OriginalLedger`.
pub(crate) struct OriginalLedgerIter<'a> {
    ledger: &'a OriginalLedger,
    index: usize,
}

impl<'a> Iterator for OriginalLedgerIter<'a> {
    type Item = &'a [Literal];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.ledger.offsets.len() {
            return None;
        }
        let clause = self.ledger.clause(self.index);
        self.index += 1;
        Some(clause)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.ledger.offsets.len().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for OriginalLedgerIter<'_> {}

/// Cold solver state that is not needed on the BCP fast path.
pub(crate) struct ColdState {
    // Glucose-style EMA restart state (ADAM bias-corrected, CaDiCaL ema.cpp)
    /// Bias-corrected fast EMA of LBD (short window, ~32 conflicts)
    pub(super) lbd_ema_fast: f64,
    /// Bias-corrected slow EMA of LBD (long window, ~100K conflicts)
    pub(super) lbd_ema_slow: f64,
    /// Raw (biased) fast EMA before correction
    pub(super) lbd_ema_fast_biased: f64,
    /// Raw (biased) slow EMA before correction
    pub(super) lbd_ema_slow_biased: f64,
    /// Bias correction exponent: beta_fast^n (decays toward 0)
    pub(super) lbd_ema_fast_exp: f64,
    /// Bias correction exponent: beta_slow^n (decays toward 0)
    pub(super) lbd_ema_slow_exp: f64,
    pub(super) saved_lbd_ema_fast: f64,
    pub(super) saved_lbd_ema_slow: f64,
    pub(super) saved_lbd_ema_fast_biased: f64,
    pub(super) saved_lbd_ema_slow_biased: f64,
    pub(super) saved_lbd_ema_fast_exp: f64,
    pub(super) saved_lbd_ema_slow_exp: f64,
    pub(super) ema_swapped: bool,
    /// Whether to use Glucose-style restarts (true) or Luby restarts (false)
    pub(super) glucose_restarts: bool,
    /// Trail-length EMA (slow) for restart blocking (Audemard & Simon SAT 2012).
    pub(super) trail_ema_slow: f64,
    /// Number of trail EMA updates (for warmup gating).
    pub(super) trail_ema_count: u64,
    /// Count of restarts blocked by trail-length heuristic (diagnostics).
    pub(super) trail_blocked_restarts: u64,
    /// Whether to use geometric restart schedule (overrides glucose/Luby when true).
    /// Z3 uses geometric restarts for QF_LRA: next_restart = initial * factor^n.
    pub(super) geometric_restarts: bool,
    /// Initial restart interval for geometric restarts (conflicts). Z3 default: 100.
    pub(super) geometric_initial: f64,
    /// Growth factor for geometric restarts. Z3 default: 1.1.
    pub(super) geometric_factor: f64,
    /// Minimum conflicts before considering restart (initial stabilization)
    pub(super) restart_min_conflicts: u64,
    /// Current index into the Luby sequence
    pub(super) luby_idx: u32,
    /// Base restart interval (conflicts per Luby unit)
    pub(super) restart_base: u64,
    /// Total number of restarts performed
    pub(super) restarts: u64,
    /// Conflict count when stabilization mode was last switched (first phase only)
    pub(super) stable_mode_start_conflicts: u64,
    /// Length of current stabilization phase in conflicts (first phase only)
    pub(super) stable_phase_length: u64,
    /// Counter for stable phase number (used to increase phase length)
    pub(super) stable_phase_count: u64,
    /// Total number of stable/focused mode switches.
    /// Kissat uses this to inject deterministic focused-mode polarity cycles.
    pub(super) mode_switch_count: u64,
    /// Search-mode lock for SAT-tuned DIMACS profiles.
    pub(super) mode_lock: ModeLock,
    /// Cumulative ticks charged during probe BCP.
    /// CaDiCaL stats.ticks.probe (stats.hpp:36).
    pub(super) probe_ticks: u64,
    /// Cumulative ticks charged during vivify BCP.
    /// CaDiCaL stats.ticks.vivify.
    pub(super) vivify_ticks: u64,
    /// Tick increment for stabilization phases. 0 = not yet bootstrapped (first phase
    /// uses conflicts). After the first phase switch, bootstrapped from that phase's
    /// tick delta. CaDiCaL restart.cpp:53-54.
    pub(super) stabilize_tick_inc: u64,
    /// Branch heuristic selector mode.
    pub(super) branch_selector_mode: BranchSelectorMode,
    /// Restart-boundary MAB controller state.
    pub(super) branch_mab: MabController,
    /// Tick limit for the current stabilization phase (absolute tick count for the
    /// current mode). CaDiCaL restart.cpp:64.
    pub(super) stabilize_tick_limit: u64,
    /// Knuth reluctant doubling state u (see reference/cadical/src/reluctant.hpp)
    pub(super) reluctant_u: u64,
    /// Knuth reluctant doubling state v (current Luby sequence value)
    pub(super) reluctant_v: u64,
    /// Countdown: conflicts remaining before next reluctant restart fires
    pub(super) reluctant_countdown: u64,
    /// Conflict count at last reluctant tick (for delta computation)
    pub(super) reluctant_ticked_at: u64,
    /// When to next run clause deletion
    pub(super) next_reduce_db: u64,
    /// Total number of clause DB reductions performed.
    /// CaDiCaL: `stats.reductions` (reduce.cpp:216).
    pub(super) num_reductions: u64,
    /// Arena word-offset boundary: clauses at offsets < this are original (non-learned).
    pub(super) original_clause_boundary: usize,
    /// Reduction count at last inprocessing probe round.
    /// Used to skip redundant probe calls when no new reductions occurred.
    pub(super) last_inprobe_reduction: u64,
    /// Next conflict count at which to run inprocessing probe.
    /// CaDiCaL: `lim.inprobe` (probe.cpp:980-981).
    /// Formula: `conflicts + 25 * INPROBE_INTERVAL * floor_log10(phase + 9)`.
    pub(super) next_inprobe_conflict: u64,
    /// Number of completed inprocessing probe phases (for logarithmic interval growth).
    /// CaDiCaL: tracks `phases` in probe scheduling (probe.cpp:979-981).
    pub(super) inprobe_phases: u64,
    /// Cached result of `is_uniform_nonbinary_irredundant_formula()`.
    /// `None` = dirty (needs recomputation), `Some(v)` = cached result.
    /// Invalidated when irredundant clauses are added, deleted, or strengthened.
    /// Avoids O(total_clauses) iteration on every inprocessing call (#7905).
    pub(super) uniform_formula_cache: Option<bool>,
    /// Trail of learned clause arena offsets for eager subsumption.
    /// CaDiCaL walks backward through its `clauses` vector; Z4 uses this
    /// equivalent trail to find the most recently learned clauses.
    pub(super) learned_clause_trail: Vec<usize>,
    /// Number of clauses removed by eager subsumption (CaDiCaL `stats.eagersub`).
    pub(super) num_eager_subsumptions: u64,
    /// Conflict count at which to next run clause flush (CaDiCaL reduce.cpp:26-30).
    /// Flush is more aggressive than reduce -- marks ALL unused learned clauses
    /// as garbage regardless of tier. Grows geometrically by `FLUSH_FACTOR`.
    pub(super) next_flush: u64,
    /// Current flush interval increment (grows by `FLUSH_FACTOR` after each flush).
    pub(super) flush_inc: u64,
    /// Number of flush operations performed.
    pub(super) num_flushes: u64,
    /// Number of learned clauses eagerly subsumed per-conflict (#5136).
    /// CaDiCaL: stats.eagersub (analyze.cpp:754).
    pub(super) eager_subsumed: u64,
    /// Maximum number of learned clauses (None = no limit).
    ///
    /// When exceeded, trigger aggressive clause database reduction.
    pub(super) max_learned_clauses: Option<usize>,
    /// Maximum clause database memory in bytes (None = no limit).
    ///
    /// When exceeded, trigger aggressive clause database reduction and arena compaction.
    pub(super) max_clause_db_bytes: Option<usize>,
    /// Bumpreason rate-limiting: decisions at last conflict (CaDiCaL saved_decisions).
    /// Used to compute per-conflict decision rate for reason bump gating.
    pub(super) bumpreason_saved_decisions: u64,
    /// Bumpreason rate-limiting: EMA of decisions per conflict (CaDiCaL averages.current.decisions).
    /// When this exceeds BUMPREASON_RATE_LIMIT (100), reason bumping is skipped.
    pub(super) bumpreason_decision_rate: f64,
    /// Bumpreason adaptive delay: remaining conflicts to skip before re-enabling.
    /// Per-mode array `[focused, stable]` matching CaDiCaL's `delay[stable].bumpreasons.limit`.
    /// Reason bumping adapts independently in each mode because focused mode has
    /// high decision rates (many bumps wasted) while stable mode has low rates
    /// (bumps are useful). A global counter would carry stale delay from one mode
    /// into the other after a mode switch.
    pub(super) bumpreason_delay_remaining: [u64; 2],
    /// Bumpreason adaptive delay: current interval (doubles on wasted bumps, halves on useful ones).
    /// Per-mode array `[focused, stable]` matching CaDiCaL's `delay[stable].bumpreasons.interval`.
    pub(super) bumpreason_delay_interval: [u64; 2],
    /// `search_ticks` at the last learned vivification round. The delta
    /// `search_ticks - last_vivify_ticks` determines the tick budget.
    pub(super) last_vivify_ticks: u64,
    /// `search_ticks` at the last irredundant vivification round.
    pub(super) last_vivify_irred_ticks: u64,
    /// Adaptive delay multiplier for irredundant vivification interval.
    pub(super) vivify_irred_delay_multiplier: u64,
    // Random decision injection (CaDiCaL-style)
    /// Countdown of remaining random decisions in current burst (0 = inactive)
    pub(super) randomized_deciding: u64,
    /// Number of random decision phases completed
    pub(super) random_decision_phases: u64,
    /// Conflict count at which the next random decision burst starts
    pub(super) next_random_decision: u64,
    /// Per-decision random variable frequency (Z3-style). 0.0 = disabled (default).
    /// Z3 default for SMT: 0.01 (1% of decisions are random).
    pub(super) random_var_freq: f64,
    /// BVE effort as per-mille of cumulative search propagations.
    pub(super) bve_effort_permille: u64,
    /// Subsumption effort as per-mille of cumulative search propagations.
    pub(super) subsume_effort_permille: u64,
    // Bounded Variable Elimination state
    /// Number of completed BVE phases (for CaDiCaL-style growing interval)
    pub(super) bve_phases: u32,
    /// fixed_count at last BVE run (fixpoint guard: skip if no new units)
    pub(super) last_bve_fixed: i64,
    /// Count of irredundant clause modification events from subsumption/vivification/decompose.
    /// CaDiCaL equivalent: `stats.mark.elim` (internal.hpp:1117-1124).
    /// BVE re-triggers when `last_bve_marked != bve_marked`.
    pub(super) bve_marked: u64,
    /// bve_marked at last BVE run (fixpoint guard).
    /// CaDiCaL equivalent: `last.elim.marked` (elim.cpp:79).
    pub(super) last_bve_marked: u64,
    /// Clause-count resume threshold for BVE.
    /// BVE stays disabled while the current clause count is at or above this
    /// value. After a shrinking phase this is the post-phase clause count;
    /// after a growing phase it remains the stricter pre-phase baseline.
    pub(super) last_bve_clauses: usize,
    /// fixed_count at last level-0 garbage collection (fixpoint guard: skip if no new units).
    /// CaDiCaL equivalent: `last.collect.fixed < stats.all.fixed` in collect.cpp.
    pub(super) last_collect_fixed: i64,
    /// Clause DB mutation counter (incremented by add/delete/replace during inprocessing).
    pub(super) clause_db_changes: u64,
    /// Cumulative BVE resolution count (for effort limiting, CaDiCaL: stats.elimres).
    pub(super) bve_resolutions: u64,
    // Factorization state
    /// Factorization stats: total rounds
    pub(super) factor_rounds: u64,
    /// Factorization stats: total factored groups
    pub(super) factor_factored_total: u64,
    /// Factorization stats: total extension variables introduced
    pub(super) factor_extension_vars_total: u64,
    /// Per-variable signed factor candidate marks (CaDiCaL `Flags::factor`):
    /// bit0 = positive literal marked, bit1 = negative literal marked.
    pub(super) factor_candidate_marks: Vec<u8>,
    /// Monotonic epoch tracking irredundant clause mutations relevant to factoring.
    pub(super) factor_marked_epoch: u64,
    /// Last `factor_marked_epoch` consumed by a completed factor round.
    pub(super) factor_last_completed_epoch: u64,
    /// Search ticks at last factor call. Used to compute tick-proportional effort.
    /// CaDiCaL: `last.factor.ticks` (factor.cpp:962).
    pub(super) last_factor_ticks: u64,
    /// Search ticks at last sweep call. Used for proportional sweep effort
    /// and tick-threshold scheduling (#7905, #8090).
    pub(super) last_sweep_ticks: u64,
    /// Search ticks at last backbone call. Used for tick-threshold scheduling (#8090).
    /// CaDiCaL: `last.backbone.ticks` (backbone.cpp).
    pub(super) last_backbone_ticks: u64,
    /// Number of completed backbone phases. Used to enforce the round limit
    /// (`BACKBONE_MAX_ROUNDS`). CaDiCaL: `stats.backbone.phases` (backbone.cpp:533).
    pub(super) backbone_phases: u32,
    /// Wall-clock overhead (milliseconds) of the most recent inprocessing round's
    /// infrastructure work: rebuild_watches, sort_all_binary_first, trail
    /// re-propagation. Used by adaptive tick-threshold scaling (#8099).
    /// When incremental state maintenance reduces this overhead, techniques
    /// can fire more frequently.
    pub(super) last_inprocessing_overhead_ms: f64,
    /// Level-0 assignments for eliminated variables, saved during compaction.
    /// External → internal variable index. Indexed by external var index.
    /// `e2i[ext_var]` = internal var index, or `UNMAPPED` if compacted away.
    /// Length: max external var + 1. Grows monotonically (never shrinks).
    /// Reference: CaDiCaL `external.hpp:64`.
    pub(super) e2i: Vec<u32>,
    /// Internal → external variable index. Indexed by internal var index.
    /// `i2e[int_var]` = external var index.
    /// Length: current `num_vars`. Rebuilt during compaction.
    /// Reference: CaDiCaL `internal.hpp:222`.
    pub(super) i2e: Vec<u32>,
    /// Next conflict count at which compaction is eligible.
    /// CaDiCaL compact.cpp:540-541: `lim.compact = conflicts + compactint * (compacts + 1)`.
    pub(super) compact_next_conflict: u64,
    /// Number of compactions performed so far.
    pub(super) compact_count: u64,
    /// Reference counts for frozen variables (protected from elimination)
    pub(super) freeze_counts: Vec<u32>,
    // LRAT proof support
    /// Clause IDs for LRAT proofs (maps clause index to clause ID)
    /// Original clauses get IDs 1..n, learned clauses get n+1, n+2, etc.
    pub(super) clause_ids: Vec<u64>,
    /// Per-variable LRAT clause ID fallback for level-0 variables whose reason
    /// clause was deleted via `ReasonPolicy::ClearLevel0`. Without this, chain
    /// collectors skip such variables, producing incomplete LRAT hints (#4617).
    pub(super) level0_proof_id: Vec<u64>,
    /// Next clause ID to assign (for derived clauses and id-sync with proof writer)
    pub(super) next_clause_id: u64,
    /// Next original clause ID to assign (1-indexed, increments for each non-derived clause).
    /// Original clauses in LRAT are pre-registered at IDs 1..=num_originals, and this
    /// counter tracks which original ID to assign next. Keeps original clause IDs
    /// consistent with the LRAT proof even when derived clauses/deletions advance
    /// next_clause_id past the original range.
    pub(super) next_original_clause_id: u64,
    /// Whether LRAT proof generation is enabled (track resolution chains)
    pub(super) lrat_enabled: bool,
    /// Whether the empty clause derivation was already written to proof_manager.
    /// Prevents duplicate empty-clause entries between mark_empty_clause and
    /// finalize_unsat_proof (#4123).
    pub(super) empty_clause_in_proof: bool,
    /// LRAT clause ID assigned to the empty clause derivation, if any.
    /// Used by pop() to emit a deletion step when retracting scoped UNSAT (#4475).
    pub(super) empty_clause_lrat_id: Option<u64>,
    /// Scope depth at which has_empty_clause was first set.
    /// Used by pop() to preserve base-level (depth 0) UNSAT.
    pub(super) empty_clause_scope_depth: usize,
    // In-memory clause trace for SMT proof reconstruction
    /// Optional clause trace (only active when SMT proof production is enabled)
    pub(super) clause_trace: Option<ClauseTrace>,
    /// Stack of active scope selector variables (for push/pop)
    pub(super) scope_selectors: Vec<Variable>,
    /// LRAT axiom IDs for scope selector negations, parallel to scope_selectors.
    /// Each entry is the LRAT ID assigned to [¬selector] during push().
    /// Used by finalize_unsat_proof to include axiom IDs in empty clause hints.
    /// Only populated in debug builds (LRAT checker is debug-only).
    #[cfg(debug_assertions)]
    pub(super) scope_selector_axiom_ids: Vec<u64>,
    /// Whether the solver has ever entered incremental mode (push/pop).
    /// Once set, clause-deleting inprocessing techniques (conditioning, BVE,
    /// BCE, sweep, congruence, factor) are permanently disabled because their
    /// reconstruction-based model recovery interacts unsoundly with learned
    /// clauses from scoped solving (#3662).
    pub(super) has_been_incremental: bool,
    /// Whether push() has ever been called. Once set, the `original_ledger`
    /// may contain clauses with scope-selector literals that are no
    /// longer asserted after pop(). `verify_against_original` must be skipped
    /// in this case because those clauses may be unsatisfied.
    /// Multi-solve without push/pop (assumption-based incremental, e.g. CHC)
    /// does NOT set this flag — `original_ledger` remains a sound ledger.
    pub(super) has_ever_scoped: bool,
    /// Whether `init_solve()` has been called at least once. Used to detect
    /// multi-solve scenarios (solve→solve without push/pop) where destructive
    /// inprocessing must be disabled to prevent formula corruption (#5031).
    pub(super) has_solved_once: bool,
    /// When true, theory lemmas from extension callbacks use `TrustedTransform`
    /// proof emission instead of `Axiom` and do NOT block LRAT mode (#7913).
    ///
    /// Set by `prepare_preprocessing_extension` when a preprocessing extension
    /// (e.g., XOR Gauss-Jordan) consumes original clauses and replaces them
    /// with equivalent theory propagations/conflicts. These extension-derived
    /// clauses are logical consequences of the consumed originals and do not
    /// require the full LRAT block that SMT theory lemmas need.
    pub(crate) extension_trusted_lemmas: bool,
    /// O(1) lookup for scope selectors during UNSAT core filtering
    pub(super) scope_selector_set: Vec<bool>,
    /// Permanent record of variables ever used as scope selectors.
    /// Unlike `scope_selector_set` (cleared on pop), this is never cleared.
    /// Used by `verify_against_original` to skip clauses containing scope
    /// selector literals when `has_ever_scoped` is true (#5522).
    pub(super) was_scope_selector: Vec<bool>,
    /// Clauses removed by conditioning's root-satisfied GC (#5106).
    /// These clauses are satisfied at level 0 and safe to remove within a single
    /// solve, but must be restored by `reset_search_state()` for incremental use
    /// because level-0 assignments are wiped between solves.
    pub(super) root_satisfied_saved: Vec<Vec<Literal>>,
    /// Set by inprocessing (decompose/congruence) when clause_db is permanently
    /// modified (clauses deleted or replaced) without reconstruction entries.
    /// Checked by `reset_search_state()` to trigger clause_db rebuild from
    /// `original_ledger` on the next solve (#5031).
    pub(super) inprocessing_modified_clause_db: bool,
    // Rephasing and phase initialization
    pub(super) rephase_enabled: bool,
    pub(super) rephase_count: u64,
    pub(super) rephase_count_stable: u64,
    pub(super) rephase_count_focused: u64,
    pub(super) next_rephase: u64,
    // Preprocessing and runtime tracing
    pub(super) preprocess_enabled: bool,
    pub(super) preprocess_watches_valid: bool,
    pub(super) symmetry_enabled: bool,
    pub(super) symmetry_stats: crate::symmetry::SymmetryStats,
    pub(super) tla_trace: Option<TlaTraceWriter>,
    pub(super) diagnostic_trace: Option<SatDiagnosticWriter>,
    pub(super) decision_trace: Option<DecisionTraceWriter>,
    pub(super) replay_trace: Option<ReplayTrace>,
    pub(super) diagnostic_pass: DiagnosticPass,
    pub(super) solution_witness: Option<Vec<Option<bool>>>,
    pub(super) forward_checker: Option<crate::forward_checker::ForwardChecker>,
    pub(super) last_unknown_reason: Option<SatUnknownReason>,
    /// Detail string explaining WHY the last Unknown was produced (#7917).
    /// Populated when finalization fails (e.g., which original clause was
    /// unsatisfied, reconstruction panic details).
    pub(super) last_unknown_detail: Option<String>,
    /// Number of times finalize_sat_model has failed in the current solve call.
    /// When this exceeds MAX_FINALIZE_SAT_RETRIES, the solver gives up and
    /// returns Unknown. Reset at each solve entry (#7917).
    pub(super) finalize_sat_fail_count: u32,
    pub(super) interrupt: Option<Arc<AtomicBool>>,
    pub(super) process_memory_interrupt: bool,
    /// Cached check: `Z4_TRACE_EXT_CONFLICT` env var was set at solver creation.
    /// Avoids repeated `std::env::var()` syscalls in the CDCL hot loop (#perf).
    pub(super) trace_ext_conflict: bool,
    /// Cached `Z4_BVE_LIMIT` env var. Avoids per-candidate syscalls in BVE loop.
    pub(super) bve_limit: Option<usize>,
    /// Cached `Z4_BVE_TRACE` env var. Avoids per-elimination syscalls in BVE loop.
    pub(super) bve_trace: bool,
    // Progress reporting
    /// Whether periodic progress lines should be emitted to stderr.
    pub(super) progress_enabled: bool,
    /// Wall-clock time of the last progress line emission.
    pub(super) last_progress_time: Option<std::time::Instant>,
    /// Wall-clock time when the current solve() call started.
    pub(super) solve_start_time: Option<std::time::Instant>,
    // Immutable original-formula ledger and proof/debug helpers
    #[cfg(z4_logging)]
    pub(super) log_enabled: bool,
    /// Flat arena for the immutable original-clause ledger.
    /// Replaces `Vec<Vec<Literal>>` to eliminate per-clause heap allocations.
    pub(super) original_ledger: OriginalLedger,
    pub(super) incremental_original_boundary: usize,
    #[cfg(debug_assertions)]
    pub(super) pending_forward_check: Option<u64>,
}

impl ColdState {
    /// Create the full cold solver tail for `Solver::build`.
    pub(crate) fn new(num_vars: usize, clauses_capacity: usize, lrat_enabled: bool) -> Self {
        Self {
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
            lbd_ema_fast_biased: 0.0,
            lbd_ema_slow_biased: 0.0,
            lbd_ema_fast_exp: 1.0,
            lbd_ema_slow_exp: 1.0,
            saved_lbd_ema_fast: 0.0,
            saved_lbd_ema_slow: 0.0,
            saved_lbd_ema_fast_biased: 0.0,
            saved_lbd_ema_slow_biased: 0.0,
            saved_lbd_ema_fast_exp: 1.0,
            saved_lbd_ema_slow_exp: 1.0,
            ema_swapped: false,
            glucose_restarts: true,
            trail_ema_slow: 0.0,
            trail_ema_count: 0,
            trail_blocked_restarts: 0,
            geometric_restarts: false,
            geometric_initial: 100.0,
            geometric_factor: 1.1,
            restart_min_conflicts: RESTART_MIN_CONFLICTS,
            luby_idx: 1,
            restart_base: DEFAULT_RESTART_BASE,
            restarts: 0,
            stable_mode_start_conflicts: 0,
            stable_phase_length: STABLE_PHASE_INIT,
            stable_phase_count: 0,
            mode_switch_count: 0,
            mode_lock: ModeLock::None,
            probe_ticks: 0,
            vivify_ticks: 0,
            stabilize_tick_inc: 0,
            branch_selector_mode: BranchSelectorMode::LegacyCoupled,
            branch_mab: MabController::new(),
            stabilize_tick_limit: 0,
            reluctant_u: 1,
            reluctant_v: 1,
            reluctant_countdown: RELUCTANT_INIT,
            reluctant_ticked_at: 0,
            next_reduce_db: FIRST_REDUCE_DB,
            num_reductions: 0,
            original_clause_boundary: 0,
            last_inprobe_reduction: 0,
            next_inprobe_conflict: 0,
            inprobe_phases: 0,
            uniform_formula_cache: None,
            learned_clause_trail: Vec::new(),
            num_eager_subsumptions: 0,
            next_flush: FLUSH_INIT,
            flush_inc: FLUSH_INIT,
            num_flushes: 0,
            eager_subsumed: 0,
            max_learned_clauses: None,
            max_clause_db_bytes: None,
            bumpreason_saved_decisions: 0,
            bumpreason_decision_rate: 0.0,
            bumpreason_delay_remaining: [0; 2],
            bumpreason_delay_interval: [0; 2],
            last_vivify_ticks: 0,
            last_vivify_irred_ticks: 0,
            vivify_irred_delay_multiplier: 1,
            randomized_deciding: 0,
            random_decision_phases: 0,
            next_random_decision: 1000,
            random_var_freq: 0.0,
            bve_effort_permille: BVE_EFFORT_PER_MILLE,
            subsume_effort_permille: SUBSUME_EFFORT_PER_MILLE,
            bve_phases: 0,
            last_bve_fixed: -1,
            bve_marked: 0,
            last_bve_marked: 0,
            last_bve_clauses: 0,
            last_collect_fixed: -1,
            clause_db_changes: 0,
            bve_resolutions: 0,
            factor_rounds: 0,
            factor_factored_total: 0,
            factor_extension_vars_total: 0,
            factor_candidate_marks: vec![0; num_vars],
            factor_marked_epoch: 1,
            factor_last_completed_epoch: 0,
            last_factor_ticks: 0,
            last_sweep_ticks: 0,
            last_backbone_ticks: 0,
            backbone_phases: 0,
            last_inprocessing_overhead_ms: 0.0,
            e2i: (0..num_vars as u32).collect(),
            i2e: (0..num_vars as u32).collect(),
            compact_next_conflict: 0,
            compact_count: 0,
            freeze_counts: vec![0; num_vars],
            // Always allocate clause_ids unconditionally (#8069: Phase 2a).
            // Clause IDs are the foundation for deferred backward proof
            // reconstruction and must be tracked even when LRAT mode is not
            // explicitly enabled.
            clause_ids: Vec::with_capacity(clauses_capacity),
            level0_proof_id: vec![0; num_vars],
            next_clause_id: 1,
            next_original_clause_id: 1,
            lrat_enabled,
            empty_clause_in_proof: false,
            empty_clause_lrat_id: None,
            empty_clause_scope_depth: 0,
            clause_trace: None,
            scope_selectors: Vec::new(),
            #[cfg(debug_assertions)]
            scope_selector_axiom_ids: Vec::new(),
            has_been_incremental: false,
            has_ever_scoped: false,
            has_solved_once: false,
            extension_trusted_lemmas: false,
            scope_selector_set: vec![false; num_vars],
            was_scope_selector: vec![false; num_vars],
            root_satisfied_saved: Vec::new(),
            inprocessing_modified_clause_db: false,
            rephase_enabled: true,
            rephase_count: 0,
            rephase_count_stable: 0,
            rephase_count_focused: 0,
            next_rephase: REPHASE_INITIAL,
            preprocess_enabled: true,
            preprocess_watches_valid: false,
            symmetry_enabled: true,
            symmetry_stats: crate::symmetry::SymmetryStats::default(),
            tla_trace: None,
            diagnostic_trace: None,
            decision_trace: None,
            replay_trace: None,
            diagnostic_pass: DiagnosticPass::None,
            solution_witness: None,
            forward_checker: None,
            last_unknown_reason: None,
            last_unknown_detail: None,
            finalize_sat_fail_count: 0,
            interrupt: None,
            process_memory_interrupt: false,
            trace_ext_conflict: std::env::var("Z4_TRACE_EXT_CONFLICT").is_ok(),
            bve_limit: std::env::var("Z4_BVE_LIMIT")
                .ok()
                .and_then(|s| s.parse::<usize>().ok()),
            bve_trace: std::env::var("Z4_BVE_TRACE").is_ok(),
            progress_enabled: false,
            last_progress_time: None,
            solve_start_time: None,
            #[cfg(z4_logging)]
            log_enabled: std::env::var("Z4_LOG").is_ok_and(|v| v == "1"),
            original_ledger: OriginalLedger::new(),
            incremental_original_boundary: 0,
            #[cfg(debug_assertions)]
            pending_forward_check: None,
        }
    }
}
