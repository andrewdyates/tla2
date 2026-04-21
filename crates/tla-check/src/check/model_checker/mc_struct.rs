// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    Arc, ArrayState, CapacityStatus, CheckError, CheckStats, Config, DetectedAction, Duration,
    EvalCtx, Expr, FairnessConstraint, Fingerprint, FingerprintSet, FpHashMap, FxHashMap,
    InitProgressCallback, InlineLivenessPropertyPlan, Instant, LiveExpr, LivenessMode, OperatorDef,
    PathBuf, ProgressCallback, Spanned, State, TraceFile, TraceLocationStorage,
    TraceLocationsStorage,
};
use crate::storage::{ActionBitmaskMap, StateBitmaskMap, SuccessorGraph};

pub(super) use super::liveness::inline_fairness::EnabledActionGroup;
pub(super) use super::liveness::inline_fairness::EnabledProvenanceEntry;
pub(super) use super::liveness::inline_fairness::SubscriptActionPair;

/// Part of #4128: Identity hash for Fingerprint-keyed maps (pre-hashed keys).
pub(super) type SuccessorWitnessCache = FpHashMap<Vec<(Fingerprint, ArrayState)>>;

/// Checkpoint state for periodic model checking saves.
pub(super) struct CheckpointState {
    /// Directory for saving checkpoints during model checking
    pub(super) dir: Option<PathBuf>,
    /// Interval between checkpoints (in seconds)
    pub(super) interval: Duration,
    /// Time of last checkpoint
    pub(super) last_time: Option<Instant>,
    /// Spec path for checkpoint metadata
    pub(super) spec_path: Option<String>,
    /// Config path for checkpoint metadata
    pub(super) config_path: Option<String>,
    /// SHA-256 hash of spec file content (for checkpoint resume validation)
    pub(super) spec_hash: Option<String>,
    /// SHA-256 hash of config file content (for checkpoint resume validation)
    pub(super) config_hash: Option<String>,
}

/// Module metadata: names, paths, assumptions, variable names, and operator definitions.
pub(super) struct ModuleState {
    /// Root module name (for TLC-style location rendering fallbacks).
    pub(super) root_name: String,
    /// Mapping from FileId to module name for TLC-style location rendering.
    pub(super) file_id_to_name: FxHashMap<tla_core::FileId, String>,
    /// Mapping from FileId to source path for TLC-style line/col location rendering.
    ///
    /// When absent for a given FileId (or unreadable), error locations fall back to byte offsets.
    pub(super) file_id_to_path: FxHashMap<tla_core::FileId, std::path::PathBuf>,
    /// Setup/configuration error detected during construction.
    ///
    /// Used for config validation that requires access to the loaded module set,
    /// such as TLC-style module-scoped overrides.
    pub(super) setup_error: Option<CheckError>,
    /// ASSUME statements collected from all modules (main + extended)
    /// Each entry is (module_name, assume_expr) for error reporting
    pub(super) assumes: Vec<(String, Spanned<Expr>)>,
    /// Variable names
    pub(super) vars: Vec<Arc<str>>,
    /// Cached operator definitions
    pub(super) op_defs: FxHashMap<String, OperatorDef>,
}

/// Partial Order Reduction (POR) prototype state.
pub(super) struct PorState {
    /// Pre-computed independence matrix for POR analysis.
    pub(super) independence: Option<crate::por::IndependenceMatrix>,
    /// Visibility set extracted from invariant expressions.
    pub(super) visibility: crate::por::VisibilitySet,
    /// POR prototype statistics.
    pub(super) stats: crate::por::PorStats,
}

/// Symmetry reduction state.
pub(super) struct SymmetryState {
    /// Symmetry permutations for state reduction (empty if no SYMMETRY in config)
    pub(super) perms: Vec<crate::value::FuncValue>,
    /// Fast symmetry permutations using MVPerm for O(1) model value lookup (Part of #358)
    pub(super) mvperms: Vec<crate::value::MVPerm>,
    /// Cache: original fingerprint -> canonical fingerprint (for symmetry reduction)
    /// Avoids recomputing canonical fingerprint for the same state
    pub(super) fp_cache: FxHashMap<Fingerprint, Fingerprint>,
    /// Number of fp_cache hits (state fingerprint already known canonical).
    pub(super) fp_cache_hits: u64,
    /// Number of fp_cache misses (required full canonical computation).
    pub(super) fp_cache_misses: u64,
    /// Number of states folded into existing canonical representatives.
    /// Incremented when a new state's canonical fingerprint matches an already-seen state.
    pub(super) states_folded: u64,
    /// Names of model value set constants that contribute to symmetry groups.
    pub(super) group_names: Vec<String>,
    /// Whether symmetry was auto-detected from config model value sets.
    pub(super) auto_detected: bool,
}

/// Part of #2752: Shared periodic liveness state — re-export from crate root
/// so sequential and parallel paths use identical gating logic.
pub(super) use crate::periodic_liveness::PeriodicLivenessState;

/// Debug instrumentation state (only active in debug builds).
pub(super) struct DebugDiagnostics {
    /// Map TLC FP -> internal FP to detect dedup mismatches.
    pub(super) seen_tlc_fp_dedup: Option<FxHashMap<u64, Fingerprint>>,
    /// Number of times a TLC fingerprint was seen with a different internal FP.
    pub(super) seen_tlc_fp_dedup_collisions: u64,
    /// Maximum collisions to print.
    pub(super) seen_tlc_fp_dedup_collision_limit: usize,
    /// Number of seen states containing lazy values.
    #[cfg(debug_assertions)]
    pub(super) lazy_values_in_state_states: u64,
    /// Number of lazy values observed across all recorded states.
    #[cfg(debug_assertions)]
    pub(super) lazy_values_in_state_values: u64,
    /// Maximum lazy-value state lines to print.
    #[cfg(debug_assertions)]
    pub(super) lazy_values_in_state_log_limit: usize,
    /// Map internal FP -> first TLC FP to detect internal FP collisions.
    pub(super) internal_fp_collision: Option<FxHashMap<Fingerprint, u64>>,
    /// Number of internal FP collisions detected.
    pub(super) internal_fp_collisions: u64,
    /// Maximum internal FP collisions to print.
    pub(super) internal_fp_collision_limit: usize,
}

/// Runtime hooks and progress reporting state.
pub(super) struct RuntimeHooksState {
    pub(super) init_progress_callback: Option<InitProgressCallback>,
    pub(super) progress_callback: Option<ProgressCallback>,
    pub(super) progress_interval: usize,
    pub(super) last_capacity_status: CapacityStatus,
}

/// Coverage collection state.
pub(super) struct CoverageState {
    /// Whether to collect per-action coverage statistics
    pub(super) collect: bool,
    /// Cached detected actions (including expressions) for coverage collection
    pub(super) actions: Vec<DetectedAction>,
    /// Whether to use coverage-guided exploration (priority frontier).
    pub(super) coverage_guided: bool,
    /// Coverage tracker for guided exploration (populated when coverage_guided=true).
    pub(super) tracker: Option<crate::coverage::guided::CoverageTracker>,
    /// Mix ratio for coverage-guided frontier (every N pops, one is priority-guided).
    pub(super) mix_ratio: usize,
}

/// Liveness checking cache state.
pub(super) struct LivenessCacheState {
    /// Cached successors from BFS (fingerprint -> list of successor fingerprints).
    /// Used for liveness checking to avoid regenerating transitions.
    /// Part of #3176: now uses `SuccessorGraph` dispatch enum supporting
    /// both in-memory HashMap and disk-backed storage.
    pub(super) successors: SuccessorGraph,
    /// Concrete successor witnesses keyed by canonical source fingerprint.
    ///
    /// Under SYMMETRY, liveness action checks must evaluate against the concrete
    /// successor states generated during BFS, not against the reduced
    /// representative state recovered later from `seen`.
    pub(super) successor_witnesses: SuccessorWitnessCache,
    /// Fairness constraints extracted from SPEC formula
    pub(super) fairness: Vec<FairnessConstraint>,
    /// Deduplicated fairness-derived state leaves keyed by stable fairness tags.
    ///
    /// Part of #3065: these are evaluated during BFS and copied into the
    /// existing cross-property cache before post-BFS liveness checking.
    pub(super) fairness_state_checks: Vec<LiveExpr>,
    /// Deduplicated fairness-derived action leaves keyed by stable fairness tags.
    pub(super) fairness_action_checks: Vec<LiveExpr>,
    /// Maximum fairness tag produced by fairness-first LiveExpr conversion.
    pub(super) fairness_max_tag: u32,
    /// Part of #3100: Reverse-indexed action provenance: split_action index → [tags].
    ///
    /// `action_provenance_tags[action_idx]` lists every fairness `ActionPred` tag
    /// proven true whenever split action `action_idx` fires. Built during liveness
    /// preparation by matching ActionPred hints against all split_action_meta entries
    /// (not just the first match). Keyed by action_idx for O(1) lookup in the BFS
    /// successor loop — avoids scanning all fairness leaves per successor.
    pub(super) action_provenance_tags: Vec<Vec<u32>>,
    /// Split-action provenance tags that are safe for runtime prepopulation.
    ///
    /// INSTANCE-qualified ModuleRef hints are still tracked in
    /// `action_provenance_tags` for diagnostics/tests, but they are excluded here
    /// until split-action matching can prove TLC-equivalent semantics (#3161).
    pub(super) action_fast_path_provenance_tags: Vec<Vec<u32>>,
    /// Part of #3100: ENABLED-based action skip groups (TLC's WF disjunction short-circuit).
    ///
    /// When `ENABLED(<<A>>_vars)` is false for state s, the conjunction
    /// `<<A>>_vars = ActionPred ∧ StateChanged` is false for ALL transitions from s.
    /// Each group maps an ENABLED state-leaf tag to the action-leaf tags (ActionPred +
    /// StateChanged) from the same WF/SF fairness constraint. Pre-populating these as
    /// false when ENABLED is false avoids expensive AST/compiled action evaluation.
    ///
    /// TLC equivalent: `LNAction.eval()` short-circuits on subscript check; combined
    /// with WF disjunction ordering, TLC skips action body evaluation when the action
    /// is not enabled.
    pub(super) enabled_action_groups: Vec<EnabledActionGroup>,
    /// Part of #3100: Subscript-action pairs for TLC's LNAction short-circuit.
    /// Maps `StateChanged(v)` tags to paired `ActionPred(A)` tags from `<<A>>_v`.
    pub(super) subscript_action_pairs: Vec<SubscriptActionPair>,
    /// Part of #3100: ENABLED provenance bypass — ENABLED tag → split_action
    /// indices. If any successor's action_tag matches, ENABLED is true.
    pub(super) enabled_provenance: Vec<EnabledProvenanceEntry>,
    /// Bitmask-only inline state results recorded during BFS.
    /// Bit `tag` set when `(fp, tag) → true`. Fingerprint presence means
    /// all fairness state tags have been evaluated for that state.
    /// Part of #3177: backed by `StateBitmaskMap` (in-memory or disk).
    pub(super) inline_state_bitmasks: StateBitmaskMap,
    /// Bitmask-only inline action results recorded during BFS.
    /// Bit `tag` set when `(from_fp, to_fp, tag) → true`. Key presence means
    /// all fairness action tags have been evaluated for that transition.
    /// Part of #3177: backed by `ActionBitmaskMap` (in-memory or disk).
    pub(super) inline_action_bitmasks: ActionBitmaskMap,
    /// Property-scoped inline liveness plans and recorded leaf results.
    pub(super) inline_property_plans: Vec<InlineLivenessPropertyPlan>,
    /// Part of #3992: Compiled liveness predicate batch for JIT-accelerated fairness.
    /// When available, state and action predicate evaluation uses compiled native code
    /// instead of the tree-walking interpreter.
    #[cfg(feature = "jit")]
    pub(super) compiled_liveness_batch: Option<tla_jit::CompiledLivenessBatch>,
    /// Cache successors for liveness (active when properties exist and liveness not skipped).
    /// Part of #3175: no longer requires store_full_states.
    pub(super) cache_for_liveness: bool,
    /// Initial states cached during BFS for post-BFS liveness checking.
    /// Part of #3175: populated regardless of store_full_states mode.
    /// Small: typically 1-10 states.
    pub(super) init_states: Vec<(Fingerprint, ArrayState)>,
    /// Part of #3210: Cached fp-only state replay result. Populated on first
    /// call to `build_fp_only_liveness_state_cache` and reused across properties
    /// to avoid O(S×D) per-state trace reconstruction per property.
    #[allow(clippy::type_complexity)]
    pub(super) fp_only_replay_cache: Option<(
        Arc<FxHashMap<Fingerprint, State>>,
        Arc<FxHashMap<Fingerprint, Fingerprint>>,
    )>,
}

/// State storage: seen states and fingerprints for deduplication and trace reconstruction.
pub(super) struct StateStorage {
    /// Seen states (fingerprint -> array state for trace reconstruction)
    /// Only populated when `store_full_states` is true
    /// Part of #4128: Identity hash — fingerprints are pre-hashed.
    pub(super) seen: FpHashMap<ArrayState>,
    /// Seen fingerprints (for memory-efficient mode when `store_full_states` is false)
    /// Uses FingerprintSet trait which supports both in-memory HashSet and memory-mapped storage.
    pub(super) seen_fps: Arc<dyn FingerprintSet>,
    /// Whether to store full states for trace reconstruction
    /// When false, only fingerprints are stored (saves memory but no trace available)
    pub(super) store_full_states: bool,
}

/// Trace reconstruction state: depths and disk-based trace storage.
///
/// Part of #3178: the `parents` FxHashMap has been removed. Parent
/// relationships are now stored in the trace file for both full-state
/// and fp-only modes, saving ~16 bytes per state on the BFS hot path.
pub(super) struct TraceState {
    /// Depth tracking for each state (fingerprint -> depth)
    /// Part of #4128: Identity hash — fingerprints are pre-hashed.
    pub(super) depths: FpHashMap<usize>,
    /// Whether to auto-create a temp trace file (both full-state and fp-only modes)
    /// Default: true. Set to false for --no-trace mode (no trace reconstruction at all)
    pub(super) auto_create_trace_file: bool,
    /// Disk-based trace file for large state space exploration
    /// When enabled, stores (predecessor_loc, fingerprint) pairs on disk for trace reconstruction
    pub(super) trace_file: Option<TraceFile>,
    /// Mapping from fingerprint to trace file location
    /// Uses TraceLocationsStorage for scalable (mmap) or in-memory storage
    pub(super) trace_locs: TraceLocationsStorage,
    /// Whether trace I/O errors have occurred, meaning counterexample traces may be incomplete
    pub(super) trace_degraded: bool,
    /// Trace file location of the current parent state, set during BFS dequeue.
    ///
    /// Part of #2881 Step 3: eliminates per-successor `trace_locs` HashMap reads
    /// by carrying the parent's trace_loc from the queue entry. Set once per
    /// dequeued parent state, read by all successor admissions in that iteration.
    pub(super) current_parent_trace_loc: Option<u64>,
    /// Trace file location of the last successfully inserted state.
    ///
    /// Part of #2881 Step 3: used by `admit_successor` to include the trace_loc
    /// on queue entries without changing return types. Set by
    /// `mark_state_seen_checked` / `mark_state_seen_fp_only_checked` after a
    /// successful trace file write.
    pub(super) last_inserted_trace_loc: u64,
    /// When true, skip `trace_locs.insert` during BFS state admission.
    ///
    /// Part of #2881 Step 3: eliminates the last per-state HashMap write on
    /// the BFS hot path. The trace index is built lazily from the trace file
    /// via `ensure_trace_index_built()` when reconstruction is needed (cold
    /// path only). Default: false (eager inserts for backward compatibility
    /// with tests and callers that don't use queue entry threading).
    pub(super) lazy_trace_index: bool,
    /// Cached Init operator name (for trace reconstruction from fingerprints)
    pub(super) cached_init_name: Option<String>,
    /// Cached Next operator name (for trace reconstruction from fingerprints)
    pub(super) cached_next_name: Option<String>,
    /// Cached resolved Next operator name (avoids per-state resolve_op_name + String alloc)
    pub(super) cached_resolved_next_name: Option<String>,
}

impl TraceState {
    /// Build the trace location index from the trace file.
    ///
    /// Part of #2881 Step 3: when `lazy_trace_index` is true, the BFS hot
    /// path skips `trace_locs.insert` to avoid per-state HashMap writes.
    /// This method builds the index on demand by scanning the trace file.
    /// Called before any operation that needs fingerprint-to-offset lookups
    /// (error trace reconstruction, resume queue building).
    ///
    /// No-op when the index is already populated or no trace file exists.
    pub(super) fn ensure_trace_index_built(&mut self) {
        if !self.lazy_trace_index {
            return; // Eager mode — index already populated during BFS
        }

        // Check if the index already covers all trace file records.
        // Initial states may have been inserted eagerly before lazy mode was
        // enabled, so trace_locs.len() > 0 does not mean the index is complete.
        let file_records = match self.trace_file {
            Some(ref f) => f.record_count() as usize,
            None => return, // No trace file, nothing to build
        };

        if self.trace_locs.len() >= file_records {
            return; // Index already complete
        }

        if let Some(ref mut trace_file) = self.trace_file {
            match trace_file.read_all_records() {
                Ok(records) => {
                    for (fp, offset) in records {
                        self.trace_locs.insert(fp, offset);
                    }
                }
                Err(_) => {
                    // Trace file I/O failure; the caller (reconstruct_trace_from_file)
                    // will report a warning when the fingerprint lookup fails.
                    self.trace_degraded = true;
                }
            }
        }
    }
}

/// Part of #3100: Metadata from `ActionInstance` stored for action provenance matching.
///
/// Captures the action name and binding values from each split action instance,
/// enabling the liveness evaluator to match `ActionPred` expressions against BFS
/// actions by comparing operator names and binding values.
#[derive(Debug, Clone)]
pub(super) struct ActionInstanceMeta {
    /// Operator name of the action (e.g., "RcvMsg" for `RcvMsg(p)`).
    pub(super) name: Option<String>,
    /// Bound variable values from EXISTS expansion (e.g., `[(p, P1)]` for `RcvMsg(p)` with p=P1).
    pub(super) bindings: Vec<(Arc<str>, crate::Value)>,
    /// The expression body for this split action disjunct.
    ///
    /// Stored so that `try_jit_monolithic_successors` can fall back to per-action
    /// interpreter evaluation for actions that are not JIT-compiled, enabling
    /// hybrid JIT/interpreter dispatch instead of all-or-nothing.
    ///
    /// Part of #3968: per-action hybrid JIT dispatch.
    #[allow(dead_code)]
    pub(super) expr: Option<tla_core::Spanned<tla_core::ast::Expr>>,
}

/// Pre-compiled spec artifacts: invariants, Next action, VIEW, and TLCExt!Trace detection.
pub(super) struct CompiledSpec {
    /// Part of #3100: Action instance metadata from split-action discovery.
    ///
    /// Each entry corresponds to the same index in the discovered split-action
    /// list. Stores the bindings from the original `ActionInstance`, used to
    /// build the `action_provenance_tags` during liveness preparation.
    pub(super) split_action_meta: Option<Vec<ActionInstanceMeta>>,
    /// Cached VIEW operator name (for state abstraction in fingerprinting)
    /// When set, fingerprinting uses this operator's value instead of full state
    pub(super) cached_view_name: Option<String>,
    /// Whether the spec references TLCExt!Trace (conservative detection).
    /// When true, trace reconstruction is performed before invariant checks.
    pub(super) uses_trace: bool,
    /// Properties of the form `[]P` where P is a state-level predicate that were
    /// promoted to invariant checking during BFS (#2332). These are skipped in
    /// post-BFS liveness checking since they're already checked during exploration.
    pub(super) promoted_property_invariants: Vec<String>,
    /// Property names whose state-level terms are checked during BFS.
    ///
    /// This includes mixed properties with a remaining temporal tail and is
    /// used only for reporting `PropertyViolation` instead of
    /// `InvariantViolation` when the state-level part fails.
    pub(super) state_property_violation_names: Vec<String>,
    /// Eval-based implied actions for ModuleRef/INSTANCE properties (#2983).
    /// These use the general evaluator BFS-inline instead of compiled guards,
    /// because priming through INSTANCE WITH substitutions is buggy in the
    /// compiled guard path. Checked for ALL transitions during BFS.
    pub(super) eval_implied_actions: Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>,
    /// Names of properties that had action-level always-terms extracted for
    /// BFS-phase implied action checking (#2670). These are skipped in
    /// post-BFS liveness checking since they're already checked during BFS.
    pub(super) promoted_implied_action_properties: Vec<String>,
    /// Eval-based state invariants for ENABLED-containing state-level terms (#3113).
    /// Checked for unseen states only via eval_entry() during BFS.
    pub(super) eval_state_invariants: Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>,
    /// Pre-computed variable dependency analysis for ACTION_CONSTRAINTs.
    /// Used to skip constraint evaluation when referenced variables are unchanged.
    pub(super) action_constraint_analysis: Option<crate::checker_ops::ActionConstraintAnalysis>,
    /// Init predicates from PROPERTY entries: non-Always state/constant-level
    /// terms checked against initial states only. Part of #2834.
    pub(super) property_init_predicates: Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>,
    /// PlusCal `pc`-dispatch table for skipping irrelevant actions.
    ///
    /// When the spec follows the PlusCal pattern where all disjuncts of Next
    /// are guarded by `pc = "label"`, this table maps pc values to action
    /// indices, allowing the BFS loop to skip actions whose pc guard cannot
    /// match the current state.
    pub(super) pc_dispatch: Option<crate::checker_ops::pc_dispatch::PcDispatchTable>,
    /// Variable index of `pc` for guard hoisting, independent of the dispatch table.
    ///
    /// For single-process PlusCal specs, this is set from `pc_dispatch.pc_var_idx`.
    /// For multi-process PlusCal specs (where the full dispatch table can't be built
    /// because `pc` is a function), this is set directly by detecting that the spec
    /// uses `pc[self] = "label"` guard patterns. This allows the unified enumerator
    /// to skip Or branches with non-matching pc guards even for multi-process specs.
    ///
    /// Part of #3805: multi-process PlusCal guard hoisting.
    pub(super) pc_var_idx: Option<tla_core::VarIndex>,
    /// Whether the spec's AST contains expressions that can produce lazy values
    /// at runtime (`FuncDef`, `SetFilter`, `Lambda`). When `false`, the
    /// per-successor `has_lazy_state_value` scan in `materialize_array_state`
    /// and `materialize_diff_changes` is skipped entirely.
    ///
    /// Part of #4053: Skip `has_lazy_state_value` for non-lazy specs.
    pub(super) spec_may_produce_lazy: bool,
}

/// Exploration control: limits, deadlock checking, and error continuation.
pub(super) struct ExplorationControl {
    /// Whether to check for deadlocks
    pub(super) check_deadlock: bool,
    /// Whether stuttering transitions are allowed (`[A]_v` = true, `<<A>>_v` = false).
    ///
    /// When true (the common `[A]_v` case), the liveness checker adds self-loop edges
    /// so that stuttering behaviors are visible to SCC analysis. Without these edges,
    /// liveness properties like `[]<>(x=3)` that are violated by infinite stuttering
    /// would be falsely reported as satisfied.
    ///
    /// Defaults to `true` (stuttering allowed), matching the most common TLA+ pattern.
    pub(super) stuttering_allowed: bool,
    /// Continue exploring after invariant/property violations (like TLC's -continue flag)
    pub(super) continue_on_error: bool,
    /// First invariant violation found (used in continue_on_error mode).
    /// Stores (invariant_name, violating_state_fingerprint).
    /// When continue_on_error is true, we record the first violation here and continue
    /// exploring until the full state space is exhausted, then report this violation.
    pub(super) first_violation: Option<(String, Fingerprint)>,
    /// First action-level PROPERTY violation found (used in continue_on_error mode).
    pub(super) first_action_property_violation: Option<(String, Fingerprint)>,
    /// Maximum states to explore (None = unlimited)
    pub(super) max_states: Option<usize>,
    /// Maximum BFS depth (None = unlimited)
    pub(super) max_depth: Option<usize>,
    /// Part of #2751: Optional memory limit for threshold-triggered stop.
    pub(super) memory_policy: Option<crate::memory::MemoryPolicy>,
    /// Part of #3282: Optional disk usage limit in bytes for disk-backed storage.
    pub(super) disk_limit_bytes: Option<usize>,
}

/// The model checker
pub struct ModelChecker<'a> {
    /// Configuration
    pub(super) config: &'a Config,
    /// Module metadata (names, paths, setup errors, assumes)
    pub(super) module: ModuleState,
    /// Evaluation context
    pub(super) ctx: EvalCtx,
    /// State storage (seen states, fingerprints, storage mode)
    pub(super) state_storage: StateStorage,
    /// Trace reconstruction (parents, depths, trace file, cached names)
    pub(super) trace: TraceState,
    /// Pre-compiled spec artifacts (invariants, Next action, VIEW, Trace detection)
    pub(super) compiled: CompiledSpec,
    /// Exploration limits and error handling
    pub(super) exploration: ExplorationControl,
    /// Statistics
    pub(super) stats: CheckStats,
    /// Runtime hooks and progress reporting
    pub(super) hooks: RuntimeHooksState,
    /// Liveness checking cache
    pub(super) liveness_cache: LivenessCacheState,
    /// Part of #3225: computed once from storage/symmetry/VIEW instead of
    /// re-deriving the liveness mode matrix at every callsite.
    pub(super) liveness_mode: LivenessMode,
    /// Coverage collection
    pub(super) coverage: CoverageState,
    /// Symmetry reduction state (permutations, fast MVPerms, fingerprint cache)
    pub(super) symmetry: SymmetryState,
    /// Env-gated AST/TIR parity replay for selected named operators.
    pub(super) tir_parity: Option<super::tir_parity::TirParityState>,
    /// Part of #3578: Compiled bytecode for invariant operators (bytecode VM fast path).
    pub(super) bytecode: Option<tla_eval::bytecode_vm::CompiledBytecode>,
    /// Part of #3910: Compiled bytecode for next-state action operators (JIT next-state fast path).
    /// Separate from invariant bytecode because actions use StoreVar opcodes for primed variables.
    #[cfg(feature = "jit")]
    pub(super) action_bytecode: Option<tla_eval::bytecode_vm::CompiledBytecode>,
    /// Part of #3582: JIT-compiled invariant functions (Cranelift native code fast path).
    /// Populated at run_prepare time. JIT is opt-in; enable with `--jit` or `TLA2_JIT=1`.
    #[cfg(feature = "jit")]
    pub(super) jit_cache: Option<tla_jit::bytecode_lower::JitInvariantCache>,
    /// Part of #3700: Reusable scalar-state scratch for JIT invariant checks.
    #[cfg(feature = "jit")]
    pub(super) jit_state_scratch: Vec<i64>,
    /// True when every configured invariant has a JIT-compiled native function.
    /// Enables the zero-allocation `check_all_compiled` fast path that skips
    /// the unchecked buffer entirely.
    #[cfg(feature = "jit")]
    pub(super) jit_all_compiled: bool,
    /// Pre-resolved JIT function pointers in invariant order. Eliminates
    /// per-invariant HashMap lookups in the hot path.
    #[cfg(feature = "jit")]
    pub(super) jit_resolved_fns: Option<Vec<tla_jit::JitInvariantFn>>,
    /// Part of #3700: Sequential JIT profile hits (fully handled by JIT).
    #[cfg(feature = "jit")]
    pub(super) jit_hits: usize,
    /// Part of #3700: Sequential JIT profile misses (fell back after JIT attempt).
    #[cfg(feature = "jit")]
    pub(super) jit_misses: usize,
    /// Part of #3935: Per-invariant JIT dispatch hits.
    #[cfg(feature = "jit")]
    pub(super) jit_hit: usize,
    /// Part of #3935: Per-invariant JIT dispatch fallbacks.
    #[cfg(feature = "jit")]
    pub(super) jit_fallback: usize,
    /// Part of #3935: Per-invariant JIT dispatch misses (no native invariant compiled).
    #[cfg(feature = "jit")]
    pub(super) jit_not_compiled: usize,
    /// Part of #3935: Total per-invariant JIT dispatch attempts.
    #[cfg(feature = "jit")]
    pub(super) total_invariant_evals: usize,
    /// Number of fully JIT-covered invariant evaluations cross-checked via the interpreter.
    pub(super) jit_verify_checked: usize,
    /// Number of JIT/interpreter invariant mismatches observed during cross-checking.
    pub(super) jit_verify_mismatches: usize,
    /// Tiered JIT compilation manager for HotSpot-style action promotion.
    ///
    /// Tracks per-action compilation tiers (Interpreter → Tier1 → Tier2) and
    /// makes promotion decisions based on evaluation frequency. Initialized
    /// in `prepare_bfs_common` after action splitting discovers action count.
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    #[cfg(feature = "jit")]
    pub(super) tier_manager: Option<tla_jit::TierManager>,
    /// Per-action evaluation counts for tiered JIT promotion decisions.
    ///
    /// Lightweight Vec<u64> indexed by action_id. Updated during successor
    /// generation for both monolithic and split-action paths. Does not
    /// depend on cooperative/z4 mode -- works for all BFS modes.
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    #[cfg(feature = "jit")]
    pub(super) action_eval_counts: Vec<u64>,
    /// Per-action successor totals for branching factor computation.
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    #[cfg(feature = "jit")]
    pub(super) action_succ_totals: Vec<u64>,
    /// Accumulated tier promotion events for `--show-tiers` report.
    ///
    /// Appended by `check_tier_promotions()` at progress intervals.
    /// Read during `run_finalize` to produce the per-action tier report.
    ///
    /// Part of #3910: Wire TierManager into BFS loop.
    #[cfg(feature = "jit")]
    pub(super) tier_promotion_history: Vec<tla_jit::TierPromotion>,
    /// Reusable scratch buffer for type profiling during BFS.
    ///
    /// Sized to state variable count. Populated with `classify_value` results
    /// for each explored state and passed to `TierManager::observe_state_types`.
    /// Avoids per-state allocation.
    ///
    /// Part of #3989: speculative type specialization.
    #[cfg(feature = "jit")]
    pub(super) type_profile_scratch: Vec<tla_jit::SpecType>,
    /// JIT-compiled next-state action cache for sequential BFS.
    ///
    /// Built lazily on first Tier 1 promotion (not at startup) to avoid
    /// compilation overhead for small specs that never cross the threshold.
    /// Once populated, the diff/full-state successor paths check this cache
    /// before falling back to the interpreter.
    ///
    /// Part of #3910: Wire TierManager into BFS loop.
    #[cfg(feature = "jit")]
    pub(super) jit_next_state_cache: Option<tla_jit::JitNextStateCache>,
    /// Next-state JIT dispatch counters for `--show-tiers` report.
    ///
    /// Part of #3910.
    #[cfg(feature = "jit")]
    pub(super) next_state_dispatch: tla_jit::NextStateDispatchCounters,
    /// Compilation statistics from the last `JitNextStateCache::build_with_stats`
    /// call. Populated on first Tier 1 promotion. Included in the
    /// `--show-tiers` end-of-run report.
    ///
    /// Part of #3910: JIT compilation latency instrumentation.
    #[cfg(feature = "jit")]
    pub(super) jit_cache_build_stats: Option<tla_jit::CacheBuildStats>,
    /// Pending async JIT compilation result.
    ///
    /// When a Tier 1 promotion fires, compilation is spawned on a background
    /// thread via `std::thread::spawn`. The sender half of a oneshot channel
    /// is moved into the thread; the receiver stays here. The BFS loop
    /// continues with the interpreter while Cranelift compiles. On each
    /// state, `poll_pending_jit_compilation` does a non-blocking `try_recv`.
    /// Once ready, the cache is moved to `jit_next_state_cache` and
    /// subsequent states use native code.
    ///
    /// Part of #3910: Async JIT compilation with interpreter warmup.
    #[cfg(feature = "jit")]
    pub(super) pending_jit_compilation: Option<
        std::sync::mpsc::Receiver<(tla_jit::JitNextStateCache, tla_jit::CacheBuildStats)>,
    >,
    /// Tier 2 recompilation controller for speculative type specialization.
    ///
    /// Manages the lifecycle of Tier 2 recompilation triggered by type profiling.
    /// When a Tier 2 promotion fires with a `SpecializationPlan`, this controller
    /// spawns a background thread to rebuild the JIT cache and polls for completion.
    ///
    /// Part of #3989: speculative type specialization.
    #[cfg(feature = "jit")]
    pub(super) recompilation_controller: tla_jit::RecompilationController,
    /// Compound state layout inferred from the initial state.
    ///
    /// Populated by `upgrade_jit_cache_with_layout` after init state solving.
    /// Used by the async JIT compilation thread to enable native compound
    /// access (FuncApply, RecordGet, TupleGet) in next-state dispatch.
    ///
    /// Part of #3958: Enable native compound access in JIT next-state dispatch.
    #[cfg(feature = "jit")]
    pub(super) jit_state_layout: Option<tla_jit::StateLayout>,
    /// Set to true when JIT successor generation must be permanently disabled.
    /// Causes include: (1) JIT runtime error (compiled function crashes),
    /// (2) validation mismatch — JIT successor count differs from monolithic
    /// enumerator (#4011). Skips the entire JIT path for remaining states.
    ///
    /// Part of #3968: per-action hybrid JIT dispatch.
    /// Part of #4011: also set on validation failure.
    #[cfg(feature = "jit")]
    pub(super) jit_monolithic_disabled: bool,
    /// Cached flag: true when ALL split actions (including EXISTS-bound
    /// specializations) have JIT cache entries. Computed once when the
    /// JIT next-state cache is installed via `poll_pending_jit_compilation`.
    ///
    /// When false, `try_jit_monolithic_successors` bails out immediately
    /// instead of iterating through actions only to discover a cache miss
    /// partway through and abandoning the work.
    ///
    /// Part of EXISTS binding JIT dispatch: avoids per-state O(N) cache
    /// coverage re-checking.
    #[cfg(feature = "jit")]
    pub(super) jit_all_next_state_compiled: bool,
    /// Cached flag: true when at least one action is at Tier1+ compilation.
    /// Updated once when the JIT cache is installed and coverage is checked.
    /// Avoids per-state iteration over all actions in `jit_monolithic_ready()`.
    ///
    /// Part of #4030: Eliminate per-state O(N) action scan in JIT readiness check.
    #[cfg(feature = "jit")]
    pub(super) jit_has_any_promoted: bool,
    /// Cached flag: true when the current state's flat representation has
    /// no compound (non-int, non-bool) variables. When true, the JIT fused
    /// path can skip `clear_compound_scratch()` calls, saving a TLS access
    /// per action evaluation.
    ///
    /// Part of #4030: Skip compound scratch for all-scalar states.
    #[cfg(feature = "jit")]
    pub(super) jit_state_all_scalar: bool,
    /// Remaining JIT validation cross-checks against the monolithic enumerator.
    ///
    /// When JIT produces successors for a state (all actions compiled), the
    /// result is cross-checked against the monolithic enumerator for the first
    /// N states. If successor counts differ, JIT is permanently disabled and
    /// a P0 warning is logged. After N successful validations, the
    /// double-computation is skipped.
    ///
    /// Part of #4011: JIT validation mode for fully-JIT states.
    #[cfg(feature = "jit")]
    pub(super) jit_validation_remaining: u32,
    /// Pre-computed JIT cache lookup keys for each split action.
    ///
    /// Computed once when the JIT cache is installed (in `poll_pending_jit_compilation`),
    /// avoiding per-state String allocation and clone overhead in the hot path.
    /// Each entry is the cache key for the corresponding action in split_action_meta:
    /// - Binding-free actions: the action name directly
    /// - EXISTS-bound actions: specialized_key(name, binding_values)
    ///
    /// Part of #4030: Eliminate per-state allocation in JIT hybrid dispatch.
    #[cfg(feature = "jit")]
    pub(super) jit_action_lookup_keys: Vec<String>,
    /// Reusable scratch buffer for JIT action output (successor state as i64[]).
    ///
    /// Avoids allocating a fresh Vec<i64> per action evaluation. Sized to
    /// state_var_count when the JIT cache is installed.
    ///
    /// Part of #4030: Eliminate per-action allocation in JIT dispatch.
    #[cfg(feature = "jit")]
    pub(super) jit_action_out_scratch: Vec<i64>,
    /// Adaptive performance monitoring for JIT dispatch.
    ///
    /// Tracks cumulative time spent in JIT vs interpreter paths for the first
    /// N states after JIT activation. If JIT is consistently slower, it is
    /// automatically disabled. Format: (jit_ns, interp_ns, states_sampled).
    ///
    /// Part of #4030: Adaptive JIT performance switch.
    #[cfg(feature = "jit")]
    pub(super) jit_perf_monitor: (u64, u64, u32),
    /// Cached TLA2_JIT_DIAG env var check. Set once when JIT cache is installed
    /// to avoid a per-state syscall in the hot path.
    ///
    /// Part of #4030: Eliminate per-state env var overhead.
    #[cfg(feature = "jit")]
    pub(super) jit_diag_enabled: bool,
    /// Compiled BFS step function for fully-JIT specs.
    ///
    /// When all actions AND all invariants are JIT-compiled, and the spec
    /// uses a fully-flat state representation (all variables are fixed-size
    /// i64 representable), this holds a `CompiledBfsStep` that performs
    /// the entire BFS inner loop (action dispatch, fingerprinting, dedup,
    /// invariant checking) in native Cranelift-compiled code.
    ///
    /// Built lazily after `poll_pending_jit_compilation` installs the
    /// `jit_next_state_cache` and coverage checks pass.
    ///
    /// Part of #4034: Wire CompiledBfsStep into model checker BFS loop.
    #[cfg(feature = "jit")]
    pub(super) compiled_bfs_step: Option<tla_jit::CompiledBfsStep>,
    /// Fused compiled BFS level function that processes entire frontiers in
    /// a single native call. Built lazily after `CompiledBfsStep` is
    /// available and the fused level function compiles successfully.
    ///
    /// When present, `run_compiled_bfs_loop()` uses this instead of the
    /// per-parent `CompiledBfsStep` path, eliminating Rust-to-JIT boundary
    /// crossings per parent.
    ///
    /// Part of #4171: End-to-end compiled BFS wiring.
    #[cfg(feature = "jit")]
    pub(super) compiled_bfs_level: Option<tla_jit::CompiledBfsLevel>,

    // ==================== Composed sub-structs (Part of #1268) ====================
    /// Checkpoint state for periodic saves during model checking
    pub(super) checkpoint: CheckpointState,
    /// Partial Order Reduction state
    pub(super) por: PorState,
    /// Periodic liveness checking state (TLC doPeriodicWork pattern, Part of #2752)
    pub(super) periodic_liveness: PeriodicLivenessState,
    /// Debug instrumentation (only active in debug builds)
    pub(super) debug: DebugDiagnostics,
    /// Portfolio racing verdict for early exit when another lane resolves.
    /// Part of #3717: when `Some`, the BFS worker loop checks periodically
    /// and publishes its verdict upon completion.
    pub(crate) portfolio_verdict: Option<Arc<crate::shared_verdict::SharedVerdict>>,
    /// Cooperative state for fused BFS+symbolic mode (CDEMC).
    /// Part of #3767, Epic #3762.
    #[cfg(feature = "z4")]
    pub(crate) cooperative: Option<Arc<crate::cooperative_state::SharedCooperativeState>>,
    /// Collision detection for fingerprint-based state storage.
    pub(super) collision_detector: Option<crate::collision_detection::CollisionDetector>,

    /// Flat i64 state layout inferred from the first initial state.
    ///
    /// Populated by `infer_flat_state_layout()` after init state solving.
    /// Maps each state variable to a contiguous region of i64 slots in a
    /// flat buffer. Used by JIT-compiled transition functions and invariant
    /// checkers to operate on `FlatState` representations directly.
    ///
    /// `None` before init states are computed or when inference is skipped
    /// (e.g., no initial states generated).
    ///
    /// Part of #3986: Wire FlatState into BFS path.
    pub(super) flat_state_layout: Option<Arc<crate::state::StateLayout>>,

    /// Bridge for converting between `ArrayState` and `FlatState` at the
    /// BFS engine boundary.
    ///
    /// Created after `infer_flat_state_layout()` completes. Provides cheap
    /// `ArrayState <-> FlatState` conversions and fingerprint bridging.
    ///
    /// Part of #3986: Wire FlatState into BFS engine.
    pub(super) flat_bfs_bridge: Option<crate::state::FlatBfsBridge>,

    /// BFS-specific adapter wrapping the `FlatBfsBridge` with convenience
    /// methods for the interpreter sandwich: FlatState -> ArrayState -> eval ->
    /// ArrayState -> FlatState.
    ///
    /// Created alongside `flat_bfs_bridge` during layout inference. Tracks
    /// per-run conversion statistics. Auto-activated for fully-flat layouts
    /// (all scalar vars), or force-enabled via `TLA2_FLAT_BFS=1` env var.
    /// See `should_use_flat_bfs()` for the full decision hierarchy.
    ///
    /// Part of #4126: FlatState as native BFS representation (Phase E).
    pub(super) flat_bfs_adapter: Option<crate::state::FlatBfsAdapter>,
}

#[cfg(test)]
impl<'a> ModelChecker<'a> {
    pub(in crate::check) fn test_vars(&self) -> &[Arc<str>] {
        &self.module.vars
    }

    pub(in crate::check) fn test_fairness(&self) -> &[FairnessConstraint] {
        &self.liveness_cache.fairness
    }

    pub(in crate::check) fn test_seen_is_empty(&self) -> bool {
        self.state_storage.seen.is_empty()
    }

    pub(in crate::check) fn test_seen_fps_len(&self) -> usize {
        self.state_storage.seen_fps.len()
    }

    /// Test helper: inject fp into seen_fps to create trace.depths mismatch.
    pub(in crate::check) fn test_inject_spurious_fingerprint(&self, fp: Fingerprint) {
        self.state_storage.seen_fps.insert_checked(fp);
    }
}
