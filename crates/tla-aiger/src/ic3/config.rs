// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 configuration types, parameter structs, and constants.

use crate::sat_types::SolverBackend;

/// Validation strategy for IC3 invariant checking (#4121).
///
/// Controls how aggressively the engine validates the inductive invariant
/// after convergence. High constraint-to-latch ratio circuits can overwhelm
/// even Z4NoPreprocess during the Inv AND T => Inv' check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValidationStrategy {
    /// Full 3-tier validation. Default. Uses constraint/latch ratio for tier selection.
    Auto,
    /// Skip the expensive per-lemma Inv AND T => Inv' check entirely.
    /// Only performs Init => Inv and Inv => !Bad checks.
    SkipConsecution,
    /// Skip all validation. ONLY safe when another portfolio member validates.
    None,
}

impl Default for ValidationStrategy {
    fn default() -> Self {
        ValidationStrategy::Auto
    }
}

/// Default CTG parameters for MIC generalization.
/// CTG_MAX: max CTG attempts per literal drop in MIC.
/// CTG_LIMIT: max recursive trivial_block depth.
pub(super) const DEFAULT_CTG_MAX: usize = 3;
pub(super) const DEFAULT_CTG_LIMIT: usize = 1;

/// Default CTP parameters for propagation.
/// CTP_MAX: max CTP attempts per lemma push in propagate().
pub(super) const DEFAULT_CTP_MAX: usize = 3;

/// Base threshold for periodic solver rebuild. The actual threshold is
/// scaled by circuit size: `base * max(1, num_latches / 20)`. Small circuits
/// (< 20 latches) rebuild at the base rate; larger circuits get proportionally
/// more headroom before rebuilding, since each MIC iteration is more expensive
/// and rebuilding all solvers on a 200-latch circuit with 50+ frames is costly.
///
/// The old fixed 10K threshold was too aggressive for large circuits (causing
/// frequent expensive rebuilds) and too lenient for tiny circuits.
pub(super) const SOLVER_REBUILD_BASE: usize = 5_000;

/// Default sampling interval for independent consecution verification (#4092).
///
/// The actual interval is computed adaptively by `consecution_verify_interval()`
/// based on the circuit's clause-to-latch ratio. This constant is the default
/// for low-ratio circuits where z4-sat false UNSAT is rare.
///
/// See `consecution_verify_interval()` for the adaptive logic.
pub(super) const CONSECUTION_VERIFY_INTERVAL_DEFAULT: usize = 10;

/// Compute the adaptive consecution verification interval (#4121).
///
/// High constraint-to-latch ratio circuits cause z4-sat to produce false UNSAT
/// more frequently because the SAT solver spends disproportionate time on
/// constraint propagation and may terminate prematurely. Sampling-based
/// verification (checking only every Nth consecution) misses too many unsound
/// lemmas on these circuits.
///
/// Two metrics are considered:
/// 1. `trans_clauses / latches` — Tseitin encoding complexity. A circuit can have
///    0 explicit AIGER constraints but thousands of trans_clauses that stress z4-sat.
///    cal76 (36 consecution errors) has few constraint_lits but many trans_clauses.
/// 2. `constraint_lits / latches` — AIGER environment constraint density. Circuits
///    like microban (100-300+ constraint_lits on 20-60 latches) overwhelm the SAT
///    solver's constraint propagation path even when trans_clauses are moderate.
///    microban_148 (false UNSAT) and microban_1 (infinite rebuild) are in this class.
///
/// The effective ratio is the MAX of both metrics, since either high trans_clauses
/// OR high constraint_lits can trigger z4-sat false UNSAT.
///
/// Thresholds:
/// - ratio > 5.0: verify every consecution (interval=1). These circuits produce
///   false UNSAT frequently enough that sampling is dangerous.
/// - ratio > 2.0: verify every 3rd (interval=3). Moderate risk.
/// - ratio <= 2.0: verify every 10th (interval=10). Low risk, save overhead.
#[allow(dead_code)]
pub(super) fn consecution_verify_interval(
    num_trans_clauses: usize,
    num_latches: usize,
) -> usize {
    consecution_verify_interval_full(num_trans_clauses, 0, num_latches)
}

/// Compute the adaptive consecution verification interval considering both
/// trans_clauses and constraint_lits (#4121).
///
/// This is the full version that takes both metrics. The shorter
/// `consecution_verify_interval()` is kept for backward compatibility.
pub(super) fn consecution_verify_interval_full(
    num_trans_clauses: usize,
    num_constraints: usize,
    num_latches: usize,
) -> usize {
    if num_latches == 0 {
        return 1;
    }
    let trans_ratio = num_trans_clauses as f64 / num_latches as f64;
    let constraint_ratio = num_constraints as f64 / num_latches as f64;
    // Use the max of both metrics: either high trans_clauses OR high
    // constraint_lits can cause z4-sat false UNSAT.
    let ratio = trans_ratio.max(constraint_ratio);
    if ratio > 5.0 {
        1
    } else if ratio > 2.0 {
        3
    } else {
        CONSECUTION_VERIFY_INTERVAL_DEFAULT
    }
}

/// Determine if a circuit has a high constraint-to-latch ratio (#4121).
///
/// High-constraint circuits (microban class: 100-300+ constraints on 20-60
/// latches) cause systematic z4-sat false UNSAT and SimpleSolver false SAT
/// in cross-checks. For these circuits, the cross-check should be disabled
/// from the start rather than waiting for the failure budget to be exhausted,
/// because:
/// 1. SimpleSolver's basic DPLL produces false SAT on constraint-dense formulas
/// 2. z4-sat's incremental queries are unreliable on these formulas
/// 3. The only reliable soundness check is the post-convergence validation
///
/// Returns true if either:
/// - `constraint_lits / latches > 5` (AIGER constraint density)
/// - `trans_clauses / latches > 10` AND `constraint_lits > latches` (combined pressure)
pub(super) fn is_high_constraint_circuit(
    num_trans_clauses: usize,
    num_constraints: usize,
    num_latches: usize,
) -> bool {
    if num_latches == 0 {
        return false;
    }
    let constraint_ratio = num_constraints as f64 / num_latches as f64;
    let trans_ratio = num_trans_clauses as f64 / num_latches as f64;
    // Pure constraint density: microban class (124 constraints / 23 latches = 5.4x)
    constraint_ratio > 5.0
        // Combined pressure: high trans + non-trivial constraints
        || (trans_ratio > 10.0 && num_constraints > num_latches)
}

/// Number of consecutive SatResult::Unknown from non-poisoned solvers before
/// the engine falls back to Z4NoPreprocess (#4074). z4-sat can produce
/// FINALIZE_SAT_FAIL on certain clause structures (e.g., cal14), causing
/// the solver to return Unknown/InvalidSatModel indefinitely. After
/// this many consecutive Unknown results, we disable preprocessing entirely.
///
/// Note: `solve_incremental_ic3()` skips `preprocess()`, so BVE is not the
/// cause of these failures. The fallback is a general resilience mechanism.
pub(super) const UNKNOWN_FALLBACK_THRESHOLD: usize = 3;

/// Maximum proof obligation depth. If an obligation chain exceeds this,
/// we stop exploring that branch and return to the queue. This prevents
/// runaway depth explosion when the transition system has very long
/// reachability chains. The BMC engine is better suited for such cases.
///
/// Set high enough that it doesn't interfere with genuine counterexamples
/// on HWMCC benchmarks (deepest known CEX is ~200 steps).
pub(super) const MAX_OBLIGATION_DEPTH: usize = 500;

/// Maximum cross-check failures per frame before disabling the independent
/// consecution verification for that frame. When z4-sat consistently produces
/// false UNSAT for a particular frame's clause structure (SimpleSolver
/// disagrees), rebuilding the solver and retrying creates an infinite loop.
/// After this many failures at the same frame, we stop cross-checking and
/// instead skip the z4-sat UNSAT result entirely (treat as inconclusive).
///
/// This breaks the rebuild loop observed on microban_1 (UNSAT) and similar
/// benchmarks where z4-sat returns false UNSAT 30K+ times in 10 seconds.
pub(super) const MAX_CROSSCHECK_FAILURES: usize = 5;

/// Maximum TOTAL cross-check failures across all frames (#4121).
///
/// Catches distributed failure patterns where z4-sat false UNSAT affects many
/// frames (each under the per-frame `MAX_CROSSCHECK_FAILURES` threshold).
/// Without this, a circuit that triggers failures at frame 1, then frame 2,
/// then frame 3, etc. would never hit the per-frame threshold but would still
/// suffer repeated expensive solver rebuilds.
///
/// Value = 2 * MAX_CROSSCHECK_FAILURES: slightly above per-frame max to allow
/// normal per-frame recovery before triggering, but low enough to catch
/// distributed patterns within 10 total failures.
pub(super) const MAX_TOTAL_CROSSCHECK_FAILURES: usize = 10;

/// Maximum times a proof obligation can be re-queued due to Unknown results
/// before being dropped. When the solver backend is already at its simplest
/// (SimpleSolver) and still returns Unknown, re-queuing the PO is futile.
/// This prevents the secondary infinite loop where Unknown POs cycle forever.
pub(super) const MAX_UNKNOWN_REQUEUES: usize = 3;

/// Maximum number of spurious init-consistent predecessors before skipping
/// verify_trace entirely for init-consistent predecessors (#4105).
pub(super) const MAX_SPURIOUS_INIT_PREDS: usize = 3;

/// Maximum number of solver rebuilds per frame before giving up on that
/// frame's solver and treating Unknown/poisoned results conservatively (#4105).
///
/// When a solver at frame `i` is rebuilt more than this many times (due to
/// poisoning from z4-sat panics or Unknown results triggering rebuilds),
/// further rebuilds are skipped and the query result is treated as Sat
/// (conservative: no false UNSAT). This prevents the infinite rebuild loop
/// observed on microban_1 where constraint-dense formulas cause repeated
/// solver corruption at the same frame.
pub(super) const MAX_SOLVER_REBUILDS_PER_FRAME: usize = 3;

/// Number of z4-sat panics before falling back to SimpleSolver (#4092).
///
/// z4-sat panics indicate internal corruption (backtrack bugs, conflict analysis
/// errors). The corruption may have produced incorrect UNSAT results *before*
/// the panic manifested — the panic is just the final symptom. After this many
/// panics, fall back to SimpleSolver and purge all frame lemmas.
///
/// Set to 1: a single panic means the solver is unreliable on this circuit.
/// For small circuits (<50 latches), SimpleSolver is fast enough.
pub(super) const PANIC_FALLBACK_THRESHOLD: usize = 1;

/// Maximum times `get_bad()` may return the same bad cube at a given depth
/// before the blocking loop advances to the next depth (#4139).
///
/// When `drop_po` silently discards a high-activity proof obligation without
/// blocking the cube, `get_bad()` rediscovers the same bad state, creating an
/// infinite cycle:
///   1. `get_bad()` finds bad state S
///   2. `block_one` finds predecessor P, P is init-consistent → re-queued
///   3. `drop_po` drops P (activity too high) without blocking S
///   4. `get_bad()` finds S again → back to step 2
///
/// After `MAX_BAD_CUBE_REPEATS` rediscoveries of the same cube, the blocking
/// loop breaks and IC3 advances to the next depth. This is sound: IC3 frames
/// are over-approximations, and the unblocked cube will be re-examined at the
/// next depth where additional frame lemmas may enable successful blocking.
pub(super) const MAX_BAD_CUBE_REPEATS: usize = 10;

/// Literal ordering strategy for MIC generalization.
///
/// Controls the order in which literals are tried for removal during
/// the MIC (Minimal Inductive Clause) generalization loop. Different
/// orderings lead to different generalization paths and complementary
/// coverage across portfolio members.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralizationOrder {
    /// Sort by VSIDS activity (default). Low-activity literals are tried
    /// for removal first (backward iteration over activity-sorted array).
    /// This is the standard rIC3 approach.
    Activity,
    /// Reverse topological order: drop output-side latches before input-side.
    /// Uses the AND-gate depth from each latch to the primary inputs.
    /// Latches further from inputs (deeper in the circuit) are tried for
    /// removal first, since they depend on more variables and are more
    /// likely to be don't-cares in the generalization.
    ReverseTopological,
    /// Random shuffle using the config's random_seed. Different seeds
    /// produce different orderings, providing pure diversity without any
    /// heuristic bias. Useful in portfolios where activity-based ordering
    /// might consistently miss certain generalizations.
    RandomShuffle,
}

impl Default for GeneralizationOrder {
    fn default() -> Self {
        GeneralizationOrder::Activity
    }
}

/// Restart strategy hint for IC3 frame solvers.
///
/// These are advisory hints stored in the IC3 configuration. Currently
/// z4-sat manages its own restart schedule internally, so these are not
/// directly applied. They serve as portfolio diversity knobs for future
/// integration when z4-sat supports configurable restart strategies.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RestartStrategy {
    /// Use the solver's default restart strategy.
    Default,
    /// Geometric restart: conflicts_to_restart = base * factor^restarts.
    /// More aggressive restarts for smaller base values.
    Geometric { base: usize, factor: f64 },
    /// Luby sequence restart: conflicts_to_restart = unit * luby(restarts).
    /// Provides a good balance of short and long restart intervals.
    Luby { unit: usize },
}

impl Default for RestartStrategy {
    fn default() -> Self {
        RestartStrategy::Default
    }
}

/// IC3 engine configuration for portfolio diversity.
///
/// Each field controls a knob that can be varied across portfolio members.
/// rIC3 varies: ctg on/off, ctg_max, ctg_limit, ctp, internal signals,
/// drop_po, random seed, and more. We mirror the most impactful axes.
///
/// Reference: rIC3 `src/portfolio/portfolio.toml` (16 engine configs).
#[derive(Debug, Clone)]
pub struct Ic3Config {
    /// Enable CTP (Counter-To-Propagation) in propagate().
    pub ctp: bool,
    /// Enable infinity frame promotion.
    pub inf_frame: bool,
    /// Enable internal signals (FMCAD'21 AND gate variables in cubes).
    pub internal_signals: bool,
    /// Enable ternary simulation pre-reduction in find_bad_in_frame.
    pub ternary_reduce: bool,
    /// Max CTG (Counter-To-Generalization) attempts per literal drop in MIC.
    /// Higher values = more generalization effort. Default: 3. rIC3 varies 3..5.
    pub ctg_max: usize,
    /// Max recursive trivial_block depth during CTG.
    /// Higher values allow deeper predecessor blocking. Default: 1. rIC3 varies 1..15.
    pub ctg_limit: usize,
    /// Enable circuit-size-based CTG adaptation at engine construction time.
    ///
    /// When enabled, adjusts CTG parameters based on circuit size:
    /// - Small circuits (<100 latches): aggressive CTG (ctg_max=max(cfg,5), ctg_limit=max(cfg,15))
    /// - Medium circuits (100..=500 latches): use configured values as-is
    /// - Large circuits (>500 latches): conservative CTG (ctg_max=min(cfg,2), ctg_limit=min(cfg,1))
    pub circuit_adapt: bool,
    /// Max CTP attempts per lemma push in propagate().
    /// Only used when `ctp` is true. Default: 3.
    pub ctp_max: usize,
    /// Random seed for activity initialization and randomized MIC ordering,
    /// providing tie-breaking diversity across portfolio members.
    /// Mirrors rIC3's `--rseed` parameter. Default: 0 (no perturbation).
    pub random_seed: u64,
    /// Literal ordering strategy for MIC generalization.
    pub gen_order: GeneralizationOrder,
    /// SAT solver backend. Default: Varisat (truly incremental with UNSAT cores).
    /// See [`SolverBackend`] for available options and trade-offs.
    pub solver_backend: SolverBackend,
    /// Advisory restart strategy hint for IC3 frame solvers.
    pub restart_strategy: RestartStrategy,
    /// Enable parent lemma heuristic in MIC generalization.
    ///
    /// When generalizing a cube at frame k, find a "parent lemma" in frame k-1
    /// that subsumes the cube, and sort MIC literals so that parent-lemma
    /// literals are tried for removal last. This biases generalization toward
    /// reusing structure from already-proven lemmas.
    ///
    /// Reference: rIC3 `mic.rs:227` — CAV'23 parent lemma heuristic.
    pub parent_lemma: bool,
    /// Enable CTG-enhanced down() MIC variant.
    ///
    /// When a literal-drop fails in MIC, instead of just marking the literal
    /// as essential, extract the counterexample model and shrink the cube by
    /// keeping only literals present in the model. This is more aggressive than
    /// standard literal-dropping and can find better generalizations.
    ///
    /// Reference: rIC3 `mic.rs:122` — `ctg_down()` function.
    pub ctg_down: bool,
    /// Enable proof obligation dropping (GAP-2).
    ///
    /// When a proof obligation's activity exceeds the threshold (20.0),
    /// it is silently dropped instead of being processed. This prevents
    /// infinite loops on benchmarks where a cube keeps getting rediscovered
    /// but cannot be blocked efficiently — a common pathology on hard
    /// industrial benchmarks.
    ///
    /// The activity score is bumped each time the PO is re-encountered
    /// and decayed (x0.6 per frame level) when pushed to a higher frame.
    ///
    /// Reference: rIC3 `block.rs:121` — `if self.cfg.drop_po && po.act > 20.0`.
    pub drop_po: bool,
    /// Activity threshold for proof obligation dropping (GAP-2).
    ///
    /// When `drop_po` is enabled and a PO's activity exceeds this threshold,
    /// the PO is dropped. Higher thresholds allow more re-attempts before
    /// giving up, at the cost of spending more time on hard-to-block cubes.
    /// Lower thresholds drop cubes more aggressively, freeing solver time for
    /// other obligations.
    ///
    /// Default: 20.0 (matches rIC3). Portfolio diversity: vary between 10.0
    /// and 40.0 to explore different trade-offs. Lower values help on
    /// benchmarks with many thrashing cubes; higher values help when cubes
    /// eventually become blockable after sufficient frame lemmas accumulate.
    pub drop_po_threshold: f64,
    /// Enable dynamic generalization parameters (GAP-5).
    ///
    /// Instead of using fixed CTG parameters for all proof obligations,
    /// dynamically adjust them based on the PO's activity chain. High-activity
    /// POs (indicating thrashing) get more aggressive generalization:
    /// - Activity < 10.0: no CTG (level=0, max=0, limit=0)
    /// - Activity 10.0..40.0: moderate CTG (level=1, max=2+, limit=1)
    /// - Activity >= 40.0: aggressive CTG (level=1, max=5, limit=5+)
    ///
    /// This allows IC3 to invest more effort in cubes that are proving
    /// difficult to block, while keeping overhead low for easy cubes.
    ///
    /// Reference: rIC3 `block.rs:129-159` — dynamic MicType selection.
    pub dynamic: bool,
    /// Enable predicate propagation (backward analysis) for bad-state discovery.
    ///
    /// When enabled, IC3 uses a backward transition solver to find predecessors
    /// of bad states, complementing the standard forward `get_bad()` query.
    /// The backward solver encodes: Trans(s,s') AND bad(s') AND !bad(s).
    ///
    /// Predprop helps on benchmarks where the property has small backward
    /// reachability even if forward IC3 struggles with coarse frame approximations.
    ///
    /// Reference: rIC3 `ic3/predprop.rs` — `PredProp` struct (127 LOC).
    pub predprop: bool,
    /// VSIDS decay factor for the bucket-queue VSIDS used in MIC literal ordering.
    ///
    /// Controls how quickly old activity scores fade relative to new bumps.
    /// Higher values (closer to 1.0) keep older bumps relevant longer, producing
    /// more stable literal orderings. Lower values (closer to 0.5) make the
    /// ordering more responsive to recent queries.
    ///
    /// Portfolio diversity: varying decay across configs produces different
    /// MIC literal orderings even with the same seed. Default: 0.99.
    /// Typical range: 0.75..0.999.
    pub vsids_decay: f64,
    /// Number of IC3 SAT restarts before switching from bucket-queue VSIDS
    /// (O(1) amortized variable selection) to binary-heap VSIDS (O(log n) exact).
    ///
    /// - `0` = start directly in heap mode (skip bucket queue entirely)
    /// - `10` = default (switch after 10 restarts, matching rIC3's GipSAT)
    /// - `50` = keep bucket queue longer (good for circuits with many short queries)
    pub bucket_queue_restarts: usize,
    /// Maximum number of literal-drop SAT calls per MIC invocation (#4072).
    ///
    /// Limits the expensive per-literal inductiveness checks in the MIC
    /// drop loop. For arithmetic circuits where carry chains make most
    /// literals essential, this prevents O(n) wasted SAT calls.
    ///
    /// - `0` = unlimited (default, standard MIC behavior)
    /// - `N > 0` = stop after N failed+successful drops combined
    pub mic_drop_budget: usize,
    /// Enable per-latch flip_to_none pre-filtering in the lift path (#4091).
    ///
    /// After the frame solver returns SAT (predecessor found), use z4-sat's
    /// native `flip_to_none` on each latch variable to identify don't-cares
    /// before SAT-based lifting. Latches that can be flipped are excluded
    /// from the lift solver's cube, reducing both the UNSAT core extraction
    /// cost and the ternary flip_to_none pass.
    ///
    /// This is the tla-aiger equivalent of rIC3's approach in
    /// `transys/lift.rs:62`: `!satif.flip_to_none(s)`.
    ///
    /// Also enables flip_to_none-based shrinking in MIC CTG-down, matching
    /// rIC3's `mic.rs:96-100`.
    ///
    /// Enabled by default for z4-sat backends (which implement flip_to_none).
    /// Falls back gracefully on backends where flip_to_none returns false.
    pub flip_to_none_lift: bool,
    /// Maximum number of `get_bad()` SAT calls per depth level (#4072).
    ///
    /// On arithmetic circuits with 64+ latches, the blocking phase at each
    /// depth level may never terminate because the number of distinct bad cubes
    /// is exponential. The blocking budget forces IC3 to advance to the next
    /// depth after N bad-state discoveries, even if `get_bad()` still finds
    /// reachable bad states.
    ///
    /// Advancing early is sound: IC3's frame sequence still over-approximates
    /// reachability. The unblocked cubes will be re-discovered at the next
    /// depth where they may be easier to block (more frame lemmas available).
    ///
    /// - `0` = unlimited (default, standard IC3 behavior)
    /// - `N > 0` = advance after N get_bad() SAT calls return bad cubes
    pub blocking_budget: usize,
    /// Number of variable orderings to try during MIC generalization (#4099).
    ///
    /// Multi-ordering lift runs MIC with multiple literal orderings and keeps
    /// the shortest (most general) result. Values:
    /// - `0` or `1` = disabled (standard single-ordering MIC)
    /// - `2` = try primary ordering + one complementary ordering
    /// - `3` = try primary + complementary + random shuffle (maximum diversity)
    ///
    /// Additional passes only attempted when first result > half original cube
    /// and circuit has > 15 latches.
    pub multi_lift_orderings: usize,
    /// Validation strategy for the post-convergence invariant check (#4121).
    ///
    /// Controls which validation checks are performed after IC3 converges.
    /// High-constraint-ratio circuits (e.g., qspiflash with 157 latches, ~800
    /// constraints) can timeout during validation even with Z4NoPreprocess.
    /// Speed-focused portfolio configs can skip validation since at least one
    /// portfolio member (with Auto) always validates.
    pub validation_strategy: ValidationStrategy,
    /// Enable parent lemma MIC seeding optimization (CAV'23 #4150).
    ///
    /// When a proof obligation has a parent (po.next), and the parent's cube
    /// was previously blocked with a lemma, use the intersection of the
    /// current cube and the parent's blocking lemma as the starting point for
    /// MIC generalization. This produces tighter lemmas faster by reducing the
    /// initial literal set to structurally relevant variables.
    pub parent_lemma_mic: bool,
}

impl Default for Ic3Config {
    fn default() -> Self {
        // Conservative defaults: parent_lemma enabled (cheap, effective),
        // ctg_down disabled (more aggressive, may not always help).
        // drop_po enabled by default (matches rIC3: default_value_t = true).
        // dynamic disabled by default (matches rIC3: default_value_t = false).
        Ic3Config {
            ctp: false,
            inf_frame: false,
            internal_signals: false,
            ternary_reduce: false,
            ctg_max: DEFAULT_CTG_MAX,
            ctg_limit: DEFAULT_CTG_LIMIT,
            circuit_adapt: false,
            ctp_max: DEFAULT_CTP_MAX,
            random_seed: 0,
            gen_order: GeneralizationOrder::Activity,
            solver_backend: SolverBackend::default(),
            restart_strategy: RestartStrategy::Default,
            parent_lemma: true,
            ctg_down: false,
            drop_po: true,
            drop_po_threshold: 20.0,
            dynamic: false,
            predprop: false,
            vsids_decay: 0.99,
            bucket_queue_restarts: 10,
            flip_to_none_lift: true,
            mic_drop_budget: 0,
            blocking_budget: 0,
            multi_lift_orderings: 0,
            validation_strategy: ValidationStrategy::Auto,
            parent_lemma_mic: true,
        }
    }
}

/// Result of an IC3 model checking run.
#[derive(Debug)]
pub enum Ic3Result {
    /// Property holds: system is safe. Contains the convergence depth.
    Safe { depth: usize },
    /// Property violated: counterexample found.
    Unsafe {
        /// Depth of the counterexample trace.
        depth: usize,
        /// Counterexample trace: sequence of states from init to bad.
        /// Each state is a vector of (variable, value) pairs.
        trace: Vec<Vec<(Var, bool)>>,
    },
    /// Could not determine within resource limits.
    Unknown { reason: String },
}

/// Result of `get_bad()` — distinguishes standard bad states from
/// predicate-propagation predecessors so the main loop can route them
/// to different proof-obligation frames.
pub(super) enum GetBadResult {
    /// A state in F_k that satisfies the bad property (standard forward check).
    Bad(Vec<Lit>),
    /// A predecessor of bad found by backward analysis (predprop).
    /// This state is NOT bad itself — it's one transition step away from bad.
    Predecessor(Vec<Lit>),
}

use crate::sat_types::{Lit, Var};
