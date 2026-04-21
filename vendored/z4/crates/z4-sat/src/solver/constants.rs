// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CDCL solver tuning constants.
//!
//! All scheduling intervals, decay factors, and budget limits live here.
//! Values are calibrated against CaDiCaL defaults unless otherwise noted.
//! See `reference/cadical/src/options.hpp` for CaDiCaL's option table.

// ─── Preprocessing Budget ──────────────────────────────────────────

/// Maximum probes during preprocessing (per round).
/// CaDiCaL uses tick-proportional budgets with preprocessinit=2e6 ticks
/// floor. Since Z4 doesn't track per-probe ticks during preprocessing,
/// we use a generous count limit that prevents hangs on large instances
/// (e.g., shuffling-2: 138K vars, 4.7M clauses) while allowing thorough
/// probing on moderate instances.
/// CaDiCaL reference: `probeeffort=8`, `preprocessinit=2e6` (options.hpp).
pub(super) const MAX_PREPROCESS_PROBES: usize = 2_000;

// ─── Restart Parameters ─────────────────────────────────────────────

/// Default base restart interval (conflicts per Luby unit)
pub(super) const DEFAULT_RESTART_BASE: u64 = 100;

/// Extension-mode restart warmup: suppress restarts for the first N conflicts.
/// Theory/extension mode benefits from a slightly longer warmup than pure SAT
/// because theory propagation establishes an initial search trajectory that
/// premature restarts would disrupt. The fast EMA needs ~33 conflicts to
/// stabilize, so 50 provides a reasonable margin.
pub(super) const EXTENSION_RESTART_WARMUP: u64 = 50;

/// Fast EMA decay factor (short window, ~33 conflicts)
/// decay = 1 - 1/33 (matches CaDiCaL emagluefast=33)
pub(super) const EMA_FAST_DECAY: f64 = 1.0 - 1.0 / 33.0;

/// Slow EMA decay factor (long window, ~100000 conflicts)
/// decay = 1 - 1/100000 = 0.99999 (matches CaDiCaL's emaglueslow)
pub(super) const EMA_SLOW_DECAY: f64 = 0.99999;

/// Restart margin (focused mode): fast EMA must exceed slow EMA * margin.
/// CaDiCaL restartmarginfocused=10 → (100+10)/100 = 1.10.
pub(super) const RESTART_MARGIN_FOCUSED: f64 = 1.10;

/// Restart margin (stable mode): higher threshold = harder to restart.
/// CaDiCaL restartmarginstable=25 → (100+25)/100 = 1.25.
/// Currently dead code (stable uses reluctant doubling), but architecturally
/// correct for when EMA restarts are enabled in stable mode.
#[allow(dead_code)]
pub(super) const RESTART_MARGIN_STABLE: f64 = 1.25;

/// Minimum conflicts between restarts in focused mode (restart blocking).
/// CaDiCaL restartint=2 (with <= gate, effectively 3 conflicts).
/// Z4 uses >= gate so RESTART_INTERVAL=2 allows restart after 2 conflicts.
pub(super) const RESTART_INTERVAL: u64 = 2;

/// Trail-length EMA decay for restart blocking (slow EMA).
/// Tracks average trail length over ~5000 conflicts.
/// Audemard & Simon (SAT 2012): block restarts when current trail is
/// significantly longer than average, indicating productive search.
pub(super) const TRAIL_EMA_DECAY: f64 = 1.0 - 1.0 / 5000.0;

/// Margin for trail-based restart blocking (DISABLED — CaDiCaL does not
/// implement Glucose's trail blocking). Kept for possible future experiments.
/// Block restart if trail_len > margin * trail_ema_slow.
#[allow(dead_code)]
pub(super) const TRAIL_BLOCKING_MARGIN: f64 = 1.25;

/// Warmup period before trail blocking activates (DISABLED — see above).
#[allow(dead_code)]
pub(super) const TRAIL_BLOCKING_WARMUP: u64 = 100;

/// Minimum conflicts before considering Glucose-style restarts.
///
/// CaDiCaL has NO warmup gate — it relies entirely on ADAM-style EMA bias
/// correction (ema.cpp) to handle the cold-start. Z4 implements the same
/// bias correction (update_lbd_ema), so a warmup is unnecessary.
///
/// Previously 100, which suppressed all restarts for the first 100 conflicts
/// and prevented early search diversification. Reduced to 2 to match
/// CaDiCaL's effective behavior (restartint=2 is the only gate).
pub(super) const RESTART_MIN_CONFLICTS: u64 = 2;

/// Initial stabilization phase length (conflicts before first mode switch)
/// CaDiCaL uses 1000 conflicts for first focused phase
pub(super) const STABLE_PHASE_INIT: u64 = 1000;

/// Base period for reluctant doubling (Knuth's Luby sequence) in stable mode.
/// Restart interval = period x luby(n). CaDiCaL: reluctantint=1024.
pub(super) const RELUCTANT_INIT: u64 = 1024;

/// Maximum Luby sequence value before resetting to (u=1, v=1).
/// CaDiCaL: reluctantmax=1048576. Prevents unbounded interval growth.
pub(super) const RELUCTANT_MAX: u64 = 1_048_576;

// ─── Random Decision Parameters ─────────────────────────────────────

/// Inter-burst interval multiplier (CaDiCaL randecint=500)
/// Next burst at: conflicts + phases * ln(phases) * RANDEC_INT
pub(super) const RANDEC_INT: f64 = 500.0;

/// Base length multiplier for random decision burst duration (CaDiCaL randeclength=10)
/// Burst length = RANDEC_LENGTH * ln(phase_count + 10)
pub(super) const RANDEC_LENGTH: f64 = 10.0;

// ─── Clause DB Reduction ─────────────────────────────────────────────

/// First clause DB reduction after this many conflicts.
/// CaDiCaL: `reduceinit = 300` (options.hpp:179).
pub(super) const FIRST_REDUCE_DB: u64 = 300;

/// Base interval multiplier for clause DB reduction scheduling.
/// CaDiCaL: `reduceint = 25` (options.hpp:180).
/// Actual interval: `REDUCE_DB_INC * sqrt(conflicts)`, growing with search depth.
pub(super) const REDUCE_DB_INC: u64 = 25;

/// Fraction of tier-2 reduction candidates deleted each `reduce_db()` call.
/// CaDiCaL: `reducetarget = 75` (options.hpp:181).
pub(super) const REDUCE_TARGET_PERCENT: usize = 75;
const _: () = assert!(REDUCE_TARGET_PERCENT <= 100);

/// Poll the process-wide memory limit after this many conflicts.
///
/// This amortizes the global-memory probe used by `TermStore::global_memory_exceeded()`
/// while still bounding mid-solve overshoot on hard SAT instances (#6552).
pub(super) const PROCESS_MEMORY_CHECK_INTERVAL: u64 = 10_000;

/// Tier1 usage percentage limit (CaDiCaL tier1limit=50)
/// tier1 boundary is set so accumulated usage <= this % of total
pub(super) const TIER1_LIMIT_PCT: u64 = 50;

/// Tier2 usage percentage limit (CaDiCaL tier2limit=90)
pub(super) const TIER2_LIMIT_PCT: u64 = 90;

/// Initial conflict interval between clause flushes.
/// CaDiCaL: `flushint = 1e5` (options.hpp:133), but `flush` defaults to 0
/// (DISABLED). Flush is more aggressive than reduce — it marks ALL unused
/// learned clauses as garbage regardless of tier. On hard combinatorial
/// instances requiring deep search (300K-1.2M conflicts), flushing deletes
/// valuable learned clauses that took many conflicts to discover.
/// Disabled (u64::MAX) to match CaDiCaL's default.
pub(super) const FLUSH_INIT: u64 = u64::MAX;

/// Multiplicative factor for flush interval growth.
/// CaDiCaL: `flushfactor = 3` (options.hpp:132).
/// Intervals grow geometrically: 100K, 300K, 900K, 2.7M, ...
pub(super) const FLUSH_FACTOR: u64 = 3;

// ─── Backtracking ────────────────────────────────────────────────────

/// Maximum levels to jump before using chronological backtracking
/// If jump_levels > CHRONO_LEVEL_LIMIT, use chronological backtracking instead
pub(super) const CHRONO_LEVEL_LIMIT: u32 = 100;

// ─── Vivification ────────────────────────────────────────────────────

/// Run vivification after this many conflicts (was 10000, reduced for BV #757).
/// Acts as a minimum spacing guard between vivification rounds; actual effort
/// is controlled by tick-proportional budgeting (VIVIFY_EFFORT_PERMILLE).
pub(super) const VIVIFY_INTERVAL: u64 = 2000;

/// Interval between irredundant vivification passes.
/// Set lower than the initial 10K to run irredundant vivification more
/// promptly, but higher than learned (2K) since irredundant vivification
/// uses standalone propagation which is slower per-clause.
pub(super) const VIVIFY_IRRED_INTERVAL: u64 = 5000;

/// Number of irredundant clauses to vivify per call.
/// Higher than learned budget (500) because irredundant clauses are
/// typically the bottleneck on structured instances.
pub(super) const VIVIFY_IRRED_CLAUSES_PER_CALL: usize = 1000;

/// Maximum adaptive multiplier for irredundant vivification interval.
/// Caps backoff at 64 * VIVIFY_IRRED_INTERVAL to avoid starvation.
pub(super) const VIVIFY_IRRED_MAX_DELAY_MULTIPLIER: u64 = 64;

/// Vivification effort as per-mille of search ticks since last vivification.
/// CaDiCaL: `vivifyeffort = 50` (options.hpp:258). 50 per-mille = 5%.
pub(super) const VIVIFY_EFFORT_PERMILLE: u64 = 50;

/// Tier effort weights for splitting the vivification tick budget.
/// CaDiCaL vivify.cpp:1753-1764: tier1=4, tier2=2, tier3=1, irred=3.
pub(super) const VIVIFY_TIER_WEIGHT_CORE: u64 = 4;
pub(super) const VIVIFY_TIER_WEIGHT_TIER2: u64 = 2;
pub(super) const VIVIFY_TIER_WEIGHT_OTHER: u64 = 1;
pub(super) const VIVIFY_TIER_WEIGHT_IRRED: u64 = 3;

/// Minimum vivification effort (propagations) per call.
/// CaDiCaL controls vivification effort via `vivifyeffort` (options.hpp:258,
/// per-mille efficiency) and per-tier options `vivifytier{1,2,3}eff`.
/// This constant serves a similar role to `elimmineff` (options.hpp:99) for
/// elimination: a minimum floor ensuring progress even when few search ticks
/// have accumulated (e.g. early in the search or on trivial instances).
pub(super) const VIVIFY_MIN_EFFORT: u64 = 10_000;

/// Maximum number of consecutive retries for a successfully vivified clause.
/// CaDiCaL vivify.cpp:1598-1608 (`opts.vivifyretry`, default 1): when a clause
/// is strengthened and still has >2 literals, push it back onto the schedule for
/// another attempt. This catches cascading simplifications that a single pass misses.
pub(super) const VIVIFY_RETRY_LIMIT: u32 = 1;

// ─── Subsumption ─────────────────────────────────────────────────────

/// Run subsumption after this many conflicts.
/// CaDiCaL runs forward subsumption as part of elimination (not a separate pass).
/// On large formulas (>1M clauses), frequent standalone subsumption rounds have
/// high per-round overhead from dirty-variable scanning. Values below 10K cause
/// 30%+ conflict rate regression on FmlaEquivChain (4.7M clauses). The adaptive
/// backoff (1.5x growth on progress, 2x on idle) naturally reduces frequency
/// when rounds are unproductive (#3639).
pub(super) const SUBSUME_INTERVAL: u64 = 20_000;

/// Subsumption effort as per-mille of search propagations.
/// CaDiCaL: `subsumeeffort = 1000` (options.hpp:218).
pub(super) const SUBSUME_EFFORT_PER_MILLE: u64 = 1_000;

/// Maximum subsumption check limit per call.
/// CaDiCaL: `subsumemaxeff = 1e8` (options.hpp:220).
pub(super) const SUBSUME_MAX_EFFORT: u64 = 100_000_000;

/// Minimum subsumption check limit per call.
/// CaDiCaL: `subsumemineff = 0` (options.hpp:221).
pub(super) const SUBSUME_MIN_EFFORT: u64 = 0;

/// Maximum subsumption scheduling interval (conflicts).
/// With 1.5x growth from 20k: 20k, 30k, 45k, 67.5k, 101k, 152k, ...
/// Caps at 160k to prevent starvation on long runs while reducing overhead on
/// structured instances.
pub(super) const SUBSUME_MAX_INTERVAL: u64 = 160_000;

/// Maximum subsumption interval when rounds make no database progress.
/// On hard structured formulas, no-op rounds are often net-negative; allow
/// a longer cooldown before retrying subsumption.
pub(super) const SUBSUME_MAX_IDLE_INTERVAL: u64 = 320_000;

// ─── Probing ─────────────────────────────────────────────────────────

/// Run failed literal probing after this many conflicts (was 15000, reduced for BV #757)
/// Note: 100 was too aggressive; 1000 is 15x more frequent but avoids dominating solve time
pub(super) const PROBE_INTERVAL: u64 = 1000;

// ─── Backbone Computation ───────────────────────────────────────────

/// Backbone inprocessing interval (in conflicts).
/// CaDiCaL runs backbone interleaved with probing (backbone.cpp:622).
/// Same interval as probing since backbone is a probing-like technique.
pub(super) const BACKBONE_INTERVAL: u64 = 2000;

/// Maximum backbone interval under growing backoff.
/// Keeps unproductive restart-level backbone passes from stretching indefinitely.
pub(super) const BACKBONE_MAX_INTERVAL: u64 = 64_000;

/// Maximum number of backbone rounds (phases) before backbone is permanently disabled.
/// CaDiCaL: `backbonerounds = 100` scaled by phase count, capped at
/// `backbonemaxrounds = 1000` (options.hpp:30-31). Z4 uses a simpler flat
/// limit matching CaDiCaL's `backbonemaxrounds` default.
pub(super) const BACKBONE_MAX_ROUNDS: u32 = 1_000;

// ─── Bounded Variable Elimination ────────────────────────────────────

/// BVE inprocessing base interval (in conflicts).
/// CaDiCaL uses `elimint=2000` scaled by clause/variable ratio and
/// growing linearly with each phase: `elimint * (phases + 1) * scale()`.
/// Use 2000 to match CaDiCaL's base frequency more closely on SAT workloads.
pub(super) const BVE_INTERVAL_BASE: u64 = 2_000;

/// Maximum number of variable eliminations per BVE call.
/// CaDiCaL uses a resolution-count limit instead of a fixed count.
/// We use a generous per-call cap; the growth bound and occurrence
/// limit handle actual pruning.
pub(super) const MAX_BVE_ELIMINATIONS: usize = 100_000;

/// Per-call elimination cap for preprocessing fastelim.
/// CaDiCaL's fastelim runs until the resolution budget is exhausted or
/// Maximum variable eliminations per fastelim call. With watch-free BVE
/// mode (watches disconnected during preprocessing), per-elimination
/// overhead is ~2x CaDiCaL's (down from 16x). CaDiCaL has no cap
/// (effort-limited only). Remove the artificial ceiling so preprocessing
/// can eliminate 30-50% of variables on BVE-dominated formulas.
pub(super) const FASTELIM_MAX_ELIMINATIONS: usize = 100_000;

/// Maximum number of BVE rounds per inprocessing call.
/// Kissat: eliminaterounds=2. Z4 grows the growth_bound between inner
/// rounds (Kissat-style progressive bound, eliminate.c:339-372), so 3
/// rounds lets the bound progress from 0 to 2 within a single BVE phase.
/// This is critical for structured formulas like clique graphs where many
/// variables are only profitably eliminable at bound >= 1 (#8135).
pub(super) const BVE_ROUNDS: usize = 3;

/// Maximum number of BVE rounds during preprocessing fastelim.
/// CaDiCaL: fastelimrounds=4 (options.hpp:131). With watch-free BVE mode,
/// per-round overhead is low enough to afford 4 rounds with interleaved
/// subsumption. Variables exposed by earlier rounds are picked up by later
/// rounds, matching CaDiCaL's multi-round fastelim behavior.
pub(super) const PREPROCESS_BVE_ROUNDS: usize = 4;

/// Resolution effort as per-mille of search propagations.
/// CaDiCaL: `elimeffort = 1000` (options.hpp:93).
pub(super) const BVE_EFFORT_PER_MILLE: u64 = 1_000;

/// Minimum resolution effort (resolutions) for inprocessing.
/// CaDiCaL: `elimmineff = 1e7` (options.hpp:99).
pub(super) const BVE_MIN_EFFORT: u64 = 10_000_000;

/// Resolution effort for preprocessing fastelim.
/// With watch-free BVE mode (Phase 1 of BVE perf design), per-resolution
/// overhead is ~2x CaDiCaL's (down from 16x). Match CaDiCaL's minimum
/// effort budget. CaDiCaL: `elimmineff = 1e7` (options.hpp:99).
pub(super) const FASTELIM_EFFORT: u64 = 10_000_000;

/// Clause count threshold for scaling down fastelim effort (#8136).
pub(super) const FASTELIM_SCALE_CLAUSE_THRESHOLD: u64 = 1_000_000;

/// Minimum scaled fastelim effort after clause-count scaling (#8136).
pub(super) const FASTELIM_MIN_SCALED_EFFORT: u64 = 2_000_000;

/// Wall-clock time limit (seconds) for preprocessing BVE rounds (#8136).
pub(super) const FASTELIM_WALL_CLOCK_LIMIT_SECS: u64 = 3;

/// Skip preprocessing BVE above this active clause count + high density (#8136).
pub(super) const PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD: usize = 2_000_000;

/// Minimum clause/variable density to trigger preprocessing BVE skip (#8136).
pub(super) const PREPROCESS_BVE_SKIP_DENSITY: f64 = 20.0;

/// Maximum resolution effort (resolutions).
/// CaDiCaL: `elimmaxeff = 2e9` (options.hpp:98).
pub(super) const BVE_MAX_EFFORT: u64 = 2_000_000_000;

/// Maximum interleaved elimination phase rounds (BVE → subsume → BCE).
/// CaDiCaL runs up to `elimrounds=2` BVE rounds with interleaved
/// subsumption and BCE between them (elim.cpp:1060-1098). Each round
/// creates new elimination candidates: BVE produces resolvents that
/// subsumption can simplify, and subsumption removals enable further
/// BVE. The loop exits when no technique produces new candidates.
/// Matches CaDiCaL `elimrounds=2` (options.hpp:102).
pub(super) const ELIM_INTERLEAVE_ROUNDS: usize = 2;

// ─── Blocked Clause Elimination ──────────────────────────────────────

/// Run BCE after this many conflicts
pub(super) const BCE_INTERVAL: u64 = 25000;

/// Maximum number of blocked clause eliminations per call
pub(super) const MAX_BCE_ELIMINATIONS: usize = 200;

// ─── Covered Clause Elimination (CCE) ────────────────────────────────

/// Run CCE after this many conflicts. Same interval as BCE.
/// CaDiCaL defaults `opts.cover = false`, so CCE only runs when explicitly
/// enabled. Uses the same reconstruction stack format as BCE.
pub(super) const CCE_INTERVAL: u64 = 25000;

/// CCE effort as per-mille of search propagations.
/// CaDiCaL: `covereffort = 4` (options.hpp). 4 per-mille = 0.4%.
pub(super) const CCE_EFFORT_PER_MILLE: u64 = 4;

/// Minimum CCE effort (clause scans) per call.
/// CaDiCaL: `covermineff = 0` (options.hpp).
pub(super) const CCE_MIN_EFFORT: u64 = 0;

/// Maximum CCE effort (clause scans) per call.
/// CaDiCaL: `covermaxeff = 1e8` (options.hpp).
pub(super) const CCE_MAX_EFFORT: u64 = 100_000_000;

// ─── Conditioning (GBCE) ─────────────────────────────────────────────

/// Run conditioning (GBCE) after this many conflicts
pub(super) const CONDITION_INTERVAL: u64 = 10000;

/// Maximum number of conditioned clause eliminations per call
pub(super) const MAX_CONDITION_ELIMINATIONS: usize = 100_000;

// ─── Congruence Closure ──────────────────────────────────────────────

/// Run congruence closure (gate-based equivalence detection) after this many conflicts.
/// CaDiCaL effective rate: ~once per 587 conflicts (15 rounds in 8K conflicts).
/// Previous value 10000 was 17x too infrequent. CaDiCaL: `congruence.cpp`.
pub(super) const CONGRUENCE_INTERVAL: u64 = 2000;

/// Maximum congruence scheduling interval after exponential backoff.
/// CaDiCaL uses exponential backoff: each fruitless call doubles the delay.
/// On shuffling-2 (4.9M clauses), congruence was running every 2K conflicts
/// on a 63K-conflict solve, causing ~31 × 1.5s = 46s of wasted work (#7135).
/// With 2× growth from 2K: 2K → 4K → 8K → 16K → 32K → 64K — only 5 calls.
pub(super) const CONGRUENCE_MAX_INTERVAL: u64 = 64_000;

// ─── Decompose (SCC) ─────────────────────────────────────────────────

/// Run decompose (SCC equivalent literal substitution) after this many conflicts
pub(super) const DECOMPOSE_INTERVAL: u64 = 10000;

/// Maximum decompose scheduling interval after growing backoff.
/// Unproductive decompose calls (no equivalences found) grow the interval 1.5×.
/// Productive calls reset to base. CaDiCaL: decompose uses Delay struct.
/// With 1.5× growth from 10K: 10K → 15K → 22K → 33K → 50K → 75K → 100K.
pub(super) const DECOMPOSE_MAX_INTERVAL: u64 = 100_000;

// ─── Factorization ───────────────────────────────────────────────────

/// Run factorization after this many conflicts.
/// CaDiCaL runs factoring after BVE; we fire on the same schedule.
pub(super) const FACTOR_INTERVAL: u64 = 10000;

/// Maximum factor scheduling interval after growing backoff.
/// Unproductive factor calls (0 factored clauses) grow the interval 1.5×.
/// Productive calls reset to base. CaDiCaL: factor uses Delay struct.
pub(super) const FACTOR_MAX_INTERVAL: u64 = 100_000;

/// Delay factorization until enough elimination rounds have run.
/// CaDiCaL option parity: `factordelay = 4` (options.hpp).
pub(super) const FACTOR_DELAY: u64 = 4;

/// Factor effort as per-mille of search ticks since last factor call.
/// CaDiCaL: `factoreffort = 50` (options.hpp:122). 50 per-mille = 5%.
pub(super) const FACTOR_EFFORT_PERMILLE: u64 = 50;

/// Initial factor effort bonus (ticks) for inprocessing.
/// CaDiCaL: `factoriniticks = 300` (options.hpp:123) in millions.
/// CaDiCaL ticks include cache-line overhead (~13x per scan vs Z4's
/// 1-tick-per-clause-access), so 300M CaDiCaL ≈ 23M Z4-equivalent.
/// During inprocessing the proportional budget dominates; this bonus
/// only matters for the first call after search starts.
pub(super) const FACTOR_INIT_TICKS: u64 = 300_000_000;

/// Maximum factor effort per call.
pub(super) const FACTOR_MAX_EFFORT: u64 = 2_000_000_000;

// ─── Transitive Reduction ────────────────────────────────────────────

/// Run transitive reduction after this many conflicts
pub(super) const TRANSRED_INTERVAL: u64 = 15000;

/// Transred effort as per-mille of search propagations since last transred.
/// CaDiCaL: `transredeffort = 100` (options.hpp:250). 100 per-mille = 10%.
/// CaDiCaL transred uniquely uses propagations (not ticks) for effort.
pub(super) const TRANSRED_EFFORT_PERMILLE: u64 = 100;

/// Maximum transred effort (propagations).
/// CaDiCaL: `transredmaxeff = 1e8` (options.hpp:251).
pub(super) const TRANSRED_MAX_EFFORT: u64 = 100_000_000;

/// Minimum transred effort (propagations).
/// CaDiCaL: `transredmineff = 0` (options.hpp:252).
pub(super) const TRANSRED_MIN_EFFORT: u64 = 0;

// ─── Hyper-Ternary Resolution ────────────────────────────────────────

/// Run HTR after this many conflicts.
/// Coupled with decompose (CaDiCaL pattern: decompose → ternary → decompose).
/// Matches DECOMPOSE_INTERVAL so both fire in the same inprocessing pass.
pub(super) const HTR_INTERVAL: u64 = 10000;

/// Maximum number of resolvents per HTR call.
/// CaDiCaL uses `ternarymaxadd=1000` (10x clause count); we use a fixed cap
/// that's generous enough for structured instances without blowup on random.
pub(super) const MAX_HTR_RESOLVENTS: usize = 2000;

// ─── SAT Sweeping ────────────────────────────────────────────────────

/// Run SAT sweeping after this many conflicts
pub(super) const SWEEP_INTERVAL: u64 = 35000;

/// Maximum sweep scheduling interval after growing backoff.
/// Unproductive sweep calls (no rewrites) double the interval.
/// Productive calls reset to base. CaDiCaL: sweep uses Delay struct.
pub(super) const SWEEP_MAX_INTERVAL: u64 = 200_000;

/// Skip expensive equivalence preprocessing passes above this variable count.
/// Raised from 100K to 200K: asconhash benchmarks (158K vars) need
/// congruence/decompose/sweep during preprocessing to solve at 20s. CaDiCaL
/// has no variable-count gate for preprocessing.
pub(super) const PREPROCESS_EXPENSIVE_MAX_VARS: usize = 200_000;

/// Skip expensive equivalence inprocessing passes above this clause count.
/// On large residuals (>3M clauses), the O(clauses) SETUP cost of entering
/// techniques (building occurrence lists, sorting watches, SCC traversal)
/// exceeds the tick-proportional effort budget. CaDiCaL handles this via
/// per-technique threshold gates (if budget < thresh × clauses, skip), but
/// Z4's setup costs are not metered against tick budgets.
///
/// At 5M: catches 6g_6col (8.5M) while allowing shuffling-2 (4.7M post-BVE)
/// and 2dlx_ca (4.3M) to run expensive techniques. Raised from 3M: shuffling-2
/// benefits from SCC decompose finding equivalences post-BVE, and the per-
/// technique tick budgets already limit overhead on large residuals.
pub(super) const PREPROCESS_EXPENSIVE_MAX_CLAUSES: usize = 5_000_000;

/// Clause threshold for congruence + decompose during preprocessing and
/// inprocessing. Aligned with PREPROCESS_EXPENSIVE_MAX_CLAUSES (5M).
///
/// Raised from 3M to 5M: shuffling-2 (4.7M clauses) now runs congruence
/// and decompose. The congruence max-interval backoff (2K → 64K) and
/// decompose max-interval backoff (10K → 100K) limit repeated no-op calls.
/// CaDiCaL runs congruence on shuffling-2 and completes in <1s due to
/// tick-based effort limiting.
pub(super) const CONGRUENCE_MAX_CLAUSES: usize = 5_000_000;

// ─── Preprocessing Effort Budgets ────────────────────────────────────

/// Maximum propagations for probing during preprocessing (before search).
/// CaDiCaL uses preprocessinit=2M as base. Since we have no search ticks
/// during preprocessing, this is a fixed budget per preprocessing round.
/// On shuffling-2 (138K vars), unbounded probing caused >20s hangs (#6926).
pub(super) const PREPROCESS_PROBE_MAX_PROPAGATIONS: u64 = 2_000_000;

// ─── Unified Inprocessing (inprobe) ──────────────────────────────────

/// Base interval for the unified inprocessing round timer.
/// CaDiCaL default: `inprobeint = 100` (options.hpp:141).
/// Actual interval grows logarithmically: `25 * INPROBE_INTERVAL * log10(phase + 9)`.
pub(super) const INPROBE_INTERVAL: u64 = 100;

// ─── Variable Reorder ────────────────────────────────────────────────

/// Run clause-weighted variable reorder after this many conflicts.
/// Kissat default: `reorderint` (options.hpp). Z4 uses 20K, similar to
/// the BVE/factor/HTR interval range. Reorder is lightweight (O(vars +
/// irredundant_clauses)) so a moderate interval suffices.
pub(super) const REORDER_INTERVAL: u64 = 20_000;

/// Maximum reorder scheduling interval after growing backoff.
pub(super) const REORDER_MAX_INTERVAL: u64 = 200_000;

// ─── Rephasing ───────────────────────────────────────────────────────

/// Rephase interval base (conflicts).
/// CaDiCaL: `rephaseint = 1000` (options.hpp:189).
/// Schedule: delta = REPHASE_INITIAL * (rephase_count + 1), arithmetic progression.
pub(super) const REPHASE_INITIAL: u64 = 1000;

// ─── Walk/Local Search ───────────────────────────────────────────────

/// Default walk tick limit per round (effort budget).
/// Used only for startup walk before any search ticks have accumulated.
pub(super) const WALK_DEFAULT_LIMIT: u64 = 100_000;
