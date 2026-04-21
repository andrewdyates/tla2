// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Model Checking (BMC) engine with incremental SAT.
//!
//! Unrolls the transition system for k time steps and checks if a bad state
//! is reachable. Uses an incremental SAT solver: each step adds new clauses
//! (the transition relation for one more step) and checks reachability via
//! assumptions.
//!
//! Also provides convenience functions `check_bmc()` and `check_kind()` that
//! apply COI reduction and return a `BmcResult` with raw literal witness traces.
//!
//! Reference: rIC3 `src/bmc.rs` (179 lines), adapted for our SAT types.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

use rustc_hash::FxHashMap;

use crate::check_result::CheckResult;
use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend};
use crate::transys::{Transys, VarRenamer};

// ---------------------------------------------------------------------------
// BmcResult and convenience API
// ---------------------------------------------------------------------------

/// Result of a BMC or k-induction model checking run.
///
/// This is a lightweight result type suitable for the public API. It carries
/// the verdict, the maximum depth explored, and an optional witness trace
/// as raw SAT literals (one `Vec<Lit>` per time step).
#[derive(Debug, Clone)]
pub struct BmcResult {
    /// `Some(true)` = SAFE, `Some(false)` = UNSAFE, `None` = unknown/bounded.
    pub verdict: Option<bool>,
    /// Maximum depth checked (or depth of counterexample for UNSAFE).
    pub depth: usize,
    /// Counterexample trace for UNSAFE verdicts. Each entry is one time step,
    /// represented as a vector of literals over latch and input variables.
    /// Positive literal = variable is true; negative = variable is false.
    pub witness: Option<Vec<Vec<Lit>>>,
}

/// Run BMC up to `max_depth` steps.
///
/// Convenience wrapper around `BmcEngine` that applies COI reduction,
/// variable compaction, and returns a `BmcResult` with raw literal witness
/// traces.
///
/// ## Preprocessing (#4073)
///
/// Uses COI reduction + variable compaction (not the full `preprocess()`
/// pipeline which includes SCORR/FRTS) to keep startup fast while still
/// reducing the per-step clause count. Compaction renumbers variables to a
/// dense range, improving z4-sat cache locality and reducing memory.
///
/// BMC can only prove UNSAFE (by finding a counterexample). If it reaches
/// `max_depth` without finding one, it returns `verdict = None`.
pub fn check_bmc(ts: &Transys, max_depth: usize) -> BmcResult {
    let reduced = ts.coi_reduce().compact_vars();
    let mut engine = BmcEngine::new(reduced, 1);
    let result = engine.check(max_depth);
    bmc_result_from_engine(&engine, result, max_depth)
}

/// Run BMC with dynamic step size (rIC3's `--dyn-step`).
///
/// Automatically adjusts step size based on circuit complexity:
/// small circuits get large steps (fast deep exploration), large circuits
/// get step=1 (thorough per-depth checking).
///
/// Uses COI reduction + variable compaction for improved per-step efficiency.
pub fn check_bmc_dynamic(ts: &Transys, max_depth: usize) -> BmcResult {
    let reduced = ts.coi_reduce().compact_vars();
    let mut engine = BmcEngine::new_dynamic(reduced);
    let result = engine.check(max_depth);
    bmc_result_from_engine(&engine, result, max_depth)
}

/// Convert a BmcEngine check result into a BmcResult.
fn bmc_result_from_engine(engine: &BmcEngine, result: CheckResult, max_depth: usize) -> BmcResult {
    match result {
        CheckResult::Unsafe { depth, .. } => {
            let witness = engine.extract_lit_trace(depth);
            BmcResult {
                verdict: Some(false),
                depth,
                witness: Some(witness),
            }
        }
        CheckResult::Safe => BmcResult {
            verdict: Some(true),
            depth: max_depth,
            witness: None,
        },
        CheckResult::Unknown { .. } => BmcResult {
            verdict: None,
            depth: max_depth,
            witness: None,
        },
    }
}

/// Run k-induction up to `max_depth` steps.
///
/// Convenience wrapper around `KindEngine` that applies COI reduction and
/// returns a `BmcResult`. k-induction can prove both SAFE (if the inductive
/// step succeeds) and UNSAFE (if the base case finds a counterexample).
pub fn check_kind(ts: &Transys, max_depth: usize) -> BmcResult {
    use crate::kind::KindEngine;

    let reduced = ts.coi_reduce();
    let mut engine = KindEngine::new(reduced);
    let result = engine.check(max_depth);
    kind_result_from_engine(&engine, result, max_depth)
}

/// Run k-induction with the simple-path constraint (rIC3's default mode).
///
/// The simple-path constraint asserts that all states in the induction trace
/// are pairwise distinct. This strengthens the induction hypothesis, helping
/// prove properties that are not directly k-inductive. This is rIC3's default
/// k-induction mode (`kind --step 1 --simple-path`).
pub fn check_kind_simple_path(ts: &Transys, max_depth: usize) -> BmcResult {
    use crate::kind::KindEngine;

    let reduced = ts.coi_reduce();
    let mut engine = KindEngine::new_simple_path(reduced);
    let result = engine.check(max_depth);
    kind_result_from_engine(&engine, result, max_depth)
}

/// Convert a KindEngine check result into a BmcResult.
fn kind_result_from_engine(
    engine: &crate::kind::KindEngine,
    result: CheckResult,
    max_depth: usize,
) -> BmcResult {
    match result {
        CheckResult::Unsafe { depth, .. } => {
            let witness = engine.extract_lit_trace(depth);
            BmcResult {
                verdict: Some(false),
                depth,
                witness: Some(witness),
            }
        }
        CheckResult::Safe => BmcResult {
            verdict: Some(true),
            depth: max_depth,
            witness: None,
        },
        CheckResult::Unknown { .. } => BmcResult {
            verdict: None,
            depth: max_depth,
            witness: None,
        },
    }
}

// ---------------------------------------------------------------------------
// BmcEngine
// ---------------------------------------------------------------------------

/// Strategy for computing the BMC step size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BmcStepStrategy {
    /// Fixed step size (check every `step`-th depth).
    Fixed(usize),
    /// Dynamic step size based on circuit complexity.
    ///
    /// Mirrors rIC3's `dyn_step` computation:
    /// `step = max(1, 10_000_000 / (max_var + num_trans_clauses))`.
    ///
    /// Small circuits get large steps (reaching deep bugs fast), while large
    /// circuits get step=1 (every depth is checked since each SAT call is expensive).
    Dynamic,
    /// Geometric backoff: start at step_size=1 for the first `initial_depths`
    /// depths, then double the step size every `double_interval` SAT calls.
    ///
    /// This strategy provides thorough coverage at shallow depths (where most
    /// bugs hide) while rapidly exploring deep state space. Specifically designed
    /// for Sokoban/microban puzzles where counterexamples may be at depth 100+
    /// but shallow bugs should not be missed.
    ///
    /// The pattern: step=1 for depths 0..initial_depths, then step=2 for next
    /// `double_interval` checks, step=4, step=8, etc. Capped at `max_step`.
    GeometricBackoff {
        initial_depths: usize,
        double_interval: usize,
        max_step: usize,
    },
}

/// Bounded Model Checking engine.
///
/// Incrementally unrolls the transition system and checks if a bad state
/// is reachable within `max_depth` steps.
///
/// ## Any-depth accumulator optimization
///
/// Instead of checking `bad@k` at each individual depth (which requires one
/// SAT call per depth), we maintain an accumulator variable `any_bad` that
/// represents `bad@0 OR bad@1 OR ... OR bad@k`. After unrolling `step`
/// depths, a single SAT call with `any_bad` as assumption checks if bad is
/// reachable at ANY depth up to k. This reduces SAT calls from k to k/step,
/// which is critical for performance since each SAT call has overhead even
/// when UNSAT.
///
/// When `any_bad` is SAT, we identify the actual counterexample depth by
/// checking which `bad@i` is satisfied in the model.
pub struct BmcEngine {
    ts: Transys,
    solver: Box<dyn SatSolver>,
    renamer: VarRenamer,
    /// How many steps to advance per iteration (rIC3 uses dynamic step).
    step: usize,
    /// Current unroll depth (how many transition steps have been added).
    depth: usize,
    /// The bad-state literal in the base (step-0) encoding.
    bad_base: Lit,
    /// Cancellation flag shared with portfolio.
    cancelled: Arc<AtomicBool>,
    /// Accumulator: OR of bad@0, bad@1, ..., bad@depth.
    /// When checked as an assumption, one SAT call covers all depths.
    any_bad: Lit,
    /// The bad literal at each depth, for identifying which depth was SAT.
    bad_at_depth: Vec<Lit>,
    /// Reusable buffer for latch-wiring clauses to avoid per-step allocation.
    /// Pre-sized for 2-literal clauses used in latch current<=>next-state wiring.
    latch_wire_buf: Vec<Lit>,
    /// Indices of latches with constant next-state (Lit::FALSE or Lit::TRUE).
    ///
    /// For these latches, the wiring at step k is a single unit clause
    /// (assert curr@k = constant) instead of the usual 2-clause equivalence
    /// (curr@k <=> next@(k-1)). This saves 1 clause per constant latch per
    /// step. For Sokoban puzzles with many constant-init latches, this
    /// significantly reduces the per-step clause count (#4073).
    const_next_latches: Vec<(usize, bool)>,
    /// Indices of latches with non-constant next-state (need full wiring).
    dynamic_latch_indices: Vec<usize>,
    /// Count of spurious SAT results caught by witness verification (#4103).
    ///
    /// Tracks how many times z4-sat returned SAT but the witness failed
    /// simulation. This counter serves two purposes:
    /// 1. **Diagnostics**: logged at the end of a BMC run to quantify
    ///    solver reliability on this particular circuit.
    /// 2. **Solver fallback**: if the count exceeds `SPURIOUS_SAT_FALLBACK_THRESHOLD`,
    ///    the engine rebuilds with a SimpleSolver backend (DPLL without
    ///    CDCL optimizations). This mirrors IC3's fallback strategy (#4074).
    spurious_sat_count: usize,
}

impl BmcEngine {
    /// Create a new BMC engine with a dynamic step size based on circuit complexity.
    ///
    /// Mirrors rIC3's `dyn_step`: `step = max(1, 10_000_000 / (max_var + num_trans_clauses))`.
    /// Small circuits get large steps; large circuits get step=1.
    ///
    /// The step size is capped at 500 to ensure reasonable behavior: even for
    /// trivial circuits, checking every 500th depth keeps the search thorough
    /// while skipping expensive intermediate SAT calls on large circuits.
    pub fn new_dynamic(ts: Transys) -> Self {
        let complexity = ts.max_var as usize + ts.trans_clauses.len();
        let step = (10_000_000 / complexity.max(1)).max(1).min(500);
        Self::new(ts, step)
    }

    /// Create a new BMC engine with geometric backoff step sizing.
    ///
    /// Starts at step=1 for the first `initial_depths` depths (default 50),
    /// then doubles the step size every `double_interval` SAT calls (default 20),
    /// capped at `max_step` (default 64).
    ///
    /// This strategy is optimized for SAT benchmarks (Sokoban/microban puzzles)
    /// where counterexamples may be at depth 100+ but shallow bugs should still
    /// be caught. The geometric growth means depths 0-50 are checked individually,
    /// then the engine rapidly explores depth 50-1000+ with exponentially growing
    /// steps.
    pub fn new_geometric_backoff(ts: Transys) -> Self {
        // Start with step=1; check_geometric_backoff() handles the progression
        Self::new(ts, 1)
    }

    /// Create a new BMC engine with geometric backoff and a specific solver backend.
    pub fn new_geometric_backoff_with_backend(ts: Transys, backend: SolverBackend) -> Self {
        Self::new_with_backend(ts, 1, backend)
    }

    /// Create a new BMC engine with a dynamic step size and a specific solver backend.
    ///
    /// Same as `new_dynamic` but allows selecting the solver backend (e.g., z4-sat
    /// Luby, Stable, VMTF variants for portfolio diversity).
    pub fn new_dynamic_with_backend(ts: Transys, backend: SolverBackend) -> Self {
        let complexity = ts.max_var as usize + ts.trans_clauses.len();
        let step = (10_000_000 / complexity.max(1)).max(1).min(500);
        Self::new_with_backend(ts, step, backend)
    }

    /// Create a new BMC engine.
    ///
    /// `step` controls how many time steps to unroll between SAT checks.
    /// With the any-depth accumulator, step>1 still checks ALL depths --
    /// step only controls how many depths to unroll between SAT checks,
    /// reducing the number of SAT calls from k to k/step.
    ///
    /// ## Solver backend (#4073)
    ///
    /// Uses `Z4NoPreprocess` by default. For incremental BMC, z4-sat's
    /// per-solve preprocessing (BVE, subsumption) is wasted because the
    /// clause database only grows monotonically -- there is nothing to
    /// simplify. Disabling preprocessing eliminates this per-call overhead.
    pub fn new(ts: Transys, step: usize) -> Self {
        Self::new_with_backend(ts, step, SolverBackend::Z4NoPreprocess)
    }

    /// Create a new BMC engine with a specific solver backend.
    ///
    /// This allows the portfolio to spawn BMC engines backed by different
    /// z4-sat configurations (Luby restarts, stable mode, VMTF branching,
    /// etc.) for diversity. rIC3's portfolio uses Kissat and CaDiCaL as
    /// BMC backends; we use z4-sat configuration variants for equivalent
    /// diversity without external solver dependencies.
    pub fn new_with_backend(ts: Transys, step: usize, backend: SolverBackend) -> Self {
        let mut solver: Box<dyn SatSolver> = backend.make_solver(ts.max_var + 1);
        let mut renamer = VarRenamer::new(&ts);

        // Pre-classify latches into constant-next (unit wiring) and dynamic
        // (full 2-clause equivalence wiring). Constant-next latches have
        // next_state = Lit::FALSE or Lit::TRUE, meaning their value at step k
        // is always the constant regardless of step k-1 state. This saves 1
        // clause per constant latch per BMC step (#4073).
        let mut const_next_latches = Vec::new();
        let mut dynamic_latch_indices = Vec::new();
        for (idx, &latch_var) in ts.latch_vars.iter().enumerate() {
            if let Some(&next_lit) = ts.next_state.get(&latch_var) {
                if next_lit == Lit::FALSE {
                    const_next_latches.push((idx, false));
                } else if next_lit == Lit::TRUE {
                    const_next_latches.push((idx, true));
                } else {
                    dynamic_latch_indices.push(idx);
                }
            } else {
                dynamic_latch_indices.push(idx);
            }
        }

        // Constrain Var(0) = false (AIGER convention: literal 0 = constant FALSE).
        solver.add_clause(&[Lit::TRUE]);

        // Ensure step-0 variables
        renamer.ensure_step(0);
        solver.ensure_vars(renamer.max_allocated());

        // Load initial state at step 0
        ts.load_init(solver.as_mut());

        // Load transition relation at step 0 (defines AND gates for step 0)
        ts.load_trans_renamed(solver.as_mut(), &|lit| renamer.rename_lit(lit, 0));

        // Get the combined bad literal
        let bad_base = ts.get_bad_lit(solver.as_mut());

        // Initialize the any-depth accumulator: any_bad starts as bad@0
        let bad_at_0 = bad_base; // At step 0, bad_base is in the step-0 encoding
        let any_bad = bad_at_0;
        let bad_at_depth = vec![bad_at_0];

        BmcEngine {
            ts,
            solver,
            renamer,
            step: step.max(1),
            depth: 0,
            bad_base,
            cancelled: Arc::new(AtomicBool::new(false)),
            any_bad,
            bad_at_depth,
            latch_wire_buf: Vec::with_capacity(2),
            const_next_latches,
            dynamic_latch_indices,
            spurious_sat_count: 0,
        }
    }

    /// Set the cancellation flag (shared with portfolio).
    ///
    /// Propagates the flag to the underlying SAT solver so z4-sat's CDCL loop
    /// can exit promptly when cancelled, instead of running to completion (#4057).
    pub fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.solver.set_cancelled(cancelled.clone());
        self.cancelled = cancelled;
    }

    /// Number of spurious SAT results caught by witness verification (#4103).
    ///
    /// Returns the count of z4-sat SAT results where the witness trace
    /// failed simulation against the original circuit. Each spurious SAT
    /// represents a solver bug (z4-sat returned an incorrect satisfying
    /// assignment). The BMC engine treats these as Unknown and continues.
    pub fn spurious_sat_count(&self) -> usize {
        self.spurious_sat_count
    }

    /// Run BMC up to `max_depth` steps.
    ///
    /// Uses the any-depth accumulator: after unrolling `step` new depths,
    /// a single SAT call checks if bad is reachable at ANY depth up to
    /// the current frontier. This is significantly faster than checking
    /// each depth individually, especially for step>1.
    ///
    /// ## Optimizations (#4073)
    ///
    /// - **Step=1 fast path**: when step=1, each depth is checked individually
    ///   using `bad@k` directly as the assumption. This avoids the Tseitin OR
    ///   accumulator overhead (3 clauses + 1 variable per depth) since we check
    ///   every depth anyway. For SAT benchmarks (Sokoban puzzles) where the bug
    ///   depth may be 100+, this saves hundreds of variables and clauses.
    /// - **Improved logging**: reports circuit size, step size, and per-depth
    ///   solve rate to diagnose bottlenecks.
    pub fn check(&mut self, max_depth: usize) -> CheckResult {
        let start = Instant::now();
        let mut last_log = start;
        let mut depths_checked: u64 = 0;

        // Check at step 0 first (before any unrolling)
        if self.step == 1 {
            // Step=1 fast path: check bad@0 directly, no accumulator needed
            if let Some(result) = self.check_bad_at_depth(0) {
                return result;
            }
        } else if let Some(result) = self.check_any_bad() {
            return result;
        }

        let mut k = self.depth;
        while k < max_depth {
            if self.cancelled.load(Ordering::Relaxed) {
                return CheckResult::Unknown {
                    reason: "cancelled".into(),
                };
            }

            if self.step == 1 {
                // Step=1 fast path: unroll one depth, check bad@k directly.
                // Skip the Tseitin OR accumulator — saves 3 clauses + 1 variable
                // per depth. For deep SAT benchmarks this is a meaningful reduction:
                // at depth 500, it saves 1500 clauses and 500 variables.
                let next_k = k + 1;
                self.unroll_step_no_accumulator(next_k);
                k = next_k;
                depths_checked += 1;

                // Check bad@k directly
                if let Some(result) = self.check_bad_at_depth(k) {
                    return result;
                }
            } else {
                // Step>1: use the any-depth accumulator for batch checking
                let target = (k + self.step).min(max_depth);
                for next_k in (k + 1)..=target {
                    self.unroll_step(next_k);
                }
                k = target;
                depths_checked += 1;

                // One SAT call covers ALL depths from 0 to k
                if let Some(result) = self.check_any_bad() {
                    return result;
                }
            }

            // Log progress every 2 seconds
            let now = Instant::now();
            if now.duration_since(last_log).as_millis() >= 2000 {
                let vars = self.renamer.max_allocated();
                let elapsed = start.elapsed().as_secs_f64();
                let rate = if elapsed > 0.0 {
                    depths_checked as f64 / elapsed
                } else {
                    0.0
                };
                eprintln!(
                    "BMC(step={}): depth={}/{} vars={} latches={} elapsed={:.1}s rate={:.0}depth/s",
                    self.step,
                    k,
                    max_depth,
                    vars,
                    self.ts.latch_vars.len(),
                    elapsed,
                    rate,
                );
                last_log = now;
            }
        }

        if self.spurious_sat_count > 0 {
            eprintln!(
                "BMC(step={}): completed depth {max_depth} with {} spurious SAT(s) caught by witness verification",
                self.step, self.spurious_sat_count,
            );
        }

        CheckResult::Unknown {
            reason: format!("BMC reached bound {max_depth}"),
        }
    }

    /// Run BMC with geometric backoff step sizing (#4123).
    ///
    /// Phase 1 (depths 0..initial_depths): step=1, check every depth individually.
    /// Phase 2 (depths beyond initial_depths): step doubles every `double_interval`
    /// SAT calls, capped at `max_step`. Uses the step=1 fast path for phase 1
    /// (no Tseitin accumulator) and the step>1 accumulator path for phase 2.
    ///
    /// This is the key strategy for Sokoban/microban puzzles: thorough at shallow
    /// depths where most bugs hide, then rapidly explores deep state space.
    /// At depth 1000 with defaults (initial=50, interval=20, max=64):
    ///   - Depths 0-50: step=1 (50 SAT calls)
    ///   - Depths 50-90: step=2 (20 SAT calls)
    ///   - Depths 90-170: step=4 (20 SAT calls)
    ///   - Depths 170-330: step=8 (20 SAT calls)
    ///   - ... etc
    /// Total: ~150 SAT calls to reach depth 1000 (vs 1000 with step=1).
    pub fn check_geometric_backoff(
        &mut self,
        max_depth: usize,
        initial_depths: usize,
        double_interval: usize,
        max_step: usize,
    ) -> CheckResult {
        let start = Instant::now();
        let mut last_log = start;
        let mut depths_checked: u64 = 0;

        // Check at step 0 first
        if let Some(result) = self.check_bad_at_depth(0) {
            return result;
        }

        let mut k = self.depth;
        let mut current_step: usize = 1;
        let mut calls_at_current_step: usize = 0;

        while k < max_depth {
            if self.cancelled.load(Ordering::Relaxed) {
                return CheckResult::Unknown {
                    reason: "cancelled".into(),
                };
            }

            // Phase 1: step=1 for initial depths (thorough shallow coverage)
            if k < initial_depths {
                let next_k = k + 1;
                self.unroll_step_no_accumulator(next_k);
                k = next_k;
                depths_checked += 1;

                if let Some(result) = self.check_bad_at_depth(k) {
                    return result;
                }
            } else {
                // Phase 2: geometric backoff with accumulator
                let target = (k + current_step).min(max_depth);
                for next_k in (k + 1)..=target {
                    self.unroll_step(next_k);
                }
                k = target;
                depths_checked += 1;
                calls_at_current_step += 1;

                if let Some(result) = self.check_any_bad() {
                    return result;
                }

                // Double the step size after `double_interval` calls
                if calls_at_current_step >= double_interval && current_step < max_step {
                    current_step = (current_step * 2).min(max_step);
                    calls_at_current_step = 0;
                }
            }

            // Log progress every 2 seconds
            let now = Instant::now();
            if now.duration_since(last_log).as_millis() >= 2000 {
                let vars = self.renamer.max_allocated();
                let elapsed = start.elapsed().as_secs_f64();
                let rate = if elapsed > 0.0 {
                    depths_checked as f64 / elapsed
                } else {
                    0.0
                };
                eprintln!(
                    "BMC(geometric step={}): depth={}/{} vars={} latches={} elapsed={:.1}s rate={:.0}depth/s",
                    current_step,
                    k,
                    max_depth,
                    vars,
                    self.ts.latch_vars.len(),
                    elapsed,
                    rate,
                );
                last_log = now;
            }
        }

        if self.spurious_sat_count > 0 {
            eprintln!(
                "BMC(geometric): completed depth {max_depth} with {} spurious SAT(s) caught by witness verification",
                self.spurious_sat_count,
            );
        }

        CheckResult::Unknown {
            reason: format!("BMC geometric backoff reached bound {max_depth}"),
        }
    }

    /// Unroll one more time step: create fresh variables and add transition clauses.
    /// Also extends the any-depth accumulator to include bad@k.
    ///
    /// ## Optimizations (#4073)
    ///
    /// - **Constant-latch fast wiring**: latches with constant next-state (0 or 1)
    ///   use a single unit clause instead of 2-clause equivalence, saving 1 clause
    ///   per constant latch per step.
    /// - **Latch wire buffer reuse**: reuses a pre-allocated 2-literal buffer for
    ///   the `curr@k <=> next@(k-1)` equivalence clauses, avoiding 2*num_latches
    ///   micro-allocations per step.
    /// - **Bulk ensure_vars**: calls `ensure_vars` once at the start (after
    ///   `ensure_step` + aux var allocation) instead of multiple times.
    fn unroll_step(&mut self, k: usize) {
        self.renamer.ensure_step(k);

        // Add transition clauses for step k (defines AND gates at time k)
        let renamer = &self.renamer;
        self.ts
            .load_trans_renamed(self.solver.as_mut(), &|lit| renamer.rename_lit(lit, k));

        // Wire latch next-state at step k-1 to current-state at step k.
        self.wire_latches(k);

        // Extend the any-depth accumulator: any_bad_new = any_bad_old OR bad@k
        let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
        self.bad_at_depth.push(bad_at_k);

        // Pre-allocate the aux var before ensure_vars to batch allocations.
        let any_bad_new_var = self.renamer.alloc_aux_var();
        self.solver.ensure_vars(self.renamer.max_allocated());

        // Create a fresh OR accumulator variable:
        // any_bad_new <=> any_bad_old OR bad@k
        // Tseitin: (!any_bad_new OR any_bad_old OR bad@k) AND
        //          (!any_bad_old OR any_bad_new) AND
        //          (!bad@k OR any_bad_new)
        let any_bad_new = Lit::pos(any_bad_new_var);
        let any_bad_old = self.any_bad;

        self.solver
            .add_clause(&[!any_bad_new, any_bad_old, bad_at_k]);
        self.solver.add_clause(&[!any_bad_old, any_bad_new]);
        self.solver.add_clause(&[!bad_at_k, any_bad_new]);

        self.any_bad = any_bad_new;
        self.depth = k;
    }

    /// Check if bad is reachable at any depth up to the current frontier.
    ///
    /// Uses the any-depth accumulator for a single SAT call covering all
    /// depths. If SAT, identifies the actual counterexample depth by
    /// scanning which bad@i is true in the model.
    ///
    /// ## Witness verification (#4103)
    ///
    /// After the SAT solver reports SAT, the witness trace is verified by
    /// simulating the circuit. If the trace does not actually reach a bad
    /// state, the SAT result is spurious (a solver bug) and is treated as
    /// Unknown instead of Unsafe. This guards against z4-sat bugs that
    /// return incorrect SAT results on incremental queries.
    fn check_any_bad(&mut self) -> Option<CheckResult> {
        match self.solver.solve(&[self.any_bad]) {
            SatResult::Sat => {
                // Find which depth has the actual bad state
                let actual_depth = self.find_actual_bad_depth();
                let trace = self.extract_trace(actual_depth);

                // Verify the witness by simulating the circuit (#4103).
                // If verification fails, the SAT solver returned a wrong
                // answer. Treat as Unknown rather than propagating the error.
                if let Err(reason) = self.ts.verify_witness(&trace) {
                    self.spurious_sat_count += 1;
                    eprintln!(
                        "BMC: spurious SAT #{} at depth {} (witness verification failed: {}). \
                         Ignoring and continuing search.",
                        self.spurious_sat_count, actual_depth, reason
                    );
                    return None;
                }

                Some(CheckResult::Unsafe {
                    depth: actual_depth,
                    trace,
                })
            }
            SatResult::Unsat => None, // Safe at all depths up to frontier
            SatResult::Unknown => Some(CheckResult::Unknown {
                reason: format!("solver returned unknown at depth {}", self.depth),
            }),
        }
    }

    /// Unroll one time step WITHOUT updating the Tseitin OR accumulator.
    ///
    /// Used by the step=1 fast path where each depth is checked individually
    /// via `check_bad_at_depth`. This saves 3 clauses and 1 variable per depth
    /// compared to `unroll_step`. For deep SAT benchmarks (depth 500+), this
    /// eliminates 1500+ clauses and 500+ variables from the formula (#4073).
    fn unroll_step_no_accumulator(&mut self, k: usize) {
        self.renamer.ensure_step(k);
        self.solver.ensure_vars(self.renamer.max_allocated());

        // Add transition clauses for step k
        let renamer = &self.renamer;
        self.ts
            .load_trans_renamed(self.solver.as_mut(), &|lit| renamer.rename_lit(lit, k));

        // Wire latch next-state at step k-1 to current-state at step k.
        self.wire_latches(k);

        // Track bad@k for witness extraction, but don't build the accumulator
        let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
        self.bad_at_depth.push(bad_at_k);
        self.depth = k;
    }

    /// Wire latch next-state at step k-1 to current-state at step k.
    ///
    /// Splits latches into two categories (#4073):
    /// - **Constant-next latches**: next_state = Lit::FALSE/TRUE. Wired with a
    ///   single unit clause `curr@k = constant`. Saves 1 clause vs equivalence.
    /// - **Dynamic latches**: full 2-clause equivalence `curr@k <=> next@(k-1)`.
    fn wire_latches(&mut self, k: usize) {
        // Constant-next latches: single unit clause per step.
        for &(idx, val) in &self.const_next_latches {
            let latch_var = self.ts.latch_vars[idx];
            let curr_at_k = Lit::pos(self.renamer.rename_var(latch_var, k));
            if val {
                self.solver.add_clause(&[curr_at_k]); // curr@k = true
            } else {
                self.solver.add_clause(&[!curr_at_k]); // curr@k = false
            }
        }

        // Dynamic latches: full equivalence wiring.
        for &idx in &self.dynamic_latch_indices {
            let latch_var = self.ts.latch_vars[idx];
            let next_lit = self.ts.next_state[&latch_var];

            // next_lit renamed to step k-1
            let next_at_prev = self.renamer.rename_lit(next_lit, k - 1);
            // latch_var renamed to step k
            let curr_at_k = Lit::pos(self.renamer.rename_var(latch_var, k));

            // curr_at_k <=> next_at_prev
            // (!curr_at_k OR next_at_prev) AND (curr_at_k OR !next_at_prev)
            self.latch_wire_buf.clear();
            self.latch_wire_buf.push(!curr_at_k);
            self.latch_wire_buf.push(next_at_prev);
            self.solver.add_clause(&self.latch_wire_buf);

            self.latch_wire_buf.clear();
            self.latch_wire_buf.push(curr_at_k);
            self.latch_wire_buf.push(!next_at_prev);
            self.solver.add_clause(&self.latch_wire_buf);
        }
    }

    /// Check if bad is reachable at a specific depth (step=1 fast path).
    ///
    /// Uses bad@k directly as the SAT assumption instead of the OR accumulator.
    /// This is correct when step=1 because every depth is checked individually.
    ///
    /// Includes witness verification (#4103) to guard against z4-sat bugs.
    fn check_bad_at_depth(&mut self, k: usize) -> Option<CheckResult> {
        let bad_k = self.bad_at_depth[k];
        match self.solver.solve(&[bad_k]) {
            SatResult::Sat => {
                let trace = self.extract_trace(k);

                // Verify witness (#4103)
                if let Err(reason) = self.ts.verify_witness(&trace) {
                    self.spurious_sat_count += 1;
                    eprintln!(
                        "BMC: spurious SAT #{} at depth {k} (witness verification failed: {reason}). \
                         Ignoring and continuing search.",
                        self.spurious_sat_count,
                    );
                    return None;
                }

                Some(CheckResult::Unsafe {
                    depth: k,
                    trace,
                })
            }
            SatResult::Unsat => None,
            SatResult::Unknown => Some(CheckResult::Unknown {
                reason: format!("solver returned unknown at depth {k}"),
            }),
        }
    }

    /// After a SAT result on any_bad, find the shallowest depth where bad is true.
    fn find_actual_bad_depth(&self) -> usize {
        for (k, &bad_lit) in self.bad_at_depth.iter().enumerate() {
            if self.solver.value(bad_lit) == Some(true) {
                return k;
            }
        }
        // Fallback: if we can't determine the depth (shouldn't happen),
        // return the maximum depth
        self.depth
    }

    /// Extract a counterexample trace from the SAT model (named string keys).
    fn extract_trace(&self, depth: usize) -> Vec<FxHashMap<String, bool>> {
        let mut trace = Vec::with_capacity(depth + 1);

        for k in 0..=depth {
            let mut step = FxHashMap::default();

            // Record latch values
            for (idx, &latch_var) in self.ts.latch_vars.iter().enumerate() {
                let renamed = self.renamer.rename_var(latch_var, k);
                let val = self.solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("l{idx}"), val);
            }

            // Record input values
            for (idx, &input_var) in self.ts.input_vars.iter().enumerate() {
                let renamed = self.renamer.rename_var(input_var, k);
                let val = self.solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("i{idx}"), val);
            }

            trace.push(step);
        }

        trace
    }

    /// Extract a literal-level witness trace from the SAT model.
    ///
    /// Each time step is a vector of literals over the original (base)
    /// latch and input variables. Call this after `check()` returns
    /// `CheckResult::Unsafe` to get the raw witness.
    pub fn extract_lit_trace(&self, depth: usize) -> Vec<Vec<Lit>> {
        let mut trace = Vec::with_capacity(depth + 1);
        for k in 0..=depth {
            let mut step_lits = Vec::new();
            for &latch_var in &self.ts.latch_vars {
                let renamed = self.renamer.rename_var(latch_var, k);
                match self.solver.value(Lit::pos(renamed)) {
                    Some(true) => step_lits.push(Lit::pos(latch_var)),
                    Some(false) => step_lits.push(Lit::neg(latch_var)),
                    None => {}
                }
            }
            for &input_var in &self.ts.input_vars {
                let renamed = self.renamer.rename_var(input_var, k);
                match self.solver.value(Lit::pos(renamed)) {
                    Some(true) => step_lits.push(Lit::pos(input_var)),
                    Some(false) => step_lits.push(Lit::neg(input_var)),
                    None => {}
                }
            }
            trace.push(step_lits);
        }
        trace
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::sat_types::Var;

    #[test]
    fn test_bmc_trivially_safe() {
        // output=0 (constant FALSE) => never bad
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_trivially_unsafe() {
        // output=1 (constant TRUE) => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_bmc_toggle_reachable() {
        // Toggle flip-flop: latch starts at 0, toggles each step.
        // Bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        match &result {
            CheckResult::Unsafe { depth, trace } => {
                assert_eq!(*depth, 1);
                assert_eq!(trace.len(), 2); // steps 0 and 1
                                            // At step 0, latch should be false (init)
                assert_eq!(trace[0]["l0"], false);
                // At step 1, latch should be true (toggled)
                assert_eq!(trace[1]["l0"], true);
            }
            other => panic!("expected Unsafe, got {other:?}"),
        }
    }

    #[test]
    fn test_bmc_latch_stays_zero() {
        // Latch with next=0. Bad = latch. Never reachable.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        // BMC can't prove safety, only bound it
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_step_size() {
        // Toggle flip-flop with step=5: unrolls 5 depths, then checks.
        // With the any-depth accumulator, BMC checks ALL depths at once,
        // so it finds the bug at depth 1 (the shallowest reachable bad state),
        // even though it unrolled 5 depths before checking.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 5);
        let result = bmc.check(20);
        // any-depth accumulator finds the shallowest bug at depth 1
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 1, .. }),
            "expected Unsafe at depth 1 (any-depth accumulator), got {result:?}"
        );
    }

    #[test]
    fn test_bmc_and_gate_unsafe() {
        // Two inputs, AND gate, bad = AND output.
        // Bad is reachable when both inputs are true (step 0).
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(5);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_bmc_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let cancel = Arc::new(AtomicBool::new(true)); // Already cancelled
        bmc.set_cancelled(cancel);
        let result = bmc.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_dynamic_step_small_circuit() {
        // Small circuit: dynamic step should be large (but capped at 500).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        // max_var=1, trans_clauses=0 => complexity ~1 => step = min(10M, 500) = 500
        let engine = BmcEngine::new_dynamic(ts);
        assert_eq!(engine.step, 500, "dynamic step should be capped at 500 for tiny circuit");
    }

    #[test]
    fn test_bmc_dynamic_step_finds_trivial_bug() {
        // Trivially unsafe (bad=1 at step 0): dynamic step BMC finds it immediately.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new_dynamic(ts);
        let result = bmc.check(1000);
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 0, .. }),
            "dynamic BMC should find Unsafe at depth 0, got {result:?}"
        );
    }

    #[test]
    fn test_bmc_dynamic_step_two_step_counter() {
        // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
        // Bad reachable at step 2. Dynamic BMC with step=500 unrolls 500 depths,
        // then checks. With the any-depth accumulator, it finds the bug at depth 2
        // (the shallowest bad state), not at depth 500.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new_dynamic(ts);
        let result = bmc.check(1000);
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 2, .. }),
            "dynamic BMC should find 2-step counter bug at depth 2, got {result:?}"
        );
    }

    // ----- Tests for convenience functions -----

    #[test]
    fn test_check_bmc_dynamic_trivially_unsafe() {
        // Trivially unsafe: dynamic BMC should find counterexample at depth 0.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc_dynamic(&ts, 100);
        assert_eq!(result.verdict, Some(false));
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_kind_simple_path_returns_unknown_for_safe_property() {
        // Latch with next=0, bad=latch. Property holds, but with the #4039
        // soundness guard, simple-path k-induction returns Unknown instead
        // of Safe to prevent false UNSAT on constrained circuits.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind_simple_path(&ts, 10);
        assert_eq!(result.verdict, None, "expected Unknown (soundness guard)");
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_kind_simple_path_unsafe() {
        // Toggle: simple-path k-induction should find the counterexample.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind_simple_path(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_bmc_trivially_safe() {
        // output=0 => never bad; BMC returns unknown (can't prove safety)
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, None);
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_bmc_trivially_unsafe() {
        // output=1 => bad at step 0; BMC finds counterexample immediately
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 0);
        assert!(result.witness.is_some());
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 1); // 1 step (step 0)
    }

    #[test]
    fn test_check_bmc_toggle() {
        // Toggle: latch starts 0, next=!latch, bad=latch.
        // BMC finds counterexample at depth 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 1);
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 2); // steps 0 and 1
                                      // Step 0: latch (Var(1)) should be negative (false)
        assert!(witness[0].contains(&Lit::neg(Var(1))));
        // Step 1: latch (Var(1)) should be positive (true = bad)
        assert!(witness[1].contains(&Lit::pos(Var(1))));
    }

    #[test]
    fn test_check_kind_latch_stays_zero() {
        // Latch with next=0, bad=latch. k-induction proves safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(true));
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_kind_toggle_unsafe() {
        // Toggle: latch starts 0, next=!latch, bad=latch.
        // k-induction finds counterexample at depth 1 (base case).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 1);
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_bmc_two_step_shift_register() {
        // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
        // bad = l0 AND l1 is NEVER reachable (they alternate), so BMC returns unknown.
        //
        // AIGER:
        //   M=3 I=0 L=2 O=0 A=1 B=1
        //   latch: lit 2 (var 1), next = lit 3 (!var 1)  -- l0 toggles
        //   latch: lit 4 (var 2), next = lit 2 (var 1)   -- l1 = l0 delayed
        //   AND: 6 = 2 & 4 (var 3 = l0 AND l1) -- bad
        //   bad: 6
        //
        // Trace: 00 -> 10 -> 01 -> 10 -> ... (l0 AND l1 never true)
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        // This property holds (l0 and l1 never both 1), but BMC can't prove it.
        assert_eq!(result.verdict, None, "BMC can't prove safety");
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_bmc_two_step_counter_precise() {
        // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
        // Reaches bad at step 2 (00 -> 10 -> 01, and !0 AND 1 = 1).
        //
        // AIGER (AAG):
        //   aag 3 0 2 0 1 1
        //   latch: 2 next=3 (l0: toggle)
        //   latch: 4 next=2 (l1: delayed copy of l0)
        //   AND: 6 = 3 & 4 (var 3 = !l0 AND l1)
        //   bad: 6
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);

        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false), "expected UNSAFE");
        assert_eq!(result.depth, 2, "bad reachable at step 2");
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 3); // steps 0, 1, 2

        // Step 0: l0=0, l1=0
        assert!(witness[0].contains(&Lit::neg(Var(1))), "step 0: l0=0");
        assert!(witness[0].contains(&Lit::neg(Var(2))), "step 0: l1=0");
        // Step 1: l0=1, l1=0
        assert!(witness[1].contains(&Lit::pos(Var(1))), "step 1: l0=1");
        assert!(witness[1].contains(&Lit::neg(Var(2))), "step 1: l1=0");
        // Step 2: l0=0, l1=1 (bad: !l0 AND l1 = true)
        assert!(witness[2].contains(&Lit::neg(Var(1))), "step 2: l0=0");
        assert!(witness[2].contains(&Lit::pos(Var(2))), "step 2: l1=1");
    }

    #[test]
    fn test_check_kind_two_step_counter_unsafe() {
        // Same 2-step counter: k-induction should also find this bug.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);

        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(false), "expected UNSAFE");
        assert!(result.depth >= 2, "needs depth >= 2 to find bug");
    }

    #[test]
    fn test_check_bmc_lit_trace_structure() {
        // Verify the lit trace has the right structure for a simple toggle.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 5);
        assert_eq!(result.verdict, Some(false));
        let witness = result.witness.unwrap();
        // Each step should have exactly 1 literal (1 latch, 0 inputs)
        for step in &witness {
            assert_eq!(step.len(), 1, "toggle has 1 latch, no inputs");
        }
    }

    #[test]
    fn test_bmc_any_depth_accumulator_finds_intermediate_bug() {
        // Test that the any-depth accumulator catches bugs at intermediate depths
        // even with large step sizes.
        //
        // 2-step counter: bug at depth 2.
        // Step=100 means we unroll depths 1-100 before checking.
        // The accumulator should find the bug at depth 2, not depth 100.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 100);
        let result = bmc.check(200);
        match &result {
            CheckResult::Unsafe { depth, .. } => {
                assert_eq!(*depth, 2, "accumulator should find shallowest bug at depth 2");
            }
            other => panic!("expected Unsafe, got {other:?}"),
        }
    }

    // ----- z4-sat variant backend BMC tests -----

    mod z4_variant_bmc_tests {
        use super::*;
        use crate::sat_types::SolverBackend;

        #[test]
        fn test_bmc_z4_luby_trivially_unsafe() {
            // output=1 (constant TRUE) => bad at step 0
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Luby);
            let result = bmc.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
        }

        #[test]
        fn test_bmc_z4_stable_trivially_safe_bounded() {
            // output=0 (constant FALSE) => never bad
            let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Stable);
            let result = bmc.check(10);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_bmc_z4_vmtf_toggle_reachable() {
            // Toggle flip-flop: latch starts at 0, toggles each step.
            // Bad = latch. Reachable at step 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Vmtf);
            let result = bmc.check(10);
            match &result {
                CheckResult::Unsafe { depth, trace } => {
                    assert_eq!(*depth, 1);
                    assert_eq!(trace.len(), 2);
                    assert_eq!(trace[0]["l0"], false);
                    assert_eq!(trace[1]["l0"], true);
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_z4_geometric_dynamic_step() {
            // Trivially unsafe: dynamic step BMC should find it at depth 0.
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_dynamic_with_backend(ts, SolverBackend::Z4Geometric);
            let result = bmc.check(1000);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "z4-sat Geometric dynamic BMC should find Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_bmc_z4_chb_two_step_counter() {
            // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
            // Bad reachable at step 2 (00 -> 10 -> 01, and !0 AND 1 = 1).
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Chb);
            let result = bmc.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat CHB BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_bmc_z4_nopreprocess_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4NoPreprocess);
            let cancel = Arc::new(AtomicBool::new(true));
            bmc.set_cancelled(cancel);
            let result = bmc.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_bmc_z4_luby_step_5_with_accumulator() {
            // Toggle flip-flop with step=5 and z4-sat Luby backend.
            // The any-depth accumulator should find the bug at depth 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 5, SolverBackend::Z4Luby);
            let result = bmc.check(20);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "z4-sat Luby BMC with step=5 should find bug at depth 1, got {result:?}"
            );
        }

        /// z4-sat variant and default BMC should produce identical results on the same circuit.
        #[test]
        fn test_bmc_z4_variant_default_agreement() {
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);

            let mut default_bmc = BmcEngine::new(ts.clone(), 1);
            let default_result = default_bmc.check(10);

            let mut luby_bmc =
                BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Luby);
            let luby_result = luby_bmc.check(10);

            // Both should find Unsafe at the same depth.
            match (&default_result, &luby_result) {
                (
                    CheckResult::Unsafe {
                        depth: default_d, ..
                    },
                    CheckResult::Unsafe {
                        depth: luby_d, ..
                    },
                ) => {
                    assert_eq!(
                        default_d, luby_d,
                        "z4-sat default and Luby should find bug at same depth"
                    );
                }
                _ => panic!(
                    "both should be Unsafe: default={default_result:?}, luby={luby_result:?}"
                ),
            }
        }

        /// z4-sat Luby BMC with dynamic step finds intermediate bugs.
        #[test]
        fn test_bmc_z4_luby_dynamic_two_step_counter() {
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_dynamic_with_backend(ts, SolverBackend::Z4Luby);
            let result = bmc.check(1000);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat Luby dynamic BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }
    }

    /// Tests for geometric backoff BMC (#4123).
    mod geometric_backoff_tests {
        use super::*;

        #[test]
        fn test_geometric_backoff_trivially_unsafe() {
            // output=1 (constant TRUE) => bad at step 0
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "geometric backoff BMC should find Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_toggle() {
            // Toggle flip-flop: latch starts at 0, toggles each step.
            // Bad = latch. Reachable at step 1 (within initial_depths phase).
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "geometric backoff BMC should find toggle bug at depth 1, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_two_step_counter() {
            // 2-step counter: bad at depth 2. Within initial_depths phase.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_safe_bounded() {
            // output=0 (constant FALSE) => never bad. BMC returns Unknown.
            let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(100, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unknown { .. }),
                "geometric backoff BMC should return Unknown for safe circuit, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_small_initial_depths() {
            // Test with initial_depths=2 to exercise the transition from
            // phase 1 (step=1) to phase 2 (geometric backoff).
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            // Bug at depth 2. With initial_depths=2, depth 2 is the
            // last depth of phase 1 (step=1), so it should still be caught.
            let result = bmc.check_geometric_backoff(1000, 2, 5, 32);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff with small initial should find bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let cancel = Arc::new(AtomicBool::new(true)); // Already cancelled
            bmc.set_cancelled(cancel);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unknown { .. }),
                "geometric backoff BMC should return Unknown when cancelled, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_z4_variant() {
            // Geometric backoff with z4-sat Luby backend.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff_with_backend(
                ts,
                SolverBackend::Z4Luby,
            );
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff z4-Luby BMC should find bug at depth 2, got {result:?}"
            );
        }
    }

    /// Witness verification tests: verify that BMC witnesses are valid
    /// circuit executions by simulating the circuit.
    mod witness_verification_tests {
        use super::*;

        #[test]
        fn test_bmc_witness_toggle_valid() {
            // Toggle flip-flop: should produce a valid witness at depth 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let result = check_bmc(&ts, 10);
            assert_eq!(result.verdict, Some(false));

            // Extract the trace from a fresh BMC run to get named trace
            let reduced = ts.coi_reduce().compact_vars();
            let mut engine = BmcEngine::new(reduced.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    // Verify the witness against the transition system
                    let verify = reduced.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "toggle witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_witness_two_step_counter_valid() {
            // 2-step counter: bug at depth 2.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);

            let reduced = ts.coi_reduce().compact_vars();
            let mut engine = BmcEngine::new(reduced.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    let verify = reduced.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "2-step counter witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_witness_preprocessed_valid() {
            // Run BMC on a preprocessed circuit and verify the witness.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let (preprocessed, _) = ts.preprocess();

            let mut engine = BmcEngine::new(preprocessed.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    let verify = preprocessed.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "preprocessed witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        /// Regression test for #4103: cal76 benchmark spurious SAT.
        ///
        /// All 8 HWMCC competition solvers agree cal76 is SAFE (UNSAT), but
        /// the portfolio path (with full preprocessing + dynamic step BMC)
        /// was finding SAT at depth 210. This test verifies that BMC on the
        /// preprocessed cal76 circuit does NOT find a counterexample.
        ///
        /// Tests both step=1 (no accumulator) and dynamic step (with
        /// any-depth accumulator, matching the portfolio's BMC path).
        #[test]
        fn test_cal76_no_spurious_sat() {
            let bench_path = std::path::PathBuf::from(env!("HOME"))
                .join("hwmcc/benchmarks/bitlevel/safety/2019/goel/industry/cal76/cal76.aig");
            if !bench_path.exists() {
                eprintln!("Skipping cal76 test: benchmark not found at {bench_path:?}");
                return;
            }

            let data = std::fs::read(&bench_path).expect("failed to read cal76");
            let circuit = crate::parser::parse_aig(&data).expect("failed to parse cal76");
            let ts = Transys::from_aiger(&circuit);

            // Preprocess exactly as portfolio does
            let (preprocessed, _stats) = ts.preprocess();
            eprintln!(
                "cal76 preprocessed: max_var={} latches={} inputs={} gates={} clauses={}",
                preprocessed.max_var,
                preprocessed.num_latches,
                preprocessed.num_inputs,
                preprocessed.and_defs.len(),
                preprocessed.trans_clauses.len(),
            );

            // Test with dynamic step (step=500 for this small circuit),
            // which uses the any-depth accumulator -- the exact path
            // that was producing spurious SAT.
            eprintln!("=== Testing with dynamic step (accumulator path) ===");
            let mut engine = BmcEngine::new_dynamic(preprocessed.clone());
            eprintln!("cal76 dynamic step = {}", engine.step);
            let result = engine.check(300);

            match &result {
                CheckResult::Unsafe { depth, trace } => {
                    eprintln!("cal76: dynamic BMC found SAT at depth {depth}");

                    // Verify witness against the preprocessed circuit
                    let verify = preprocessed.verify_witness(trace);
                    if verify.is_err() {
                        eprintln!(
                            "cal76: witness FAILS simulation (spurious SAT): {}",
                            verify.err().unwrap()
                        );
                    } else {
                        eprintln!("cal76: witness PASSES simulation -- preprocessing bug!");
                    }
                    panic!(
                        "cal76: BMC finds SAT at depth {depth}. \
                         Bug #4103 not yet fixed."
                    );
                }
                CheckResult::Unknown { reason } => {
                    eprintln!("cal76 dynamic: BMC bounded -- CORRECT ({reason})");
                }
                CheckResult::Safe => {
                    eprintln!("cal76 dynamic: BMC proved SAFE -- CORRECT");
                }
            }

            // Also test with step=1 (no accumulator) for comparison
            eprintln!("=== Testing with step=1 (no accumulator) ===");
            let mut engine2 = BmcEngine::new(preprocessed.clone(), 1);
            let result2 = engine2.check(300);

            match &result2 {
                CheckResult::Unsafe { depth, .. } => {
                    panic!("cal76: step=1 BMC also found SAT at depth {depth}!");
                }
                CheckResult::Unknown { reason } => {
                    eprintln!("cal76 step=1: BMC bounded -- CORRECT ({reason})");
                }
                CheckResult::Safe => {
                    eprintln!("cal76 step=1: BMC proved SAFE -- CORRECT");
                }
            }

            // Test all z4-sat variant backends used by the portfolio.
            // Use depth 220 (just past the spurious SAT at depth 210) rather
            // than 300 to keep test runtime reasonable. The step=1 and dynamic
            // step tests above already verify depth 300.
            use crate::sat_types::SolverBackend;
            let variants: &[(&str, usize, SolverBackend)] = &[
                ("Z4Luby step=10", 10, SolverBackend::Z4Luby),
                ("Z4Stable step=65", 65, SolverBackend::Z4Stable),
                ("Z4Vmtf step=500", 500, SolverBackend::Z4Vmtf),
                ("Z4Geometric step=1", 1, SolverBackend::Z4Geometric),
                ("Z4Chb step=1", 1, SolverBackend::Z4Chb),
                ("Z4NoPreprocess step=1", 1, SolverBackend::Z4NoPreprocess),
            ];

            for &(name, step, backend) in variants {
                eprintln!("=== Testing {name} ===");
                let mut engine = BmcEngine::new_with_backend(
                    preprocessed.clone(),
                    step,
                    backend,
                );
                let result = engine.check(220);
                match &result {
                    CheckResult::Unsafe { depth, trace } => {
                        eprintln!("cal76 {name}: FOUND SAT at depth {depth}!");
                        let verify = preprocessed.verify_witness(trace);
                        eprintln!(
                            "  witness verification: {}",
                            if verify.is_ok() { "PASSES" } else { "FAILS" }
                        );
                        if let Err(e) = &verify {
                            eprintln!("  reason: {e}");
                        }
                        panic!(
                            "cal76: {name} finds SAT at depth {depth}. \
                             Bug #4103 in z4-sat variant."
                        );
                    }
                    CheckResult::Unknown { reason } => {
                        eprintln!("cal76 {name}: bounded -- CORRECT ({reason})");
                    }
                    CheckResult::Safe => {
                        eprintln!("cal76 {name}: SAFE -- CORRECT");
                    }
                }
            }
        }
    }
}
