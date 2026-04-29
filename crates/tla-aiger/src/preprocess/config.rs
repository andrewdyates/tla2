// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Configuration and statistics types for the preprocessing pipeline.

use std::fmt;

/// Default maximum number of FRTS+BVE fixpoint loop iterations.
pub(super) const FRTS_BVE_MAX_ITERATIONS: usize = 10;

/// Default maximum number of SCORR outer iterations.
///
/// Increased from 1 to 100 to match rIC3's SCORR round count. Each round
/// re-runs simulation + SAT-based equivalence checking after the previous
/// round's substitutions, finding cascading latch equivalences. Early
/// termination (0 new equivalences found) makes higher round counts
/// effectively free when equivalences converge early.
pub(super) const DEFAULT_SCORR_ROUNDS: usize = 100;

/// Default maximum number of AIG synthesis rounds.
pub(super) const DEFAULT_SYNTHESIS_ROUNDS: usize = 4;

/// Configuration for the preprocessing pipeline.
///
/// Controls which passes are enabled, how many iterations to run for
/// iterative passes (SCORR, FRTS+BVE, synthesis), and verbosity.
/// Portfolio configs can customize preprocessing per-engine.
#[derive(Debug, Clone)]
pub struct PreprocessConfig {
    /// Number of iterative SCORR rounds (default 100, max 1000).
    /// Each round re-runs simulation + SAT-based equivalence checking
    /// on the result of the previous round, finding new equivalences
    /// exposed by prior eliminations. rIC3 runs ~100 rounds; the
    /// competition preset uses 1000. Early termination (0 new
    /// equivalences in a round) makes high round counts free when
    /// equivalences converge early.
    pub scorr_rounds: usize,
    /// Maximum AIG synthesis iterations (default 4, max 16).
    pub synthesis_rounds: usize,
    /// Maximum FRTS+BVE fixpoint loop iterations (default 10).
    pub frts_bve_iterations: usize,
    /// Enable SCORR (sequential latch equivalence merging).
    pub enable_scorr: bool,
    /// Enable FRTS (functional reduction / transitive simplification).
    pub enable_frts: bool,
    /// Enable BVE (bounded variable elimination).
    pub enable_bve: bool,
    /// Enable local AIG rewriting.
    pub enable_rewrite: bool,
    /// Enable DAG-aware AIG rewriting (4-input cut enumeration + NPN matching).
    pub enable_dag_rewrite: bool,
    /// Enable AIG synthesis (balance + rewrite + strash).
    pub enable_synthesis: bool,
    /// Log per-pass stats to stderr.
    pub verbose: bool,
    /// Maximum wall-clock time for preprocessing in seconds (#4074).
    /// If exceeded between phases, skip remaining phases and return
    /// the result so far. 0 means no limit (default).
    /// This prevents preprocessing from consuming the entire timeout
    /// budget on large circuits (e.g., bakery 112 latches, 1472 ANDs).
    pub timeout_secs: u64,
    /// Maximum wall-clock time for the FRTS pass in milliseconds.
    /// 0 means use the default size-scaled budget (2-8s based on circuit size).
    /// rIC3 uses 1000s for FRTS; our default (2-8s) is conservative.
    /// The competition preset uses 30s to find more equivalences on large
    /// circuits without dominating the overall preprocessing budget.
    pub frts_time_limit_ms: u64,
    /// Enable sequential ternary simulation (multi-cycle constant detection).
    /// Simulates the circuit forward for `ternary_sim_cycles` cycles with
    /// ternary values (0/1/X) to detect latches that stabilize to a constant.
    /// More powerful than structural ternary propagation alone.
    /// Reference: rIC3 ternary simulation, ABC ternary_sim.
    pub enable_ternary_sim: bool,
    /// Number of forward simulation cycles for sequential ternary simulation.
    /// 0 means use the default (64 cycles). Typical range: 32-128.
    pub ternary_sim_cycles: usize,
}

impl Default for PreprocessConfig {
    fn default() -> Self {
        Self {
            scorr_rounds: DEFAULT_SCORR_ROUNDS,
            synthesis_rounds: DEFAULT_SYNTHESIS_ROUNDS,
            frts_bve_iterations: FRTS_BVE_MAX_ITERATIONS,
            enable_scorr: true,
            enable_frts: true,
            enable_bve: true,
            enable_rewrite: true,
            enable_dag_rewrite: true,
            enable_synthesis: true,
            verbose: false,
            timeout_secs: 0,
            frts_time_limit_ms: 0,
            enable_ternary_sim: true,
            ternary_sim_cycles: 0, // 0 = default (64 cycles)
        }
    }
}

impl PreprocessConfig {
    /// Aggressive configuration for competition (HWMCC).
    ///
    /// Runs 1000 iterative SCORR rounds (vs default 100), 8 synthesis
    /// rounds (vs default 4), and 30s FRTS time limit (vs default 2-8s).
    /// Some benchmarks have deeply cascading equivalences that require
    /// more time and rounds to fully resolve. Early convergence termination
    /// makes high round counts effectively free when equivalences converge.
    pub fn aggressive() -> Self {
        Self {
            scorr_rounds: 1000,
            synthesis_rounds: 8,
            frts_time_limit_ms: 30_000,
            ternary_sim_cycles: 128, // more cycles for deeper constant detection
            ..Default::default()
        }
    }
}

/// Statistics for the full preprocessing pipeline.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct PreprocessStats {
    pub orig_latches: usize,
    pub orig_inputs: usize,
    pub orig_gates: usize,
    pub orig_trans_clauses: usize,
    pub after_trivial_latches: usize,
    pub after_trivial_inputs: usize,
    pub after_trivial_gates: usize,
    pub const_eliminated_latches: usize,
    pub scorr_eliminated_latches: usize,
    /// Number of SCORR outer iterations actually run (stops early on fixpoint).
    pub scorr_iterations: usize,
    pub frts_eliminated: usize,
    pub bve_eliminated_vars: usize,
    pub frts_bve_iterations: usize,
    pub rewrite_eliminated: usize,
    pub dag_rewrite_eliminated: usize,
    pub synthesis_rounds: usize,
    pub synthesis_gate_reduction: usize,
    pub synthesis_depth_reduction: usize,
    pub ternary_constants: usize,
    /// Number of latches eliminated by sequential ternary simulation.
    pub ternary_sim_eliminated: usize,
    pub renumber_compacted: usize,
    pub final_latches: usize,
    pub final_inputs: usize,
    pub final_gates: usize,
    pub final_trans_clauses: usize,
}

impl fmt::Display for PreprocessStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "preprocess: latches {}->{}->{} inputs {}->{}->{} gates {}->{}->{} \
             clauses {}->{} const_elim={} scorr_elim={}(iters={}) frts_elim={} bve_elim={} \
             frts_bve_iters={} rewrite_elim={} dag_rewrite_elim={} \
             synthesis(rounds={},gates=-{},depth=-{}) ternary={} ternary_sim={} renumber={}",
            self.orig_latches,
            self.after_trivial_latches,
            self.final_latches,
            self.orig_inputs,
            self.after_trivial_inputs,
            self.final_inputs,
            self.orig_gates,
            self.after_trivial_gates,
            self.final_gates,
            self.orig_trans_clauses,
            self.final_trans_clauses,
            self.const_eliminated_latches,
            self.scorr_eliminated_latches,
            self.scorr_iterations,
            self.frts_eliminated,
            self.bve_eliminated_vars,
            self.frts_bve_iterations,
            self.rewrite_eliminated,
            self.dag_rewrite_eliminated,
            self.synthesis_rounds,
            self.synthesis_gate_reduction,
            self.synthesis_depth_reduction,
            self.ternary_constants,
            self.ternary_sim_eliminated,
            self.renumber_compacted,
        )
    }
}
