// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! IC3-oriented preprocessing for AIGER transition systems.
//!
//! This module implements several reduction passes:
//! - ternary constant propagation (structural constant detection)
//! - trivial AND-gate simplification by constant propagation
//! - iterative constant latch elimination
//! - structural hashing (duplicate AND gate merging)
//! - SCORR-style latch merging via init-seeded + random simulation + SAT
//! - forward reduction for equivalent combinational signals
//! - FRTS (functional reduction / transitive simplification)
//! - bounded variable elimination (BVE) for internal AND gate variables
//! - local AIG rewriting (idempotent merge, associativity absorption)
//! - AIG synthesis (iterative balance + rewrite + strash, ABC-style)
//! - variable renumbering (compact variable IDs to dense range)
//!
//! The implementation stays close to the transition-system representation used
//! by this crate: latches are explicit current-state variables, AND gates are
//! stored both structurally (`and_defs`) and as Tseitin clauses
//! (`trans_clauses`), and latch next-state functions remain as literals in
//! `next_state`.

mod balance;
mod bve;
mod constant;
mod frts;
mod renumber;
pub(crate) mod rewrite;
mod scorr;
mod simulation;
mod simulation_sat;
mod strash;
pub(crate) mod substitution;
mod synthesis;
mod ternary_prop;
mod trivial;
pub(crate) mod xor_detect;

#[cfg(test)]
mod tests;

use std::fmt;
use std::time::{Duration, Instant};

use crate::transys::Transys;

use self::bve::bounded_variable_elimination;
use self::constant::eliminate_constant_latches;
use self::frts::frts;
use self::renumber::renumber_variables;
use self::rewrite::local_rewrite;
use self::scorr::{forward_reduce, scorr};
use self::strash::structural_hash;
use self::ternary_prop::ternary_constant_propagation;
use self::trivial::trivial_simplify;
pub(crate) use self::xor_detect::analyze_circuit;

/// Default maximum number of FRTS+BVE fixpoint loop iterations.
const FRTS_BVE_MAX_ITERATIONS: usize = 10;

/// Default maximum number of SCORR outer iterations.
///
/// Increased from 1 to 100 to match rIC3's SCORR round count. Each round
/// re-runs simulation + SAT-based equivalence checking after the previous
/// round's substitutions, finding cascading latch equivalences. Early
/// termination (0 new equivalences found) makes higher round counts
/// effectively free when equivalences converge early.
const DEFAULT_SCORR_ROUNDS: usize = 100;

/// Default maximum number of AIG synthesis rounds.
const DEFAULT_SYNTHESIS_ROUNDS: usize = 4;

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
            enable_synthesis: true,
            verbose: false,
            timeout_secs: 0,
        }
    }
}

impl PreprocessConfig {
    /// Aggressive configuration for competition (HWMCC).
    ///
    /// Runs 1000 iterative SCORR rounds (vs default 100) and 8 synthesis
    /// rounds (vs default 4). Some benchmarks have deeply cascading latch
    /// equivalences that require many rounds to fully resolve. Early
    /// convergence termination (0 new equivalences → stop) makes the high
    /// round count effectively free when equivalences stabilize early.
    pub fn aggressive() -> Self {
        Self {
            scorr_rounds: 1000,
            synthesis_rounds: 8,
            ..Default::default()
        }
    }
}

/// Statistics for the full preprocessing pipeline.
#[derive(Debug, Clone, Default)]
pub(crate) struct PreprocessStats {
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
    pub synthesis_rounds: usize,
    pub synthesis_gate_reduction: usize,
    pub synthesis_depth_reduction: usize,
    pub ternary_constants: usize,
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
             frts_bve_iters={} rewrite_elim={} \
             synthesis(rounds={},gates=-{},depth=-{}) ternary={} renumber={}",
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
            self.synthesis_rounds,
            self.synthesis_gate_reduction,
            self.synthesis_depth_reduction,
            self.ternary_constants,
            self.renumber_compacted,
        )
    }
}

/// Run the full IC3 preprocessing pipeline with default configuration.
///
/// Convenience wrapper around [`preprocess_with_config`] using
/// [`PreprocessConfig::default()`]. Used by tests.
#[cfg(test)]
pub(crate) fn preprocess_full(ts: &Transys) -> (Transys, PreprocessStats) {
    preprocess_with_config(ts, &PreprocessConfig::default())
}

/// Run the full IC3 preprocessing pipeline with a given configuration.
///
/// Pipeline (matching rIC3's approach, extended with BVE, local rewriting,
/// AIG synthesis, and renumbering):
/// 0. Ternary constant propagation (fast, no SAT -- circuit structure only)
/// 1. Trivial constant propagation (AND gate folding)
/// 2. Iterative constant latch elimination
/// 3. Structural hashing (merge duplicate AND gates)
/// 4. SCORR (sequential latch equivalence via init-seeded + random simulation + SAT)
///    -- iterative: runs up to `config.scorr_rounds` times, stopping when no new
///    equivalences are found
/// 5. Forward reduction (combinational signal merging)
/// 6. FRTS + BVE fixpoint loop (iterate FRTS -> strash -> BVE until no change)
/// 7. Local AIG rewriting (idempotent merge, associativity absorption)
/// 8. AIG synthesis (iterative balance + rewrite + strash -- ABC-style)
/// 9. Final structural hashing (clean up after synthesis)
/// 10. Variable renumbering (compact variable IDs to dense range)
pub(crate) fn preprocess_with_config(
    ts: &Transys,
    config: &PreprocessConfig,
) -> (Transys, PreprocessStats) {
    let start = Instant::now();
    let deadline = if config.timeout_secs > 0 {
        Some(start + Duration::from_secs(config.timeout_secs))
    } else {
        None
    };

    // Helper macro: check deadline between phases. If exceeded, skip to
    // renumbering on `$current` and return early with partial stats.
    macro_rules! check_deadline {
        ($current:expr, $trivial:expr, $ternary_constants:expr,
         $const_eliminated:expr, $scorr_eliminated:expr, $scorr_iterations:expr,
         $frts_eliminated:expr, $bve_eliminated:expr, $frts_bve_iterations:expr,
         $rewrite_eliminated:expr) => {
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    eprintln!(
                        "  preprocess: timeout ({:.1}s) — skipping remaining phases",
                        start.elapsed().as_secs_f64()
                    );
                    let (final_ts, renumber_compacted) = renumber_variables(&$current);
                    let stats = PreprocessStats {
                        orig_latches: ts.num_latches,
                        orig_inputs: ts.num_inputs,
                        orig_gates: ts.and_defs.len(),
                        orig_trans_clauses: ts.trans_clauses.len(),
                        after_trivial_latches: $trivial.num_latches,
                        after_trivial_inputs: $trivial.num_inputs,
                        after_trivial_gates: $trivial.and_defs.len(),
                        const_eliminated_latches: $const_eliminated,
                        scorr_eliminated_latches: $scorr_eliminated,
                        scorr_iterations: $scorr_iterations,
                        frts_eliminated: $frts_eliminated,
                        bve_eliminated_vars: $bve_eliminated,
                        frts_bve_iterations: $frts_bve_iterations,
                        rewrite_eliminated: $rewrite_eliminated,
                        synthesis_rounds: 0,
                        synthesis_gate_reduction: 0,
                        synthesis_depth_reduction: 0,
                        ternary_constants: $ternary_constants,
                        renumber_compacted,
                        final_latches: final_ts.num_latches,
                        final_inputs: final_ts.num_inputs,
                        final_gates: final_ts.and_defs.len(),
                        final_trans_clauses: final_ts.trans_clauses.len(),
                    };
                    return (final_ts, stats);
                }
            }
        };
    }

    // Phase 0: Ternary constant propagation (fast, SAT-free).
    let after_ternary = ternary_constant_propagation(ts);
    let ternary_constants = ts
        .and_defs
        .len()
        .saturating_sub(after_ternary.and_defs.len());
    if config.verbose {
        eprintln!("  preprocess phase 0 (ternary): {} constants eliminated", ternary_constants);
    }

    // Phase 1: Trivial constant propagation (AND gate folding).
    let trivial = trivial_simplify(&after_ternary);
    if config.verbose {
        eprintln!(
            "  preprocess phase 1 (trivial): latches={} inputs={} gates={}",
            trivial.num_latches,
            trivial.num_inputs,
            trivial.and_defs.len()
        );
    }

    // Phase 2: Iterative constant latch elimination.
    let (after_const, const_eliminated) = eliminate_constant_latches(&trivial);
    if config.verbose {
        eprintln!("  preprocess phase 2 (const latch): {} latches eliminated", const_eliminated);
    }

    // Phase 3: Structural hashing to merge duplicate AND gates.
    let after_strash = structural_hash(&after_const);

    check_deadline!(after_strash, trivial, ternary_constants, const_eliminated, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    // Phase 4: Iterative SCORR (sequential latch equivalence merging).
    let mut scorr_eliminated = 0usize;
    let mut scorr_iterations = 0usize;
    let mut after_scorr = if config.enable_scorr {
        let max_scorr = config.scorr_rounds.min(1000);
        let mut current = after_strash;
        for round in 0..max_scorr {
            // Check deadline before each SCORR round (SAT-heavy).
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    if config.verbose {
                        eprintln!("  preprocess phase 4 SCORR: timeout after {} rounds", round);
                    }
                    break;
                }
            }

            let latches_before = current.num_latches;
            let (after, elim) = scorr(&current);
            scorr_eliminated += elim;
            scorr_iterations += 1;

            if config.verbose {
                eprintln!(
                    "  preprocess phase 4 SCORR round {}: {} latches eliminated (latches {}->{})",
                    round,
                    elim,
                    latches_before,
                    after.num_latches
                );
            }

            current = after;

            if elim == 0 {
                break;
            }

            if elim > 0 && round + 1 < max_scorr {
                current = structural_hash(&current);
            }
        }
        current
    } else {
        after_strash
    };

    check_deadline!(after_scorr, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, 0usize, 0usize, 0usize, 0usize);

    // Phase 5: Forward reduction (combinational signal merging).
    if config.enable_scorr && after_scorr.num_latches >= 20 {
        after_scorr = forward_reduce(&after_scorr);
    }

    check_deadline!(after_scorr, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, 0usize, 0usize, 0usize, 0usize);

    // Phase 6: FRTS + BVE fixpoint loop.
    let mut current = after_scorr;
    let mut frts_eliminated = 0usize;
    let mut bve_eliminated = 0usize;
    let mut frts_bve_iterations = 0usize;
    let frts_bve_max = config.frts_bve_iterations;

    for iter in 0..frts_bve_max {
        // Check deadline before each FRTS+BVE iteration.
        if let Some(dl) = deadline {
            if Instant::now() >= dl {
                if config.verbose {
                    eprintln!("  preprocess phase 6 FRTS+BVE: timeout after {} iters", iter);
                }
                break;
            }
        }

        let gates_before = current.and_defs.len();

        let (after_frts, frts_elim) = if config.enable_frts {
            frts(&current)
        } else {
            (current, 0)
        };
        frts_eliminated += frts_elim;

        let after_strash_inner = if frts_elim > 0 {
            structural_hash(&after_frts)
        } else {
            after_frts
        };

        let (after_bve, bve_elim) = if config.enable_bve {
            bounded_variable_elimination(&after_strash_inner)
        } else {
            (after_strash_inner, 0)
        };
        bve_eliminated += bve_elim;

        current = after_bve;
        frts_bve_iterations += 1;

        if config.verbose {
            eprintln!(
                "  preprocess phase 6 FRTS+BVE iter {}: frts={} bve={} gates={}",
                iter, frts_elim, bve_elim, current.and_defs.len()
            );
        }

        let gates_after = current.and_defs.len();
        if gates_after >= gates_before {
            break;
        }
    }

    check_deadline!(current, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, frts_eliminated, bve_eliminated, frts_bve_iterations, 0usize);

    // Phase 7: Local AIG rewriting (idempotent merge, associativity absorption).
    let (after_rewrite, rewrite_eliminated) =
        if config.enable_rewrite && current.and_defs.len() >= 10 {
            local_rewrite(&current)
        } else {
            (current, 0)
        };
    if config.verbose {
        eprintln!(
            "  preprocess phase 7 (rewrite): {} gates eliminated",
            rewrite_eliminated
        );
    }

    check_deadline!(after_rewrite, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, frts_eliminated, bve_eliminated, frts_bve_iterations, rewrite_eliminated);

    // Phase 8: AIG synthesis (iterative balance + rewrite + strash).
    let pre_synth_gates = after_rewrite.and_defs.len();
    let (after_synthesis, synth_stats) = if config.enable_synthesis {
        aig_synthesis_with_rounds(&after_rewrite, config.synthesis_rounds.min(16))
    } else {
        (
            after_rewrite,
            synthesis::SynthesisStats::default(),
        )
    };
    let synthesis_gate_reduction = pre_synth_gates.saturating_sub(after_synthesis.and_defs.len());
    if config.verbose {
        eprintln!("  preprocess phase 8 (synthesis): {synth_stats}");
    }

    // Phase 9: Final structural hashing to clean up after rewrite + synthesis.
    let after_strash2 = if rewrite_eliminated > 0 || synthesis_gate_reduction > 0 {
        structural_hash(&after_synthesis)
    } else {
        after_synthesis
    };

    // Phase 10: Variable renumbering.
    let (final_ts, renumber_compacted) = renumber_variables(&after_strash2);

    let stats = PreprocessStats {
        orig_latches: ts.num_latches,
        orig_inputs: ts.num_inputs,
        orig_gates: ts.and_defs.len(),
        orig_trans_clauses: ts.trans_clauses.len(),
        after_trivial_latches: trivial.num_latches,
        after_trivial_inputs: trivial.num_inputs,
        after_trivial_gates: trivial.and_defs.len(),
        const_eliminated_latches: const_eliminated,
        scorr_eliminated_latches: scorr_eliminated,
        scorr_iterations,
        frts_eliminated,
        bve_eliminated_vars: bve_eliminated,
        frts_bve_iterations,
        rewrite_eliminated,
        synthesis_rounds: synth_stats.rounds,
        synthesis_gate_reduction,
        synthesis_depth_reduction: synth_stats.orig_depth.saturating_sub(synth_stats.final_depth),
        ternary_constants,
        renumber_compacted,
        final_latches: final_ts.num_latches,
        final_inputs: final_ts.num_inputs,
        final_gates: final_ts.and_defs.len(),
        final_trans_clauses: final_ts.trans_clauses.len(),
    };

    (final_ts, stats)
}

/// AIG synthesis with a configurable number of rounds.
///
/// Wraps [`aig_synthesis`] but allows overriding the max round count.
/// For the default (4 rounds), this delegates directly to `aig_synthesis`.
fn aig_synthesis_with_rounds(
    ts: &Transys,
    max_rounds: usize,
) -> (Transys, synthesis::SynthesisStats) {
    synthesis::aig_synthesis_configurable(ts, max_rounds)
}
