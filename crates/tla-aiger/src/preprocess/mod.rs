// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
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
mod config;
mod constant;
pub(crate) mod dag_rewrite;
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
mod ternary_sim;
mod trivial;
pub(crate) mod xor_detect;

#[cfg(test)]
mod tests;

use std::time::{Duration, Instant};

use crate::transys::Transys;

pub use self::config::PreprocessConfig;
pub use self::config::PreprocessStats;

use self::bve::bounded_variable_elimination;
use self::constant::eliminate_constant_latches;
use self::dag_rewrite::dag_rewrite;
use self::frts::frts;
use self::renumber::renumber_variables;
use self::rewrite::local_rewrite;
use self::scorr::{forward_reduce, scorr};
use self::strash::structural_hash;
use self::ternary_prop::ternary_constant_propagation;
use self::ternary_sim::sequential_ternary_simulation;
use self::trivial::trivial_simplify;
pub(crate) use self::xor_detect::analyze_circuit;

/// Run the full IC3 preprocessing pipeline with default configuration.
///
/// Convenience wrapper around [`preprocess_with_config`] using
/// [`PreprocessConfig::default()`]. Used by tests.
#[cfg(test)]
pub(crate) fn preprocess_full(ts: &Transys) -> (Transys, PreprocessStats) {
    preprocess_with_config(ts, &PreprocessConfig::default())
}

/// Structural check: does the circuit match the SAT-likely Sokoban/microban
/// pattern used by the portfolio's `is_sat_likely` heuristic?
///
/// Duplicates the structural predicate from `portfolio::factory::is_sat_likely`
/// locally so preprocessing can make pass-level decisions without pulling in
/// the portfolio module. The two predicates must stay in sync — if one moves,
/// update both. See `portfolio::factory::is_sat_likely` for the authoritative
/// reference and prior-art citations (#4247, #4259, #4149).
fn is_sat_likely_pattern(ts: &Transys) -> bool {
    if ts.num_latches == 0 {
        return false;
    }
    // Pattern 1: medium-large circuits with high I/L and some constraints.
    if ts.num_latches >= 30
        && ts.num_inputs > 2 * ts.num_latches
        && !ts.constraint_lits.is_empty()
    {
        return true;
    }
    // Pattern 2: Sokoban/microban — I==L with constraint density > 4x latches.
    if ts.num_inputs == ts.num_latches && ts.constraint_lits.len() > 4 * ts.num_latches {
        return true;
    }
    false
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
pub fn preprocess_with_config(
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
         $rewrite_eliminated:expr, $ternary_sim_eliminated:expr) => {
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
                        dag_rewrite_eliminated: 0,
                        synthesis_rounds: 0,
                        synthesis_gate_reduction: 0,
                        synthesis_depth_reduction: 0,
                        ternary_constants: $ternary_constants,
                        ternary_sim_eliminated: $ternary_sim_eliminated,
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
    // Detects AND gates that are structurally constant from circuit topology
    // alone (e.g., AND(x, !x) = 0). Does NOT use init-state values — only
    // Var(0) (the structural constant FALSE) is seeded. Init-dependent
    // constants are handled later by Phase 2 (constant latch elimination).
    let after_ternary = ternary_constant_propagation(ts);
    let ternary_constants = ts
        .and_defs
        .len()
        .saturating_sub(after_ternary.and_defs.len());
    if config.verbose {
        eprintln!("  preprocess phase 0 (ternary): {} constants eliminated", ternary_constants);
    }

    // Phase 0b: Sequential ternary simulation (multi-cycle constant detection).
    // Seeds latches with init values and simulates forward N cycles with
    // ternary logic (0/1/X). Catches constants that the structural pass
    // misses, e.g., latches stuck at 0 due to AND(self, input) feedback.
    // Reference: rIC3 ternary simulation, ABC ternary_sim.
    //
    // Wave 29 gate (#4299): for SAT-likely circuits (Sokoban/microban pattern)
    // ternary simulation yields 2-5% latch elimination at best, while the deep
    // BMC search needs every spare millisecond. Probe with a short 8-cycle
    // pass; if elimination density stays below 10% of latches, skip the full
    // multi-cycle run rather than paying its cost for a marginal return.
    let (after_ternary_sim, ternary_sim_eliminated) = if config.enable_ternary_sim {
        if is_sat_likely_pattern(&after_ternary) {
            let probe_cycles = 8usize;
            let (probe_ts, probe_elim) =
                sequential_ternary_simulation(&after_ternary, probe_cycles);
            let latch_count = after_ternary.num_latches.max(1);
            let elim_ratio = probe_elim as f64 / latch_count as f64;
            if elim_ratio < 0.10 {
                if config.verbose {
                    eprintln!(
                        "  preprocess phase 0b (ternary sim): SAT-likely early-exit \
                         after {probe_cycles}-cycle probe ({probe_elim}/{latch_count} \
                         latches eliminated, ratio {:.1}%)",
                        elim_ratio * 100.0,
                    );
                }
                (probe_ts, probe_elim)
            } else {
                // Probe was fruitful — run the full multi-cycle pass for the
                // remaining depth past the probe.
                let full_cycles = if config.ternary_sim_cycles == 0 {
                    64
                } else {
                    config.ternary_sim_cycles
                };
                let remaining = full_cycles.saturating_sub(probe_cycles);
                if remaining == 0 {
                    if config.verbose {
                        eprintln!(
                            "  preprocess phase 0b (ternary sim): {} latches eliminated (probe only)",
                            probe_elim,
                        );
                    }
                    (probe_ts, probe_elim)
                } else {
                    let (ts_after, extra_elim) =
                        sequential_ternary_simulation(&probe_ts, remaining);
                    let total = probe_elim + extra_elim;
                    if config.verbose {
                        eprintln!(
                            "  preprocess phase 0b (ternary sim): {total} latches \
                             eliminated (probe {probe_elim} + extended {extra_elim})",
                        );
                    }
                    (ts_after, total)
                }
            }
        } else {
            let (ts_after, elim) = sequential_ternary_simulation(
                &after_ternary,
                config.ternary_sim_cycles,
            );
            if config.verbose {
                eprintln!("  preprocess phase 0b (ternary sim): {} latches eliminated", elim);
            }
            (ts_after, elim)
        }
    } else {
        (after_ternary, 0)
    };

    // Phase 1: Trivial constant propagation (AND gate folding).
    let trivial = trivial_simplify(&after_ternary_sim);
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

    check_deadline!(after_strash, trivial, ternary_constants, const_eliminated, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, ternary_sim_eliminated);

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

    check_deadline!(after_scorr, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, 0usize, 0usize, 0usize, 0usize, ternary_sim_eliminated);

    // Phase 5: Forward reduction (combinational signal merging).
    if config.enable_scorr && after_scorr.num_latches >= 20 {
        after_scorr = forward_reduce(&after_scorr);
    }

    check_deadline!(after_scorr, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, 0usize, 0usize, 0usize, 0usize, ternary_sim_eliminated);

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
            frts(&current, config.frts_time_limit_ms)
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

    check_deadline!(current, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, frts_eliminated, bve_eliminated, frts_bve_iterations, 0usize, ternary_sim_eliminated);

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

    check_deadline!(after_rewrite, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, frts_eliminated, bve_eliminated, frts_bve_iterations, rewrite_eliminated, ternary_sim_eliminated);

    // Phase 7b: DAG-aware AIG rewriting with 4-input cut enumeration.
    // More powerful than local rewrite — enumerates cuts, computes truth
    // tables, and replaces with optimal implementations via NPN matching.
    let (after_dag_rewrite, dag_rewrite_eliminated) =
        if config.enable_dag_rewrite && after_rewrite.and_defs.len() >= 4 {
            dag_rewrite(&after_rewrite)
        } else {
            (after_rewrite, 0)
        };
    if config.verbose {
        eprintln!(
            "  preprocess phase 7b (DAG rewrite): {} gates eliminated",
            dag_rewrite_eliminated
        );
    }

    // Strash after DAG rewrite to clean up duplicates.
    let after_dag_strash = if dag_rewrite_eliminated > 0 {
        structural_hash(&after_dag_rewrite)
    } else {
        after_dag_rewrite
    };

    check_deadline!(after_dag_strash, trivial, ternary_constants, const_eliminated, scorr_eliminated, scorr_iterations, frts_eliminated, bve_eliminated, frts_bve_iterations, rewrite_eliminated, ternary_sim_eliminated);

    // Phase 8: AIG synthesis (iterative balance + rewrite + strash).
    let pre_synth_gates = after_dag_strash.and_defs.len();
    let (after_synthesis, synth_stats) = if config.enable_synthesis {
        aig_synthesis_with_rounds(&after_dag_strash, config.synthesis_rounds.min(16))
    } else {
        (
            after_dag_strash,
            synthesis::SynthesisStats::default(),
        )
    };
    let synthesis_gate_reduction = pre_synth_gates.saturating_sub(after_synthesis.and_defs.len());
    if config.verbose {
        eprintln!("  preprocess phase 8 (synthesis): {synth_stats}");
    }

    // Phase 9: Final structural hashing to clean up after rewrite + synthesis.
    let after_strash2 = if rewrite_eliminated > 0 || dag_rewrite_eliminated > 0 || synthesis_gate_reduction > 0 {
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
        dag_rewrite_eliminated,
        synthesis_rounds: synth_stats.rounds,
        synthesis_gate_reduction,
        synthesis_depth_reduction: synth_stats.orig_depth.saturating_sub(synth_stats.final_depth),
        ternary_constants,
        ternary_sim_eliminated,
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
