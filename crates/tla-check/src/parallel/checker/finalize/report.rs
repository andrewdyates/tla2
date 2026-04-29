// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Finalization reporting: profiling, disabled-action stats, timing, and enum-profile output.
//!
//! Pure rendering — no checker state mutation. Extracted from `finalize.rs`
//! for file size compliance (#3522).

use super::super::*;

/// Emit all finalization reports based on environment flags.
///
/// This is a structural move of the reporting block from `finalize_check`.
/// Output text, env-var gates, and format are preserved exactly.
pub(super) fn emit_finalize_reports(
    total_stats: &WorkerStats,
    num_workers: usize,
    jit_verify: bool,
) {
    // Output profiling stats when TLA2_PARALLEL_PROFILING=1.
    // Release builds need this too because the large parallel benchmarks
    // are not practical to diagnose under debug binaries.
    if parallel_profiling() {
        let peer_probe_ratio = if total_stats.peer_steal_successes > 0 {
            total_stats.peer_steal_probes as f64 / total_stats.peer_steal_successes as f64
        } else {
            0.0
        };
        eprintln!("=== Parallel Profiling Stats ===");
        eprintln!("  Workers: {}", num_workers);
        eprintln!("  Steals: {}", total_stats.steals);
        eprintln!(
            "  Injector steals: attempts={} successes={}",
            total_stats.injector_steal_attempts, total_stats.injector_steal_successes
        );
        eprintln!("  Injector pushes: {}", total_stats.injector_pushes);
        eprintln!(
            "  Peer steals: probes={} successes={} probe/success={peer_probe_ratio:.1}",
            total_stats.peer_steal_probes, total_stats.peer_steal_successes
        );
        eprintln!("  Dedup hits: {}", total_stats.dedup_hits);
        eprintln!("  Streaming preadmits: {}", total_stats.streaming_preadmits);
        eprintln!(
            "  Base fp cache rebuilds: {}",
            total_stats.base_fp_cache_rebuilds
        );
        eprintln!("  Empty polls: {}", total_stats.empty_polls);
        eprintln!(
            "  work_remaining CAS retries: {}",
            total_stats.work_remaining_cas_retries
        );
        eprintln!(
            "  active_workers transitions: +{} / -{}",
            total_stats.active_worker_activations, total_stats.active_worker_deactivations
        );
        eprintln!("  States explored: {}", total_stats.states_explored);
        eprintln!("  Transitions: {}", total_stats.transitions);
        if total_stats.transitions > 0 {
            let dedup_rate = total_stats.dedup_hits as f64 / total_stats.transitions as f64 * 100.0;
            eprintln!("  Dedup rate: {:.1}%", dedup_rate);
        }
        // Part of #3285: Aggregate intern attribution counters.
        if let Some(ic) = &total_stats.intern_counters {
            let total_hits = ic.frozen_string_hits
                + ic.frozen_token_hits
                + ic.frozen_set_hits
                + ic.frozen_int_func_hits
                + ic.overlay_string_hits
                + ic.overlay_token_hits
                + ic.overlay_set_hits
                + ic.overlay_int_func_hits;
            let total_inserts =
                ic.new_string_inserts + ic.new_set_inserts + ic.new_int_func_inserts;
            let total_ops = total_hits + total_inserts;
            eprintln!("  Intern attribution (total ops={total_ops}):");
            eprintln!(
                "    frozen:  strings={} tokens={} sets={} int_funcs={}",
                ic.frozen_string_hits,
                ic.frozen_token_hits,
                ic.frozen_set_hits,
                ic.frozen_int_func_hits
            );
            eprintln!(
                "    overlay: strings={} tokens={} sets={} int_funcs={}",
                ic.overlay_string_hits,
                ic.overlay_token_hits,
                ic.overlay_set_hits,
                ic.overlay_int_func_hits
            );
            eprintln!(
                "    new:     strings={} sets={} int_funcs={}",
                ic.new_string_inserts, ic.new_set_inserts, ic.new_int_func_inserts
            );
            if total_ops > 0 {
                let frozen_pct = (ic.frozen_string_hits
                    + ic.frozen_token_hits
                    + ic.frozen_set_hits
                    + ic.frozen_int_func_hits) as f64
                    / total_ops as f64
                    * 100.0;
                let overlay_pct = (ic.overlay_string_hits
                    + ic.overlay_token_hits
                    + ic.overlay_set_hits
                    + ic.overlay_int_func_hits) as f64
                    / total_ops as f64
                    * 100.0;
                let insert_pct = total_inserts as f64 / total_ops as f64 * 100.0;
                eprintln!(
                    "    frozen={frozen_pct:.1}% overlay={overlay_pct:.1}% new={insert_pct:.1}%"
                );
            }
        }
        // Work stealing load balance metrics.
        eprintln!("  --- Load Balance ---");
        eprintln!(
            "  Max local queue depth: {}",
            total_stats.max_local_queue_depth,
        );
        eprintln!(
            "  States generated (successors enqueued): {}",
            total_stats.states_generated,
        );
        if total_stats.idle_ns > 0 {
            eprintln!(
                "  Total idle time: {:.2}ms",
                total_stats.idle_ns as f64 / 1_000_000.0,
            );
        }
        if total_stats.steal_latency_ns > 0 {
            eprintln!(
                "  Total steal latency: {:.2}ms",
                total_stats.steal_latency_ns as f64 / 1_000_000.0,
            );
        }
        if total_stats.steals > 0 {
            let avg_steal_latency_us =
                total_stats.steal_latency_ns as f64 / total_stats.steals as f64 / 1000.0;
            eprintln!("  Avg steal latency: {avg_steal_latency_us:.1}us",);
        }
        if total_stats.states_explored > 0 && num_workers > 1 {
            // Steal ratio: fraction of states obtained via steals vs total explored.
            let steal_ratio =
                total_stats.steals as f64 / total_stats.states_explored as f64 * 100.0;
            eprintln!("  Steal ratio: {steal_ratio:.1}% of explored states came from steals",);
        }
        // Part of #3706: POR stats.
        if total_stats.por_total_states > 0 {
            eprintln!(
                "  POR: {} reductions / {} states ({:.1}%), {} actions skipped",
                total_stats.por_reductions,
                total_stats.por_total_states,
                total_stats.por_reductions as f64 / total_stats.por_total_states as f64 * 100.0,
                total_stats.por_actions_skipped,
            );
        }
        // Part of #3935: JIT dispatch breakdown when counters are non-zero.
        if total_stats.jit_hits > 0
            || total_stats.jit_misses > 0
            || total_stats.jit_fallback > 0
            || total_stats.jit_not_compiled > 0
        {
            let total_dispatches = total_stats.jit_hits + total_stats.jit_misses;
            eprintln!("  --- JIT Dispatch ---");
            eprintln!(
                "  JIT hits: {} misses: {} (total state-level dispatches: {})",
                total_stats.jit_hits, total_stats.jit_misses, total_dispatches,
            );
            eprintln!(
                "  JIT per-invariant: fallback={} not_compiled={}",
                total_stats.jit_fallback, total_stats.jit_not_compiled,
            );
            if total_dispatches > 0 {
                let hit_rate = total_stats.jit_hits as f64 / total_dispatches as f64 * 100.0;
                eprintln!("  JIT hit rate: {hit_rate:.1}%");
            }
        }
        eprintln!("================================");
    }

    // Part of #606: Output disabled action stats when TLA2_DISABLED_ACTION_STATS=1
    if crate::disabled_action_stats::enabled_for_process() {
        let snapshot = crate::disabled_action_stats::DisabledActionStatsSnapshot {
            disabled_choose_failed: total_stats.disabled_choose_failed,
            disabled_not_in_domain: total_stats.disabled_not_in_domain,
            disabled_index_out_of_bounds: total_stats.disabled_index_out_of_bounds,
            disabled_no_such_field: total_stats.disabled_no_such_field,
            disabled_division_by_zero: total_stats.disabled_division_by_zero,
            disabled_type_error: total_stats.disabled_type_error,
        };
        if let Some(rendered) = crate::disabled_action_stats::render(snapshot) {
            eprint!("{rendered}");
        }
    }

    if jit_verify {
        eprintln!(
            "[jit-verify] checked={} mismatches={}",
            total_stats.jit_verify_checked, total_stats.jit_verify_mismatches
        );
    }

    // Part of #3935: Unconditional JIT dispatch summary (matches sequential checker format).
    // Only prints when JIT was actually used (at least one dispatch counter is non-zero).
    {
        let total_jit_dispatches = total_stats.jit_hits
            + total_stats.jit_misses
            + total_stats.jit_fallback
            + total_stats.jit_not_compiled;
        if total_jit_dispatches > 0 {
            let pct = |n: usize| -> f64 {
                if total_jit_dispatches > 0 {
                    n as f64 / total_jit_dispatches as f64 * 100.0
                } else {
                    0.0
                }
            };
            eprintln!(
                "JIT: {} hit ({:.1}%), {} fallback ({:.1}%), {} not compiled ({:.1}%)",
                total_stats.jit_hits,
                pct(total_stats.jit_hits),
                total_stats.jit_fallback,
                pct(total_stats.jit_fallback),
                total_stats.jit_not_compiled,
                pct(total_stats.jit_not_compiled),
            );
        }
    }

    // Output detailed timing when TLA2_TIMING=1
    if timing_enabled() {
        let total_ns = total_stats.enum_ns
            + total_stats.contains_ns
            + total_stats.insert_ns
            + total_stats.invariant_ns
            + total_stats.materialize_ns
            + total_stats.constraints_ns;
        eprintln!("=== Timing Breakdown (all workers) ===");
        eprintln!(
            "  Enumeration:    {:>8.2}ms ({:>5.1}%)",
            total_stats.enum_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.enum_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        // Part of #3285: Enumeration sub-bucket breakdown.
        if total_stats.enum_ns > 0 {
            let enum_total = total_stats.enum_ns as f64;
            eprintln!(
                "    base_cache:   {:>8.2}ms ({:>5.1}% of Enum)",
                total_stats.enum_base_cache_ns as f64 / 1_000_000.0,
                total_stats.enum_base_cache_ns as f64 / enum_total * 100.0,
            );
            eprintln!(
                "    eval:         {:>8.2}ms ({:>5.1}% of Enum)",
                total_stats.enum_eval_ns as f64 / 1_000_000.0,
                total_stats.enum_eval_ns as f64 / enum_total * 100.0,
            );
            eprintln!(
                "    diff_fp:      {:>8.2}ms ({:>5.1}% of Enum)",
                total_stats.enum_diff_fp_ns as f64 / 1_000_000.0,
                total_stats.enum_diff_fp_ns as f64 / enum_total * 100.0,
            );
        }
        eprintln!(
            "  Contains check: {:>8.2}ms ({:>5.1}%)",
            total_stats.contains_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.contains_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        eprintln!(
            "  Insert:         {:>8.2}ms ({:>5.1}%)",
            total_stats.insert_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.insert_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        eprintln!(
            "  Invariant:      {:>8.2}ms ({:>5.1}%)",
            total_stats.invariant_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.invariant_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        eprintln!(
            "  Materialize:    {:>8.2}ms ({:>5.1}%)",
            total_stats.materialize_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.materialize_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        eprintln!(
            "  Constraints:    {:>8.2}ms ({:>5.1}%)",
            total_stats.constraints_ns as f64 / 1_000_000.0,
            if total_ns > 0 {
                total_stats.constraints_ns as f64 / total_ns as f64 * 100.0
            } else {
                0.0
            }
        );
        eprintln!("  Total measured: {:>8.2}ms", total_ns as f64 / 1_000_000.0);
        eprintln!("======================================");
    }

    // Output detailed enumeration profiling when TLA2_PROFILE_ENUM_DETAIL=1
    print_enum_profile_stats();
}
