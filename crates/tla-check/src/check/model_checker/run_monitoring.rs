// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Resource monitoring and state space estimation for BFS model checking.
//!
//! Extracted from `run.rs` (#3610): progress reporting, memory/disk pressure
//! checks, and pre-exploration state space warnings.

use super::super::api::Progress;
use super::mc_struct::ModelChecker;
use super::LimitType;
use crate::storage::FingerprintSet;
use std::time::Instant;

/// Action requested by `maybe_report_progress` after checking memory pressure.
///
/// Part of #2751: allows the sequential transport to trigger checkpoints
/// on Warning (Phase 2) and save-then-stop on Critical (Phase 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProgressAction {
    /// No action needed — continue BFS normally.
    Continue,
    /// Resource warning threshold reached — save a checkpoint if configured.
    Checkpoint,
    /// Resource critical threshold reached — save checkpoint then stop.
    /// Carries the LimitType that triggered the stop (Part of #3282).
    StopWithCheckpoint(LimitType),
    /// Resource critical threshold reached — stop immediately (no checkpoint dir).
    /// Carries the LimitType that triggered the stop (Part of #3282).
    Stop(LimitType),
}

/// Part of #4080: Minimum interval (in states) between memory pressure checks
/// when progress reporting is disabled (progress_interval == 0). Without this,
/// disabling progress reporting also silently disables all OOM safety checks.
const MEMORY_CHECK_INTERVAL: usize = 4096;

impl ModelChecker<'_> {
    /// Estimate the total bytes consumed by in-memory stores.
    ///
    /// Part of #4080: OOM safety — internal memory accounting.
    pub(super) fn estimate_internal_memory_bytes(&self) -> usize {
        self.memory_breakdown(0).total_bytes
    }

    /// Estimate internal memory including the BFS queue at its current size.
    ///
    /// Part of #4080.
    pub(super) fn estimate_internal_memory_bytes_with_queue(&self, queue_size: usize) -> usize {
        self.memory_breakdown(queue_size).total_bytes
    }

    /// Produce a structured breakdown of internal memory usage.
    ///
    /// Part of #4080: OOM safety — structured memory accounting.
    pub(super) fn memory_breakdown(
        &self,
        queue_size: usize,
    ) -> crate::memory::MemoryBreakdown {
        let fp_bytes = FingerprintSet::stats(&*self.state_storage.seen_fps).memory_bytes;

        let seen_bytes = if self.state_storage.store_full_states {
            let num_vars = self.module.vars.len();
            let value_size = num_vars.saturating_mul(64);
            let capacity = self.state_storage.seen.capacity();
            let entry_size = 8usize.saturating_add(value_size).saturating_add(1);
            let allocated = capacity.checked_next_power_of_two().unwrap_or(capacity);
            crate::memory::apply_fragmentation_overhead(
                allocated.saturating_mul(entry_size).saturating_add(56),
            )
        } else {
            0
        };

        let depths_bytes = if self.checkpoint.dir.is_some() {
            crate::memory::estimate_hashmap_bytes::<crate::state::Fingerprint, usize>(
                self.trace.depths.capacity(),
            )
        } else {
            0
        };

        let queue_bytes =
            crate::memory::estimate_vecdeque_bytes::<(crate::state::Fingerprint, usize)>(
                queue_size,
            );

        // Part of #4080: estimate liveness cache memory (successor graph +
        // witness cache). Previously invisible to memory pressure checks.
        let liveness_bytes = {
            let succ_bytes = self.liveness_cache.successors.estimate_memory_bytes();
            let witness_cap = self.liveness_cache.successor_witnesses.capacity();
            let witness_entry_size = std::mem::size_of::<crate::state::Fingerprint>()
                .saturating_add(std::mem::size_of::<Vec<(
                    crate::state::Fingerprint,
                    crate::state::ArrayState,
                )>>())
                .saturating_add(1);
            let witness_bytes = witness_cap.saturating_mul(witness_entry_size);
            succ_bytes.saturating_add(witness_bytes)
        };

        // Part of #4080: estimate symmetry fp_cache memory.
        // Previously invisible to memory pressure checks. The cache maps
        // Fingerprint -> Fingerprint (8 + 8 bytes per entry + hashmap overhead).
        let symmetry_bytes = if !self.symmetry.fp_cache.is_empty() {
            crate::memory::estimate_hashmap_bytes::<crate::state::Fingerprint, crate::state::Fingerprint>(
                self.symmetry.fp_cache.capacity(),
            )
        } else {
            0
        };

        crate::memory::MemoryBreakdown::new(fp_bytes, seen_bytes, depths_bytes, queue_bytes, 0)
            .with_liveness(liveness_bytes)
            .with_symmetry(symmetry_bytes)
    }

    /// Emit periodic progress callbacks, capacity warnings, and memory checks.
    ///
    /// Returns a `ProgressAction` indicating what the caller should do:
    /// - `Continue`: normal operation
    /// - `Checkpoint`: save a checkpoint (memory warning threshold reached)
    /// - `StopWithCheckpoint`: save checkpoint then stop (critical threshold)
    /// - `Stop`: stop immediately (critical threshold, no checkpoint configured)
    ///
    /// Part of #2751 Phases 1-3.
    /// Part of #4080: memory checks now run every MEMORY_CHECK_INTERVAL states
    /// even when progress_interval == 0 (progress reporting disabled).
    pub(super) fn maybe_report_progress(
        &mut self,
        states_since_progress: &mut usize,
        start_time: &Instant,
        current_depth: usize,
        queue_size: usize,
    ) -> ProgressAction {
        *states_since_progress += 1;

        // Part of #4080: When progress_interval == 0, still check memory
        // pressure every MEMORY_CHECK_INTERVAL states.
        let progress_due = self.hooks.progress_interval > 0
            && *states_since_progress >= self.hooks.progress_interval;
        let memory_check_due = self.hooks.progress_interval == 0
            && *states_since_progress >= MEMORY_CHECK_INTERVAL;

        if !progress_due && !memory_check_due {
            return ProgressAction::Continue;
        }
        *states_since_progress = 0;

        if progress_due {
            if let Some(ref callback) = self.hooks.progress_callback {
                let elapsed_secs = start_time.elapsed().as_secs_f64();
                let seen_count = self.states_count();
                let states_per_sec = if elapsed_secs > 0.0 {
                    seen_count as f64 / elapsed_secs
                } else {
                    0.0
                };
                let progress = Progress {
                    states_found: seen_count,
                    current_depth,
                    queue_size,
                    transitions: self.stats.transitions,
                    elapsed_secs,
                    states_per_sec,
                    memory_usage_bytes: crate::memory::current_rss_bytes().map(|b| b as u64),
                    ..Default::default()
                };
                callback(&progress);
            }

            self.check_and_warn_capacity();

            // Part of #3850: check for tiered JIT promotions at each progress interval.
            self.check_tier_promotions();
        }

        // Part of #4080: compute memory breakdown once for reuse across checks.
        let breakdown = self.memory_breakdown(queue_size);
        let seen_count = self.states_count();

        // Part of #4080: periodic memory logging for post-mortem analysis.
        if crate::memory::periodic_memory_log_enabled() {
            crate::memory::emit_memory_log(seen_count, current_depth, &breakdown);
        }

        // Part of #4080: hard internal memory cap.
        if let Some(internal_limit) = self.exploration.internal_memory_limit {
            if breakdown.total_bytes > internal_limit {
                let has_checkpoint = self.checkpoint.dir.is_some();
                let used_mb = breakdown.total_bytes / (1024 * 1024);
                let limit_mb = internal_limit / (1024 * 1024);
                eprintln!(
                    "Error: internal memory ({used_mb} MB) exceeded hard cap ({limit_mb} MB) \
                     — stopping exploration."
                );
                eprintln!("  Breakdown: {}", breakdown.format_diagnostic());
                return if has_checkpoint {
                    ProgressAction::StopWithCheckpoint(LimitType::Memory)
                } else {
                    ProgressAction::Stop(LimitType::Memory)
                };
            }
        }

        // Part of #2751: check RSS-based memory pressure.
        if let Some(ref policy) = self.exploration.memory_policy {
            use crate::memory::MemoryPressure;
            let pressure = policy.check();
            let has_checkpoint = self.checkpoint.dir.is_some();
            if pressure == MemoryPressure::Critical {
                let rss_mb = crate::memory::current_rss_bytes()
                    .map(|b| b / (1024 * 1024))
                    .unwrap_or(0);
                let limit_mb = policy.limit_bytes() / (1024 * 1024);
                eprintln!(
                    "Error: memory usage ({rss_mb} MB) exceeded critical threshold \
                     ({limit_mb} MB) — stopping exploration."
                );
                eprintln!("  Breakdown: {}", breakdown.format_diagnostic());
                return if has_checkpoint {
                    ProgressAction::StopWithCheckpoint(LimitType::Memory)
                } else {
                    ProgressAction::Stop(LimitType::Memory)
                };
            } else if pressure == MemoryPressure::Warning {
                let rss_mb = crate::memory::current_rss_bytes()
                    .map(|b| b / (1024 * 1024))
                    .unwrap_or(0);
                let limit_mb = policy.limit_bytes() / (1024 * 1024);
                eprintln!(
                    "Warning: memory usage ({rss_mb} MB) approaching limit ({limit_mb} MB). \
                     Breakdown: {}",
                    breakdown.format_diagnostic(),
                );
                if has_checkpoint {
                    return ProgressAction::Checkpoint;
                }
            }
        }

        // Part of #3282: check disk usage against configured limit.
        if let Some(disk_limit) = self.exploration.disk_limit_bytes {
            let disk_stats = FingerprintSet::stats(&*self.state_storage.seen_fps);
            // Estimate total disk usage: disk_count * fingerprint size (8 bytes each)
            // plus overhead for page index, sorted run files, etc.
            let estimated_disk_bytes = disk_stats.disk_count.saturating_mul(8);
            let has_checkpoint = self.checkpoint.dir.is_some();
            if estimated_disk_bytes > disk_limit {
                let used = crate::resource_budget::format_bytes(estimated_disk_bytes);
                let limit = crate::resource_budget::format_bytes(disk_limit);
                eprintln!(
                    "Error: disk usage ({used}) exceeded limit ({limit}) \
                     — stopping exploration."
                );
                return if has_checkpoint {
                    ProgressAction::StopWithCheckpoint(LimitType::Disk)
                } else {
                    ProgressAction::Stop(LimitType::Disk)
                };
            }
        }
        ProgressAction::Continue
    }

    /// Part of #3282: Pre-exploration state space estimation.
    ///
    /// Extracts constraints from the Init predicate and estimates the initial
    /// state space size. If the estimate exceeds configured max_states, prints
    /// a diagnostic warning to stderr. This is best-effort — if constraint
    /// extraction fails, estimation is silently skipped.
    pub(super) fn maybe_warn_state_space_estimate(&self, init_name: &str) {
        use crate::resource_budget::estimate_init_state_space;

        // Resolve Init operator definition
        let resolved_name = self.ctx.resolve_op_name(init_name).to_string();
        let Some(def) = self.module.op_defs.get(&resolved_name) else {
            return;
        };

        // Extract constraints (same analysis used by the actual enumerator).
        // TIR program is passed as None: the estimation only needs basic constraint
        // structure, not TIR-optimized leaf evaluation.
        let branches =
            match super::extract_init_constraints(&self.ctx, &def.body, &self.module.vars, None) {
                Some(b) => b,
                None => return, // Cannot extract constraints; skip estimation
            };

        let estimate = estimate_init_state_space(&branches, &self.module.vars);

        // Log the estimate for diagnostics
        if let Some(bound) = estimate.initial_states_upper_bound {
            if bound > 10_000 {
                eprintln!(
                    "State space estimate: up to {} initial states ({} branches, {} variables)",
                    bound,
                    estimate.branch_count,
                    self.module.vars.len()
                );
                // Show per-variable breakdown for large estimates
                if bound > 100_000 {
                    for (var, domain) in &estimate.variable_domains {
                        if let Some(d) = domain {
                            if *d > 1 {
                                eprintln!("  {}: {} values", var, d);
                            }
                        } else {
                            eprintln!("  {}: unbounded", var);
                        }
                    }

                    // Part of #3282: Bottleneck identification — find the variable
                    // with the largest domain and suggest reducing it.
                    if let Some((bottleneck_var, bottleneck_size)) = estimate
                        .variable_domains
                        .iter()
                        .filter_map(|(v, d)| d.map(|size| (v.as_str(), size)))
                        .max_by_key(|&(_, size)| size)
                    {
                        if bottleneck_size > 10 {
                            eprintln!(
                                "  Bottleneck: variable '{}' has {} values. \
                                 Reducing its domain (via CONSTANT assignments) \
                                 would have the largest impact on state space size.",
                                bottleneck_var, bottleneck_size
                            );
                        }
                    }
                }
            }

            // Warn if estimate exceeds configured max_states
            if let Some(max_states) = self.exploration.max_states {
                if bound > max_states as u128 {
                    eprintln!(
                        "WARNING: Estimated initial state space ({}) exceeds --max-states limit ({})",
                        bound, max_states
                    );
                    eprintln!(
                        "  The model checker will stop after exploring {} states.",
                        max_states
                    );
                }
            }

            // Warn if estimated memory exceeds configured memory limit
            if let Some(ref policy) = self.exploration.memory_policy {
                if let Some(mem_est) = estimate.estimated_memory_bytes() {
                    let limit = policy.limit_bytes() as u128;
                    if mem_est > limit {
                        eprintln!(
                            "WARNING: Estimated memory for initial states ({:.1} GB) exceeds memory limit ({:.1} GB)",
                            mem_est as f64 / (1024.0 * 1024.0 * 1024.0),
                            limit as f64 / (1024.0 * 1024.0 * 1024.0)
                        );
                    }
                }
            }

            // Part of #3282: Warn if estimated disk exceeds configured disk limit.
            if let Some(disk_limit) = self.exploration.disk_limit_bytes {
                if let Some(mem_est) = estimate.estimated_memory_bytes() {
                    let limit = disk_limit as u128;
                    if mem_est > limit {
                        eprintln!(
                            "WARNING: Estimated disk for state storage ({:.1} GB) exceeds disk limit ({:.1} GB)",
                            mem_est as f64 / (1024.0 * 1024.0 * 1024.0),
                            limit as f64 / (1024.0 * 1024.0 * 1024.0)
                        );
                    }
                }
            }
        } else if !estimate.unbounded_vars.is_empty() {
            eprintln!(
                "State space estimate: unbounded (variables with unknown domains: {})",
                estimate.unbounded_vars.join(", ")
            );
        }
    }
}
