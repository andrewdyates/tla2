// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restart decisions (Luby + glucose EMA), phase saving, and trail reuse.
//!
//! Rephasing logic is in `rephase.rs`.

use super::*;

impl Solver {
    /// Update target and best phases if we've reached a new maximum trail length
    ///
    /// Target phases track the assignment at the longest conflict-free trail in the
    /// current search. Best phases track the longest trail ever seen, for use in
    /// rephasing. This is called before backtracking to capture phases at the
    /// maximum trail length.
    pub(super) fn update_target_and_best_phases(&mut self) {
        let conflict_free_len = self.no_conflict_until;
        debug_assert!(
            conflict_free_len <= self.trail.len(),
            "BUG: no_conflict_until ({conflict_free_len}) > trail.len() ({})",
            self.trail.len()
        );

        if conflict_free_len > self.target_trail_len {
            self.target_trail_len = conflict_free_len;
            // CaDiCaL phases.cpp:5-12: copy from saved phase, not current assignment.
            self.target_phase[..self.num_vars].copy_from_slice(&self.phase[..self.num_vars]);
        }

        if conflict_free_len > self.best_trail_len {
            self.best_trail_len = conflict_free_len;
            self.best_phase[..self.num_vars].copy_from_slice(&self.phase[..self.num_vars]);
        }
    }

    /// Compute the i-th element of the Luby sequence: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
    ///
    /// The Luby sequence is defined as:
    /// - luby(i) = 2^(k-1) if i = 2^k - 1
    /// - luby(i) = luby(i - 2^(k-1) + 1) if 2^(k-1) <= i < 2^k - 1
    ///
    /// This provides a universal restart strategy that adapts to different problem
    /// structures without knowing optimal restart intervals in advance.
    pub(super) fn get_luby(i: u32) -> u32 {
        if i == 0 {
            return 1; // Edge case, shouldn't happen with 1-indexed sequence
        }

        // Find k such that 2^k - 1 >= i
        // Start with k=1, p=1 (p = 2^k - 1)
        let mut k = 1u32;
        let mut p = 1u32;

        while p < i {
            k += 1;
            // Guard against overflow: 1u32 << 32 is undefined.
            // For k >= 32, p = u32::MAX satisfies p >= i for any u32 i.
            if k >= 32 {
                p = u32::MAX;
                break;
            }
            p = (1u32 << k) - 1;
        }

        // Now 2^(k-1) - 1 < i <= 2^k - 1
        if p == i {
            // i = 2^k - 1: return 2^(k-1)
            // k < 32 guaranteed here since p == i < u32::MAX when k < 32,
            // and p == u32::MAX when k >= 32 which only equals i if i == u32::MAX.
            if k >= 32 {
                return 1u32 << 31;
            }
            1u32 << (k - 1)
        } else {
            // i < 2^k - 1: recursively compute luby(i - (2^(k-1) - 1))
            let prev_p = if k > 32 {
                u32::MAX
            } else {
                (1u32 << (k - 1)) - 1
            };
            Self::get_luby(i - prev_p)
        }
    }

    /// Check if we should restart
    ///
    /// Uses CaDiCaL-style stabilization: alternates between focused mode (frequent
    /// Glucose restarts) and stable mode (infrequent reluctant doubling restarts).
    pub(super) fn should_restart(&mut self) -> bool {
        // EMA sanity: values must be non-negative and not NaN (NaN from
        // division-by-zero would be invisible without this check).
        debug_assert!(
            self.cold.lbd_ema_fast >= 0.0 && !self.cold.lbd_ema_fast.is_nan(),
            "BUG: lbd_ema_fast is invalid ({})",
            self.cold.lbd_ema_fast
        );
        debug_assert!(
            self.cold.lbd_ema_slow >= 0.0 && !self.cold.lbd_ema_slow.is_nan(),
            "BUG: lbd_ema_slow is invalid ({})",
            self.cold.lbd_ema_slow
        );

        // Check if we should switch stabilization modes.
        // IMPORTANT: This must run BEFORE the restart early-return guards below.
        // CaDiCaL restart.cpp:18-85 calls stabilizing() unconditionally from
        // restarting() -- it is a side-effect function that updates mode state.
        // Previously, Z4 placed this check after the restart_min_conflicts and
        // conflicts_since_restart guards, which blocked mode switching for the
        // first ~44K conflicts instead of the expected 1000. This delayed the
        // tick-increment bootstrap and made all subsequent phases enormous,
        // effectively disabling stabilization (#7905).
        // CaDiCaL restart.cpp:18-85: first phase uses conflicts, subsequent
        // phases use search ticks (propagation work) for better effort accounting.
        let mode_idx = usize::from(self.stable_mode);
        let should_switch = if self.cold.stabilize_tick_inc == 0 {
            // First phase: conflict-based (CaDiCaL !inc.stabilize path).
            let conflicts_in_phase = self.num_conflicts - self.cold.stable_mode_start_conflicts;
            conflicts_in_phase >= self.cold.stable_phase_length
        } else {
            // Subsequent phases: tick-based (CaDiCaL restart.cpp:27).
            self.search_ticks[mode_idx] > self.cold.stabilize_tick_limit
        };
        // DIMACS stable-only runs must never alternate back to focused mode.
        if should_switch && self.cold.mode_lock == cold::ModeLock::None {
            // Bootstrap tick increment from first phase's tick delta.
            // CaDiCaL restart.cpp:53-54.
            if self.cold.stabilize_tick_inc == 0 {
                let delta = self.search_ticks[mode_idx];
                self.cold.stabilize_tick_inc = delta.max(1);
            }

            // Compute next phase limit for the OTHER mode.
            // CaDiCaL restart.cpp:59-67.
            let next_mode_idx = usize::from(!self.stable_mode);
            let stabphases = self.cold.stable_phase_count + 1;
            let next_delta = self
                .cold
                .stabilize_tick_inc
                .saturating_mul(stabphases.saturating_mul(stabphases));
            let base_ticks = self.search_ticks[next_mode_idx];
            self.cold.stabilize_tick_limit = base_ticks.saturating_add(next_delta);
            // Overflow guard: ensure limit is strictly greater than current ticks.
            if self.cold.stabilize_tick_limit <= base_ticks {
                self.cold.stabilize_tick_limit = base_ticks + 1;
            }

            // Switch modes.
            self.stable_mode = !self.stable_mode;
            self.cold.stable_mode_start_conflicts = self.num_conflicts;
            self.cold.mode_switch_count += 1;
            self.sync_active_branch_heuristic();

            // Swap LBD EMA averages including bias correction state (CaDiCaL swap_averages).
            if self.cold.ema_swapped {
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast,
                    &mut self.cold.saved_lbd_ema_fast,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow,
                    &mut self.cold.saved_lbd_ema_slow,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast_biased,
                    &mut self.cold.saved_lbd_ema_fast_biased,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow_biased,
                    &mut self.cold.saved_lbd_ema_slow_biased,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast_exp,
                    &mut self.cold.saved_lbd_ema_fast_exp,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow_exp,
                    &mut self.cold.saved_lbd_ema_slow_exp,
                );
            } else {
                self.cold.saved_lbd_ema_fast = self.cold.lbd_ema_fast;
                self.cold.saved_lbd_ema_slow = self.cold.lbd_ema_slow;
                self.cold.saved_lbd_ema_fast_biased = self.cold.lbd_ema_fast_biased;
                self.cold.saved_lbd_ema_slow_biased = self.cold.lbd_ema_slow_biased;
                self.cold.saved_lbd_ema_fast_exp = self.cold.lbd_ema_fast_exp;
                self.cold.saved_lbd_ema_slow_exp = self.cold.lbd_ema_slow_exp;
                self.cold.lbd_ema_fast = 0.0;
                self.cold.lbd_ema_slow = 0.0;
                self.cold.lbd_ema_fast_biased = 0.0;
                self.cold.lbd_ema_slow_biased = 0.0;
                self.cold.lbd_ema_fast_exp = 1.0;
                self.cold.lbd_ema_slow_exp = 1.0;
                self.cold.ema_swapped = true;
            }

            if self.stable_mode {
                // Entering stable mode -- reset reluctant doubling state.
                self.cold.stable_phase_count += 1;
                self.cold.reluctant_u = 1;
                self.cold.reluctant_v = 1;
                self.cold.reluctant_countdown = RELUCTANT_INIT;
                self.cold.reluctant_ticked_at = self.num_conflicts;
            }

            // Emit diagnostic event for mode switch (#4674).
            self.emit_diagnostic_mode_switch(self.stable_mode, self.cold.stabilize_tick_limit);

            // Start a random decision burst after every mode switch (Kissat mode.c:214).
            // Diversifies the search space at mode boundaries.
            self.start_random_sequence();
        }

        // --- Restart early-return guards (run AFTER stabilization check). ---

        // Don't restart too early - need to build up EMA statistics.
        // CaDiCaL has no equivalent gate (relies on EMA bias correction), but
        // removing this in Z4 causes 2x more conflicts (#6928 experiment).
        if self.num_conflicts < self.cold.restart_min_conflicts {
            return false;
        }

        // Don't restart if we haven't had any conflicts since the last restart.
        // This prevents infinite restart loops when at level 0.
        if self.conflicts_since_restart == 0 {
            return false;
        }

        // Geometric restart schedule: next_restart = initial * factor^n.
        // Z3 uses this for QF_LRA (RS_GEOMETRIC with restart_adaptive=false).
        // Bypasses stabilization and glucose/Luby logic entirely.
        if self.cold.geometric_restarts {
            let threshold = self.cold.geometric_initial
                * self.cold.geometric_factor.powi(self.cold.restarts as i32);
            // Clamp to u64::MAX to prevent overflow; at that point restarts are
            // effectively disabled which is fine for extremely long runs.
            let threshold_u64 = if threshold >= u64::MAX as f64 {
                u64::MAX
            } else {
                threshold as u64
            };
            return self.conflicts_since_restart >= threshold_u64;
        }

        if self.stable_mode {
            // Stable mode: Knuth's reluctant doubling (Luby sequence x period).
            // Reference: CaDiCaL reluctant.hpp, Luby/Sinclair/Zuckerman 1993.
            // CaDiCaL ticks the countdown once per conflict (analyze.cpp:1271).
            // Z4 polls `should_restart()` from both the conflict path and the
            // conflict-free scheduling path, so we compute the conflict delta
            // since the last poll to match CaDiCaL's per-conflict cadence.
            let new_conflicts = self.num_conflicts - self.cold.reluctant_ticked_at;
            self.cold.reluctant_ticked_at = self.num_conflicts;
            self.cold.reluctant_countdown =
                self.cold.reluctant_countdown.saturating_sub(new_conflicts);
            if self.cold.reluctant_countdown == 0 {
                // Advance Knuth's (u, v) state: produces Luby sequence values
                if (self.cold.reluctant_u & self.cold.reluctant_u.wrapping_neg())
                    == self.cold.reluctant_v
                {
                    self.cold.reluctant_u += 1;
                    self.cold.reluctant_v = 1;
                } else {
                    self.cold.reluctant_v *= 2;
                }
                // Cap v to prevent unbounded interval growth (CaDiCaL reluctantmax)
                if self.cold.reluctant_v >= RELUCTANT_MAX {
                    self.cold.reluctant_u = 1;
                    self.cold.reluctant_v = 1;
                }
                self.cold.reluctant_countdown = self.cold.reluctant_v * RELUCTANT_INIT;
                self.stats.stable_reluctant_fires += 1;
                true
            } else {
                false
            }
        } else if self.cold.glucose_restarts {
            // Glucose-style EMA restarts (focused mode only — stable mode uses
            // reluctant doubling above). CaDiCaL restart.cpp:104.
            let margin = RESTART_MARGIN_FOCUSED;
            self.stats.focused_ema_checks += 1;
            let ema_condition = self.cold.lbd_ema_fast > margin * self.cold.lbd_ema_slow;
            let conflict_gate = self.conflicts_since_restart >= RESTART_INTERVAL;
            if ema_condition && !conflict_gate {
                self.stats.focused_ema_blocked_by_conflict_gate += 1;
            }
            let fires = conflict_gate && ema_condition;
            if fires {
                // CaDiCaL does NOT implement Glucose's trail-based restart
                // blocking. Removing it to match CaDiCaL's restart behavior.
                // Trail blocking suppresses restarts that CaDiCaL would take,
                // reducing search diversification in focused mode.
                self.stats.focused_ema_fires += 1;
            }
            fires
        } else {
            // Luby restarts as fallback (focused mode)
            let threshold = self.cold.restart_base * u64::from(Self::get_luby(self.cold.luby_idx));
            self.conflicts_since_restart >= threshold
        }
    }

    /// Update LBD exponential moving averages after learning a clause.
    ///
    /// Uses ADAM-style bias correction (Kingma & Ba, ICLR 2015) matching
    /// CaDiCaL's `ema.cpp`. Without correction, the slow EMA starts near 0
    /// and takes ~100K conflicts to converge, causing the fast/slow ratio
    /// to be artificially high and triggering restarts every 2-3 conflicts.
    /// Correction: `value = biased / (1 - beta^n)` compensates for the
    /// zero-initialized bias.
    pub(super) fn update_lbd_ema(&mut self, lbd: u32) {
        self.stats.lbd_sum += u64::from(lbd);
        self.stats.lbd_count += 1;
        let y = f64::from(lbd);
        let alpha_fast = 1.0 - EMA_FAST_DECAY;
        let alpha_slow = 1.0 - EMA_SLOW_DECAY;

        // Update biased fast EMA
        self.cold.lbd_ema_fast_biased += alpha_fast * (y - self.cold.lbd_ema_fast_biased);
        // Update bias correction exponent: exp *= beta
        self.cold.lbd_ema_fast_exp *= EMA_FAST_DECAY;
        // Corrected value: biased / (1 - beta^n)
        let denom_fast = 1.0 - self.cold.lbd_ema_fast_exp;
        self.cold.lbd_ema_fast = if denom_fast > 0.0 {
            self.cold.lbd_ema_fast_biased / denom_fast
        } else {
            self.cold.lbd_ema_fast_biased
        };

        // Update biased slow EMA
        self.cold.lbd_ema_slow_biased += alpha_slow * (y - self.cold.lbd_ema_slow_biased);
        // Update bias correction exponent
        self.cold.lbd_ema_slow_exp *= EMA_SLOW_DECAY;
        let denom_slow = 1.0 - self.cold.lbd_ema_slow_exp;
        self.cold.lbd_ema_slow = if denom_slow > 0.0 {
            self.cold.lbd_ema_slow_biased / denom_slow
        } else {
            self.cold.lbd_ema_slow_biased
        };
    }

    /// Update trail-length EMA for restart blocking.
    ///
    /// Called once per conflict (from analyze_and_backtrack) before backtracking.
    /// Tracks the slow-moving average of trail length so that
    /// `should_block_restart_by_trail` can detect above-average trails.
    ///
    /// Reference: Audemard & Simon, "Refining Restarts Strategies for SAT and
    /// UNSAT" (CP 2012), Section 3. CaDiCaL restart.cpp:90-96.
    pub(super) fn update_trail_ema(&mut self) {
        let trail_len = self.trail.len() as f64;
        let alpha = 1.0 - TRAIL_EMA_DECAY;
        self.cold.trail_ema_slow += alpha * (trail_len - self.cold.trail_ema_slow);
        self.cold.trail_ema_count += 1;
    }

    /// Check if the current trail length justifies blocking a restart.
    ///
    /// DISABLED: CaDiCaL does not implement Glucose's trail-based restart
    /// blocking. Kept for possible future experiments.
    ///
    /// Returns true when the current trail is significantly longer than the
    /// slow-moving average, indicating the solver is making productive progress
    /// and a restart would be counterproductive.
    ///
    /// Only active in focused mode (stable mode uses reluctant doubling which
    /// already handles restart pacing). Requires warmup period for EMA accuracy.
    #[allow(dead_code)]
    fn should_block_restart_by_trail(&self) -> bool {
        if self.stable_mode {
            return false;
        }
        if self.cold.trail_ema_count < TRAIL_BLOCKING_WARMUP {
            return false;
        }
        let trail_len = self.trail.len() as f64;
        trail_len > TRAIL_BLOCKING_MARGIN * self.cold.trail_ema_slow
    }

    /// Compute the level to backtrack to when restarting, reusing trail decisions
    ///
    /// CaDiCaL's trail reuse optimization: instead of backtracking to level 0,
    /// keep decisions that would be made again anyway (those with higher VSIDS
    /// activity than the next decision variable).
    ///
    /// This saves re-making the same decisions after restart, which is especially
    /// valuable when VSIDS has stabilized.
    pub(super) fn compute_reuse_trail_level(&mut self) -> u32 {
        if self.decision_level == 0 {
            return 0;
        }

        // Find what the next decision variable would be, matching the current mode:
        // - Stable mode: VSIDS heap
        // - Focused mode: VMTF queue
        let Some(next_decision) = self.pick_next_decision_variable() else {
            return self.decision_level; // All assigned, keep everything
        };

        // Find the lowest level where we can reuse the trail
        let mut reuse_level = 0u32;

        for level in 1..=self.decision_level {
            let decision_idx = self.trail_lim[level as usize - 1];
            let decision_lit = self.trail[decision_idx];
            let decision_var = decision_lit.variable();

            if self.branch_priority_is_lower(
                decision_var,
                next_decision,
                self.active_branch_heuristic,
            ) {
                break;
            }
            reuse_level = level;
        }

        // Postcondition: reuse_level must not exceed current decision_level.
        debug_assert!(
            reuse_level <= self.decision_level,
            "BUG: reuse_level ({reuse_level}) > decision_level ({})",
            self.decision_level
        );
        reuse_level
    }

    /// Restart with trail reuse: keep decisions with higher VSIDS activity.
    pub(super) fn do_restart(&mut self) {
        self.trace_restart();
        self.emit_diagnostic_restart();
        let reuse_level = self.compute_reuse_trail_level();
        self.backtrack(reuse_level);
        // Stale watch entries from lazy clause deletion are handled by:
        // 1. BCP inline compaction (propagation.rs:357-364) — on-demand
        // 2. flush_watches() before inprocessing (config.rs:144) — batch
        // CaDiCaL never flushes at restart. Removing the per-restart
        // O(total_watches) sweep eliminates ~21% overhead on crn_11_99.
        self.conflicts_since_restart = 0;
        self.cold.luby_idx += 1;
        self.cold.restarts += 1;
        self.complete_branch_heuristic_epoch_if_needed();
        // CaDiCaL resets target_assigned only during rephase (rephase.cpp:373-374),
        // NOT on every restart. Resetting here was added for #7003 (6g_6color
        // timeout) but destroys target phase coherence on hard combinatorial
        // instances requiring stable search guidance (FmlaEquivChain, clique).
        // Rephase timing now matches CaDiCaL (arithmetic-increase spacing),
        // so the original workaround is no longer needed.

        // Postcondition: conflicts_since_restart must be 0 after restart.
        debug_assert_eq!(
            self.conflicts_since_restart, 0,
            "BUG: conflicts_since_restart not reset after restart"
        );
    }
}
