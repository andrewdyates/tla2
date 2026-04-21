// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mode-dependent rephasing with CaDiCaL-style schedules.
//!
//! Stable mode uses a conservative schedule (Original/Inverted dominate) because
//! EVSIDS scores are slow-changing and benefit from coherent phase information.
//! Focused mode uses an aggressive schedule (Random/Flipping dominate) because
//! VMTF already provides aggressive diversification.
//!
//! Reference: CaDiCaL `rephase.cpp:113-399`.

use super::*;

/// Kissat NLOG3N scaling: `n * (log10(n + 9))^3`.
///
/// Used for rephase interval scheduling. Grows sub-quadratically,
/// keeping rephases more frequent than linear scaling on long runs.
///
/// Reference: Kissat `kimits.c:27-37` (`kissat_nlogpown` with exponent=3).
fn nlog3n(n: u64) -> u64 {
    if n == 0 {
        return 1;
    }
    let log = ((n + 9) as f64).log10();
    let factor = log * log * log;
    ((n as f64) * factor).max(1.0) as u64
}

impl Solver {
    /// Check if rephasing should be triggered based on conflict count.
    #[inline]
    pub(super) fn should_rephase(&self) -> bool {
        self.cold.rephase_enabled && self.num_conflicts >= self.cold.next_rephase
    }

    /// Perform rephasing: mode-dependent schedule selection.
    ///
    /// Reference: CaDiCaL `rephase.cpp:113-399`.
    pub(super) fn rephase(&mut self) {
        debug_assert_eq!(
            self.target_phase.len(),
            self.num_vars,
            "BUG: target_phase.len() ({}) != num_vars ({})",
            self.target_phase.len(),
            self.num_vars
        );
        debug_assert_eq!(
            self.best_phase.len(),
            self.num_vars,
            "BUG: best_phase.len() ({}) != num_vars ({})",
            self.best_phase.len(),
            self.num_vars
        );

        // Select strategy based on current mode with independent counters.
        // CaDiCaL: `lim.rephased[stable]++` (rephase.cpp:131).
        let is_best_rephase = if self.stable_mode {
            let count = self.cold.rephase_count_stable;
            self.cold.rephase_count_stable += 1;
            self.apply_stable_rephase_schedule(count)
        } else {
            let count = self.cold.rephase_count_focused;
            self.cold.rephase_count_focused += 1;
            self.apply_focused_rephase_schedule(count)
        };

        // Copy current saved phases to target before clearing.
        // CaDiCaL: `copy_phases(phases.target)` (rephase.cpp:373).
        for i in 0..self.num_vars {
            let p = self.phase[i];
            if p != 0 {
                self.target_phase[i] = p;
            }
        }
        self.target_trail_len = 0;

        // Reset best-phase tracking after Best rephase to allow fresh discovery.
        // CaDiCaL: `best_assigned = 0` (backtrack.cpp:55-56).
        if is_best_rephase {
            self.best_trail_len = 0;
        }

        self.cold.rephase_count += 1;
        // Kissat rephase.c:119: UPDATE_CONFLICT_LIMIT(rephase, rephased, NLOG3N, false)
        // delta = rephaseint * count * (log10(count + 9))^3
        // NLOG3N grows sub-quadratically, keeping rephases frequent on hard
        // instances requiring 100K+ conflicts (#8085).
        let count = self.cold.rephase_count;
        let delta = REPHASE_INITIAL.saturating_mul(nlog3n(count));
        self.cold.next_rephase = self.num_conflicts.saturating_add(delta);

        // Shuffle decision ordering to diversify search after rephasing.
        // CaDiCaL: `rephase.cpp:396-399`.
        if self.stable_mode {
            self.vsids.shuffle_scores(self.cold.rephase_count);
        } else {
            self.vsids.shuffle_queue(self.cold.rephase_count);
        }
    }

    /// Stable-mode rephase schedule. Returns true if this was a Best rephase.
    ///
    /// CaDiCaL stable schedule (walk enabled, `rephase.cpp:287-316`):
    ///   count=0: Original, count=1: Inverted
    ///   count>=2: (count-2) % 6 -> B, W, O, B, W, I
    fn apply_stable_rephase_schedule(&mut self, count: u64) -> bool {
        match count {
            0 => {
                self.rephase_original();
                false
            }
            1 => {
                self.rephase_inverted();
                false
            }
            _ => {
                let step = (count - 2) % 6;
                match step {
                    0 | 3 => {
                        self.rephase_best();
                        true
                    }
                    1 | 4 => {
                        self.rephase_walk();
                        false
                    }
                    2 => {
                        self.rephase_original();
                        false
                    }
                    5 => {
                        self.rephase_inverted();
                        false
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Focused-mode rephase schedule. Returns true if this was a Best rephase.
    ///
    /// CaDiCaL focused schedule (walk enabled, `rephase.cpp:339-367`):
    ///   count=0: Original
    ///   count>=1: (count-1) % 6 -> #, B, W, F, B, W
    fn apply_focused_rephase_schedule(&mut self, count: u64) -> bool {
        match count {
            0 => {
                self.rephase_original();
                false
            }
            _ => {
                let step = (count - 1) % 6;
                match step {
                    0 => {
                        self.rephase_random();
                        false
                    }
                    1 | 4 => {
                        self.rephase_best();
                        true
                    }
                    2 | 5 => {
                        self.rephase_walk();
                        false
                    }
                    3 => {
                        self.rephase_flip();
                        false
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Set all phases to true (Original).
    fn rephase_original(&mut self) {
        self.phase.fill(1);
    }

    /// Set all phases to false (Inverted).
    fn rephase_inverted(&mut self) {
        self.phase.fill(-1);
    }

    /// Copy best-ever phases into saved phases (Best).
    fn rephase_best(&mut self) {
        for i in 0..self.num_vars {
            let b = self.best_phase[i];
            if b != 0 {
                self.phase[i] = b;
            }
        }
    }

    /// Deterministic pseudo-random phase assignment (Random/#).
    fn rephase_random(&mut self) {
        let mut seed = self
            .num_conflicts
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1);
        for p in &mut self.phase {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            *p = if (seed >> 32) & 1 == 0 { 1 } else { -1 };
        }
    }

    /// Invert all current phases (Flip/F).
    fn rephase_flip(&mut self) {
        for p in &mut self.phase {
            // Negate: 1 -> -1, -1 -> 1, 0 stays 0.
            *p = -*p;
        }
    }

    /// Run ProbSAT local search to find good phases during rephasing.
    ///
    /// Writes walk-discovered phases into `self.phase[]`. Uses the same walk
    /// implementation as startup phase initialization with CaDiCaL-style effort
    /// scheduling proportional to search ticks since last walk.
    ///
    /// Reference: CaDiCaL `walk.cpp:walk()` / `walk_full_occs.cpp:walk_full_occs()`.
    fn rephase_walk(&mut self) {
        if !self.phase_init.walk_enabled {
            return;
        }

        // CaDiCaL-style effort scheduling: walk budget proportional to search
        // ticks since last walk invocation.
        let total_ticks = self.search_ticks[0] + self.search_ticks[1];
        let delta = total_ticks.saturating_sub(self.phase_init.walk_last_ticks);
        let tick_limit = crate::walk::compute_walk_effort(delta);
        self.phase_init.walk_last_ticks = total_ticks;

        let seed = self
            .num_conflicts
            .wrapping_add(self.cold.rephase_count)
            .wrapping_mul(6364136223846793005);

        crate::walk::walk(
            &self.arena,
            self.num_vars,
            &mut self.phase,
            &mut self.phase_init.walk_prev_phase,
            &mut self.phase_init.walk_stats,
            seed,
            tick_limit,
            crate::walk::WalkFilter::irredundant_only(),
        );
    }
}
