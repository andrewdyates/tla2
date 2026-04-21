// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing technique control registry.
//!
//! Centralizes the `(enabled, next_conflict)` scheduling state for each
//! inprocessing technique. Follows CaDiCaL's X-macro pattern
//! (`reference/cadical/src/options.hpp`) translated to Rust `macro_rules!`.
//!
//! See: designs/2026-02-13-issue-3546-inprocessing-control-registry.md

/// Per-technique scheduling control: enabled flag + next-conflict threshold.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TechniqueControl {
    pub enabled: bool,
    pub next_conflict: u64,
    /// Tracks the last interval used by `reschedule_growing` so successive
    /// calls grow from the previous value. Initialized to the base interval.
    interval_used: u64,
}

impl TechniqueControl {
    #[inline]
    pub(crate) const fn new(enabled: bool, next_conflict: u64) -> Self {
        Self {
            enabled,
            next_conflict,
            interval_used: next_conflict,
        }
    }

    /// Check if technique should fire given current conflict count.
    #[inline]
    pub(crate) fn should_fire(&self, num_conflicts: u64) -> bool {
        self.enabled && num_conflicts >= self.next_conflict
    }

    /// Schedule the next firing `interval` conflicts from `current`.
    #[inline]
    pub(crate) fn reschedule(&mut self, current: u64, interval: u64) {
        self.next_conflict = current + interval;
    }

    /// Reset the growing interval state to `base`. Called during
    /// preprocessing/incremental resets so the growth sequence restarts.
    #[inline]
    pub(crate) fn reset_interval(&mut self, base: u64) {
        self.next_conflict = base;
        self.interval_used = base;
    }

    /// Schedule with a growing interval: each call multiplies the previous
    /// interval by `growth_numer / growth_denom` (e.g., 3/2 = 1.5x),
    /// clamped to `[base_interval, max_interval]`.
    ///
    /// CaDiCaL doubles the BVE elimination bound each round (elim.cpp:971).
    /// For subsumption a gentler 1.5x avoids starving simplification while
    /// reducing the 47% overhead that dominates crn_11_99.
    #[inline]
    pub(crate) fn reschedule_growing(
        &mut self,
        current: u64,
        base_interval: u64,
        growth_numer: u64,
        growth_denom: u64,
        max_interval: u64,
    ) -> u64 {
        let grown = self.interval_used.saturating_mul(growth_numer) / growth_denom;
        let interval = grown.max(base_interval).min(max_interval);
        self.interval_used = interval;
        self.next_conflict = current + interval;
        interval
    }
}

/// Generates the `InprocessingControls` struct and a `new()` constructor
/// from a technique table. Each technique gets typed field access with
/// zero overhead (direct struct field, no HashMap).
///
/// Each technique declares two proof-compatibility flags:
/// - `proof_override`: disabled in ALL proof modes (DRAT + LRAT)
/// - `lrat_override`: disabled only in LRAT mode (works in DRAT)
///
/// This is the single point of truth for proof compatibility (#4557).
macro_rules! define_inproc_controls {
    ($(
        $name:ident: default_enabled = $enabled:expr,
                     default_interval = $interval:expr,
                     proof_override = $proof_override:expr,
                     lrat_override = $lrat_override:expr;
    )*) => {
        /// Centralized inprocessing scheduling controls.
        ///
        /// Each technique has an `enabled` flag and a `next_conflict` threshold.
        /// Replaces the flat `next_*` + `*_enabled` fields that were duplicated
        /// across `Solver::new()` and `Solver::with_proof_output()`.
        #[derive(Debug, Clone)]
        pub(crate) struct InprocessingControls {
            $( pub $name: TechniqueControl, )*
        }

        impl InprocessingControls {
            /// Create controls with default values (no proof logging).
            pub(super) fn new() -> Self {
                Self {
                    $( $name: TechniqueControl::new($enabled, $interval), )*
                }
            }

            /// Apply proof-mode overrides: disable techniques incompatible
            /// with the active proof format.
            ///
            /// - `proof_override = true`: disabled in ALL proof modes
            /// - `lrat_override = true`: disabled only when `is_lrat` is true
            pub(super) fn with_proof_overrides(mut self, is_lrat: bool) -> Self {
                $(
                    if $proof_override || ($lrat_override && is_lrat) {
                        self.$name.enabled = false;
                    }
                )*
                self
            }

        }
    };
}

// ─── Technique Table ─────────────────────────────────────────────
//
// ONE line per technique. Adding a new technique requires only adding
// a row here (plus the engine field in Solver and the run method).
//
// Intervals use the constants from mod.rs. We import them via super.

use super::{
    BACKBONE_INTERVAL, BCE_INTERVAL, CCE_INTERVAL, CONDITION_INTERVAL, FACTOR_INTERVAL,
    HTR_INTERVAL, INPROBE_INTERVAL, PROBE_INTERVAL, REORDER_INTERVAL, SUBSUME_INTERVAL,
    SWEEP_INTERVAL, TRANSRED_INTERVAL, VIVIFY_INTERVAL, VIVIFY_IRRED_INTERVAL,
};

define_inproc_controls! {
    // Unified inprocessing round timer (#4851 Wave 2).
    // CaDiCaL: inprobe() runs ALL techniques as a single pipeline on one schedule.
    // Interval grows logarithmically: 25 * INPROBE_INTERVAL * log10(phase + 9).
    inprobe:     default_enabled = true,  default_interval = INPROBE_INTERVAL,     proof_override = false, lrat_override = false;
    vivify:      default_enabled = true,  default_interval = VIVIFY_INTERVAL,      proof_override = false, lrat_override = false;
    vivify_irred: default_enabled = true, default_interval = VIVIFY_IRRED_INTERVAL, proof_override = false, lrat_override = false;
    subsume:     default_enabled = true,  default_interval = SUBSUME_INTERVAL,     proof_override = false, lrat_override = false;
    probe:       default_enabled = true,  default_interval = PROBE_INTERVAL,       proof_override = false, lrat_override = false; // #8105: backward LRAT reconstruction handles probe hints post-UNSAT
    backbone:    default_enabled = true,  default_interval = BACKBONE_INTERVAL,    proof_override = false, lrat_override = false;
    bve:         default_enabled = false, default_interval = 0,                    proof_override = false, lrat_override = false;
    bce:         default_enabled = false, default_interval = BCE_INTERVAL,         proof_override = false, lrat_override = false; // CaDiCaL block=0: OFF by default (#8080)
    condition:   default_enabled = false, default_interval = CONDITION_INTERVAL,   proof_override = false, lrat_override = false; // CaDiCaL condition=0: OFF by default (#8080). LRAT: regular delete like BCE — weaken_minus not needed (#4812)
    decompose:   default_enabled = true,  default_interval = 0,                    proof_override = false, lrat_override = false; // LRAT: constructive chain hints (#4606)
    factor:      default_enabled = true,  default_interval = FACTOR_INTERVAL,      proof_override = false, lrat_override = false; // #8105: backward LRAT reconstruction handles factor hints post-UNSAT
    transred:    default_enabled = true,  default_interval = TRANSRED_INTERVAL,    proof_override = false, lrat_override = false;
    htr:         default_enabled = true,  default_interval = HTR_INTERVAL,         proof_override = false, lrat_override = false;
    gate:        default_enabled = true,  default_interval = 0,                    proof_override = false, lrat_override = false;
    congruence:  default_enabled = true,  default_interval = 0,                    proof_override = false, lrat_override = false; // LRAT: probe-based hints (#5419)
    sweep:       default_enabled = true,  default_interval = SWEEP_INTERVAL,       proof_override = false, lrat_override = false; // #8105: backward LRAT reconstruction handles sweep hints post-UNSAT
    cce:         default_enabled = false, default_interval = CCE_INTERVAL,         proof_override = false, lrat_override = false; // Default OFF (CaDiCaL opts.cover=false). Same reconstruction as BCE.
    reorder:     default_enabled = true,  default_interval = REORDER_INTERVAL,    proof_override = false, lrat_override = false; // Kissat reorder.c: clause-weighted VMTF queue reorder. No clause modifications, proof-safe.
}

#[cfg(test)]
#[path = "inproc_control_tests.rs"]
mod tests;
