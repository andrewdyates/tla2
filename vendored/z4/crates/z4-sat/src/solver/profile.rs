// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT profile application, snapshot readback, and shared debug env overrides.

use super::*;

pub(crate) const LARGE_FORMULA_VARS: usize = 5_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SatProfileKind {
    DpllTSafe,
    Dimacs,
    DimacsProof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SatProfileInput {
    pub(crate) num_vars: usize,
    pub(crate) num_clauses: usize,
}

/// Environment-variable family used for SAT debug override plumbing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SatDebugEnv {
    /// `Z4_NO_*` env vars used by the `z4` binary.
    Z4,
    /// `Z4_SAT_DISABLE_*` env vars used by `bench_dimacs`.
    Z4Sat,
}

impl Solver {
    pub(crate) fn apply_sat_profile(&mut self, profile: SatProfileKind, input: SatProfileInput) {
        self.sat_profile_tag = match profile {
            SatProfileKind::DpllTSafe => crate::SatProfileTag::DpllTSafe,
            SatProfileKind::Dimacs => crate::SatProfileTag::Dimacs,
            SatProfileKind::DimacsProof => crate::SatProfileTag::DimacsProof,
        };
        match profile {
            SatProfileKind::DpllTSafe => {}
            SatProfileKind::Dimacs => {
                self.set_bve_enabled(true);
                self.set_congruence_enabled(true);
                self.set_subsume_enabled(true);
                if input.num_clauses <= FULL_PREPROCESS_MAX_CLAUSES {
                    self.set_full_preprocessing(true);
                }
                // CaDiCaL --sat config (config.cpp:23-27): stabilizeonly=1
                // applied unconditionally. Stable mode (EVSIDS + reluctant
                // doubling) is critical for search quality on ALL formula
                // sizes. A/B test (W22, 2026-03-22): stable-only nets +2
                // SAT-COMP benchmarks vs focused-lock.
                self.set_stable_only(true);
                // Large formulas: apply CaDiCaL --sat reduced effort immediately.
                // Small formulas: arm the runtime demotion selector (#7585 D2).
                // The selector fires after the first inprocessing phase if
                // subsumption checks/candidates > 300 (see inprocessing_schedule.rs).
                if input.num_vars > LARGE_FORMULA_VARS {
                    self.set_bve_effort_permille(10);
                    self.set_subsume_effort_permille(60);
                } else {
                    self.small_dimacs_effort_selector_armed = true;
                }
            }
            SatProfileKind::DimacsProof => {
                self.set_bve_enabled(true);
                self.set_congruence_enabled(true);
                self.set_stable_only(true);
                if input.num_vars > LARGE_FORMULA_VARS {
                    self.set_bve_effort_permille(10);
                }
            }
        }
    }

    /// Return a read-only snapshot of the active SAT profile and search policy.
    #[must_use]
    pub fn sat_profile_snapshot(&self) -> crate::SatProfileSnapshot {
        crate::SatProfileSnapshot {
            profile: self.sat_profile_tag,
            search_mode_policy: match self.mode_lock {
                ModeLock::None => crate::SearchModePolicy::Adaptive,
                ModeLock::Stable => crate::SearchModePolicy::StableOnly,
                ModeLock::Focused => crate::SearchModePolicy::FocusedOnly,
            },
            full_preprocessing: !self.preprocessing_quick_mode,
            restart_policy: if self.cold.geometric_restarts {
                crate::RestartPolicyTag::Geometric
            } else if self.cold.glucose_restarts {
                crate::RestartPolicyTag::Glucose
            } else {
                crate::RestartPolicyTag::Luby
            },
            random_seed: self.random_seed(),
            bve_effort_permille: self.bve_effort_permille,
            subsume_effort_permille: self.subsume_effort_permille,
        }
    }

    /// Apply SAT debug override env vars for the selected binary family.
    pub fn apply_sat_debug_env_overrides(&mut self, env_family: SatDebugEnv) {
        match env_family {
            SatDebugEnv::Z4 => self.apply_z4_debug_env_overrides(),
            SatDebugEnv::Z4Sat => self.apply_z4_sat_debug_env_overrides(),
        }
    }

    fn apply_z4_debug_env_overrides(&mut self) {
        if std::env::var("Z4_NO_PREPROCESS").is_ok() {
            self.set_preprocess_enabled(false);
        }
        if std::env::var("Z4_NO_BVE").is_ok() {
            self.set_bve_enabled(false);
        }
        if std::env::var("Z4_NO_PROBE").is_ok() {
            self.set_probe_enabled(false);
        }
        if std::env::var("Z4_NO_CONGRUENCE").is_ok() {
            self.set_congruence_enabled(false);
        }
        if std::env::var("Z4_NO_DECOMPOSE").is_ok() {
            self.set_decompose_enabled(false);
        }
        if std::env::var("Z4_NO_SWEEP").is_ok() {
            self.set_sweep_enabled(false);
        }
        if std::env::var("Z4_NO_CONDITION").is_ok() {
            self.set_condition_enabled(false);
        }
        if std::env::var("Z4_NO_VIVIFY").is_ok() {
            self.set_vivify_enabled(false);
        }
        if std::env::var("Z4_NO_SUBSUME").is_ok() {
            self.set_subsume_enabled(false);
        }
        if std::env::var("Z4_NO_BCE").is_ok() {
            self.set_bce_enabled(false);
        }
        if std::env::var("Z4_NO_TRANSRED").is_ok() {
            self.set_transred_enabled(false);
        }
        if std::env::var("Z4_NO_HTR").is_ok() {
            self.set_htr_enabled(false);
        }
        if std::env::var("Z4_NO_GATE").is_ok() {
            self.set_gate_enabled(false);
        }
        if std::env::var("Z4_NO_FACTOR").is_ok() {
            self.set_factor_enabled(false);
        }
        if std::env::var("Z4_NO_SHRINK").is_ok() {
            self.set_shrink_enabled(false);
        }
        if std::env::var("Z4_NO_INPROCESS").is_ok() {
            self.disable_all_inprocessing();
        }
    }

    fn apply_z4_sat_debug_env_overrides(&mut self) {
        if std::env::var("Z4_SAT_DISABLE_PREPROCESS").is_ok() {
            self.set_preprocess_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_BVE").is_ok() {
            self.set_bve_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_BCE").is_ok() {
            self.set_bce_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_SWEEP").is_ok() {
            self.set_sweep_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_PROBE").is_ok() {
            self.set_probe_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_SUBSUME").is_ok() {
            self.set_subsume_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_VIVIFY").is_ok() {
            self.set_vivify_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_HTR").is_ok() {
            self.set_htr_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_TRANSRED").is_ok() {
            self.set_transred_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_GATES").is_ok() {
            self.set_congruence_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_WALK").is_ok() {
            self.set_walk_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_WARMUP").is_ok() {
            self.set_warmup_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_FACTOR").is_ok() {
            self.set_factor_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_CONGRUENCE").is_ok() {
            self.set_congruence_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_DECOMPOSE").is_ok() {
            self.set_decompose_enabled(false);
        }
        if std::env::var("Z4_SAT_DISABLE_CONDITION").is_ok() {
            self.set_condition_enabled(false);
        }
    }
}

/// Threshold for the runtime small-DIMACS effort demotion selector (#7585).
/// Based on clean-head anchor split: battleship=78.8, stable=204.3, clique=466.3.
const SMALL_DIMACS_DEMOTION_THRESHOLD: f64 = 300.0;

/// Pure decision function for the small-DIMACS effort demotion selector.
///
/// Returns `true` if the observed subsumption cost justifies demoting
/// to CaDiCaL --sat reduced effort values.
pub(crate) fn should_demote_small_dimacs_effort(
    is_small_dimacs_armed: bool,
    already_reduced: bool,
    checks_delta: u64,
    cands_delta: u64,
) -> bool {
    if !is_small_dimacs_armed || already_reduced || cands_delta == 0 {
        return false;
    }
    let ratio = checks_delta as f64 / cands_delta as f64;
    ratio > SMALL_DIMACS_DEMOTION_THRESHOLD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demotion_selector_battleship_ratio_below_threshold() {
        // battleship: 78.8 checks/candidate — should NOT demote.
        assert!(!should_demote_small_dimacs_effort(true, false, 121, 1));
    }

    #[test]
    fn test_demotion_selector_stable_ratio_below_threshold() {
        // stable-300: 204.3 checks/candidate — should NOT demote.
        assert!(!should_demote_small_dimacs_effort(true, false, 233, 1));
    }

    #[test]
    fn test_demotion_selector_clique_ratio_above_threshold() {
        // clique: 466.3 checks/candidate — should demote.
        assert!(should_demote_small_dimacs_effort(true, false, 471, 1));
    }

    #[test]
    fn test_demotion_selector_zero_candidates_is_safe() {
        assert!(!should_demote_small_dimacs_effort(true, false, 1000, 0));
    }

    #[test]
    fn test_demotion_selector_already_reduced_does_not_fire() {
        assert!(!should_demote_small_dimacs_effort(true, true, 471, 1));
    }

    #[test]
    fn test_demotion_selector_not_armed_does_not_fire() {
        assert!(!should_demote_small_dimacs_effort(false, false, 471, 1));
    }

    #[test]
    fn test_demotion_selector_exactly_at_threshold() {
        // ratio = 300.0 exactly — should NOT demote (threshold is strictly >300).
        assert!(!should_demote_small_dimacs_effort(true, false, 300, 1));
    }

    #[test]
    fn test_demotion_selector_just_above_threshold() {
        // ratio = 301.0 — should demote.
        assert!(should_demote_small_dimacs_effort(true, false, 301, 1));
    }
}
