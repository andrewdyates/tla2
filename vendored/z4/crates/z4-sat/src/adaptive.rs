// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feature-driven inprocessing technique gating for single-thread SAT.
//!
//! After a static variant preset is applied (via [`VariantConfig::apply_to_solver`]),
//! this module adjusts the inprocessing feature profile based on instance-specific
//! features extracted from the CNF formula. This bridges the gap between the
//! portfolio solver (which uses features for multi-thread strategy selection) and
//! single-thread mode (which previously applied a static preset regardless of
//! formula structure).
//!
//! ## Threshold Rules
//!
//! The adjustments are conservative overrides — they only *disable* techniques
//! that are demonstrably harmful for a given instance class, or *enable*
//! techniques known to help. They never override the variant preset in the
//! "wrong direction" (e.g., enabling a technique that the variant intentionally
//! disabled).
//!
//! | Rule | Condition | Action | Reference |
//! |------|-----------|--------|-----------|
//! | Conditioning ratio gate | `clause_var_ratio > 100.0` | Disable conditioning | CaDiCaL `conditionmaxrat=100` |
//! | Random k-SAT symmetry | `class == Random3Sat` | Disable symmetry | No exploitable symmetry |
//! | Industrial/large reorder | `class == Industrial` or `num_vars > 50_000` | Disable reorder | Expensive on large formulas |

use crate::features::{InstanceClass, SatFeatures};
use crate::InprocessingFeatureProfile;

/// Maximum clause-to-variable ratio for conditioning to remain enabled.
///
/// CaDiCaL's `conditionmaxrat` option defaults to 100: conditioning (GBCE)
/// becomes prohibitively expensive when the formula is highly over-constrained
/// because each conditioning round scans all clauses against root-level
/// assignments.
const CONDITION_MAX_RATIO: f64 = 100.0;

/// Variable count threshold above which reorder is disabled.
///
/// Kissat's clause-weighted VMTF queue reorder is O(n log n) in the number of
/// variables. On large industrial formulas (>50K vars), the overhead exceeds
/// the benefit.
const REORDER_MAX_VARS: usize = 50_000;

/// Adjust an inprocessing feature profile based on instance features.
///
/// This function applies conservative, feature-driven overrides to the profile
/// that was initially set by a variant preset. It is intended to be called
/// after [`VariantConfig::apply_to_solver`] and before solving begins.
///
/// The function only modifies toggles where instance features provide a clear
/// signal. It returns `true` if any adjustment was made.
///
/// # Arguments
///
/// * `features` - Static syntactic features extracted from the CNF formula.
/// * `class` - Instance class derived from the features.
/// * `profile` - Mutable reference to the feature profile to adjust.
pub fn adjust_features_for_instance(
    features: &SatFeatures,
    class: &InstanceClass,
    profile: &mut InprocessingFeatureProfile,
) -> bool {
    let mut changed = false;

    // Rule 1: Conditioning ratio gate.
    // CaDiCaL conditionmaxrat=100: disable conditioning on highly over-constrained
    // formulas where the scan cost per round exceeds the benefit.
    if features.clause_var_ratio > CONDITION_MAX_RATIO && profile.condition {
        profile.condition = false;
        changed = true;
    }

    // Rule 2: Random k-SAT has no exploitable symmetry or backbone.
    // Random formulas are structurally symmetric by construction, so symmetry
    // breaking preprocessing cannot find useful symmetries to break.
    // Backbone detection is also unproductive: random formulas near the phase
    // transition rarely have backbone literals.
    if matches!(*class, InstanceClass::Random3Sat | InstanceClass::RandomKSat) {
        if profile.symmetry {
            profile.symmetry = false;
            changed = true;
        }
        if profile.backbone {
            profile.backbone = false;
            changed = true;
        }
    }

    // Rule 3: Industrial/large formulas — disable reorder.
    // Kissat-style clause-weighted VMTF reorder is O(n log n) and the constant
    // factor is high. On large industrial formulas the overhead exceeds benefit.
    // Note: reorder is not in the InprocessingFeatureProfile; the caller must
    // apply this separately via Solver::inproc_ctrl.reorder.enabled.
    // We track the signal here but cannot set it directly on the profile.
    // (Handled by `adjust_solver_for_instance` below.)

    changed
}

/// Returns whether reorder should be disabled based on instance features.
///
/// This is separated from [`adjust_features_for_instance`] because the reorder
/// toggle lives in `Solver::inproc_ctrl.reorder.enabled`, not in the
/// [`InprocessingFeatureProfile`] struct.
#[must_use]
pub fn should_disable_reorder(features: &SatFeatures, class: &InstanceClass) -> bool {
    *class == InstanceClass::Industrial || features.num_vars > REORDER_MAX_VARS
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::features::{InstanceClass, SatFeatures};
    use crate::literal::{Literal, Variable};

    /// Helper: create a positive literal for variable index `v`.
    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    /// Helper: create a negative literal for variable index `v`.
    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    /// Baseline profile with all features enabled (for testing overrides).
    fn all_enabled_profile() -> InprocessingFeatureProfile {
        InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: true,
            subsume: true,
            probe: true,
            bve: true,
            bce: true,
            condition: true,
            decompose: true,
            factor: true,
            transred: true,
            htr: true,
            gate: true,
            congruence: true,
            sweep: true,
            backbone: true,
            symmetry: true,
        }
    }

    /// Baseline profile matching dimacs default (BCE and condition off).
    fn dimacs_default_profile() -> InprocessingFeatureProfile {
        InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: true,
            subsume: true,
            probe: true,
            bve: true,
            bce: false,
            condition: false,
            decompose: true,
            factor: true,
            transred: true,
            htr: true,
            gate: true,
            congruence: true,
            sweep: true,
            backbone: true,
            symmetry: true,
        }
    }

    #[test]
    fn test_adjust_conditioning_ratio_gate_disables_above_threshold() {
        // clause_var_ratio = 200 / 1 = 200.0 > 100.0
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 200.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = all_enabled_profile();

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(!profile.condition, "conditioning should be disabled for ratio > 100");
    }

    #[test]
    fn test_adjust_conditioning_ratio_gate_keeps_below_threshold() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 50.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = all_enabled_profile();

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        // No change from conditioning gate (ratio below threshold).
        // Other rules may or may not fire depending on features.
        assert!(profile.condition, "conditioning should remain enabled for ratio < 100");
    }

    #[test]
    fn test_adjust_conditioning_already_disabled_no_change() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 200.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = dimacs_default_profile();
        // condition is already false in dimacs default

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(!profile.condition);
        // changed may or may not be true depending on other rules
    }

    #[test]
    fn test_adjust_random3sat_disables_symmetry() {
        // Build a random-3-SAT-like instance.
        let num_vars = 2000;
        let num_clauses = 8000;
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Random3Sat);

        let mut profile = all_enabled_profile();
        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(!profile.symmetry, "symmetry should be disabled for Random3Sat");
    }

    #[test]
    fn test_adjust_random3sat_symmetry_already_disabled() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 2000;
        let class = InstanceClass::Random3Sat;
        let mut profile = all_enabled_profile();
        profile.symmetry = false;

        let _changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(!profile.symmetry);
    }

    #[test]
    fn test_adjust_industrial_disables_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 100_000;
        let class = InstanceClass::Industrial;

        assert!(should_disable_reorder(&features, &class));
    }

    #[test]
    fn test_adjust_large_vars_disables_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 60_000;
        let class = InstanceClass::Structured; // not industrial, but large

        assert!(
            should_disable_reorder(&features, &class),
            "reorder should be disabled for >50K vars regardless of class"
        );
    }

    #[test]
    fn test_adjust_small_vars_keeps_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 5_000;
        let class = InstanceClass::Structured;

        assert!(
            !should_disable_reorder(&features, &class),
            "reorder should remain enabled for small structured instances"
        );
    }

    #[test]
    fn test_adjust_small_horn_does_not_enable_bce() {
        // Rule 4 (removed in #8132): BCE is NOT force-enabled on small Horn-heavy
        // formulas. The old rule caused 4x regression on battleship.
        let num_vars = 500;
        let clauses: Vec<Vec<Literal>> = (0..1000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Small);

        let mut profile = dimacs_default_profile(); // bce = false
        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(!changed);
        assert!(!profile.bce, "BCE must NOT be force-enabled (#8132 regression fix)");
    }

    #[test]
    fn test_adjust_no_change_on_typical_structured() {
        // Medium structured instance: no rule fires on dimacs default profile.
        let num_vars = 5000;
        let clauses: Vec<Vec<Literal>> = (0..10_000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Structured);

        let mut profile = dimacs_default_profile();
        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        // clause_var_ratio = 10000/5000 = 2.0 (below 100)
        // not Random3Sat
        // not Small
        // conditioning already off in dimacs default
        assert!(!changed, "no adjustments expected for typical structured instance with dimacs default");
    }
}
