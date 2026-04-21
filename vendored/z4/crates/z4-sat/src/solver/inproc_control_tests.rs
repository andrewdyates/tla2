// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_default_controls_match_current_behavior() {
    let ctrl = InprocessingControls::new();

    // Enabled by default
    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    assert!(ctrl.probe.enabled);
    assert!(ctrl.backbone.enabled);
    // Disabled by default (CaDiCaL block=0, condition=0; #8080)
    assert!(!ctrl.bce.enabled);
    assert!(!ctrl.condition.enabled);
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(ctrl.gate.enabled);
    assert!(ctrl.congruence.enabled);

    // Disabled by default (BVE unsafe for DPLL(T))
    assert!(!ctrl.bve.enabled);
    // Disabled by default (CaDiCaL opts.cover=false)
    assert!(!ctrl.cce.enabled);
    // Enabled by default (#7037: re-enabled with clause rewriting)
    assert!(ctrl.sweep.enabled);
    // Enabled by default (root causes fixed: #3424/#3466, #3373)
    assert!(ctrl.decompose.enabled);
    assert!(ctrl.factor.enabled);
}

#[test]
fn test_drat_overrides_keep_all_enabled() {
    let ctrl = InprocessingControls::new().with_proof_overrides(false);

    // All techniques remain enabled in DRAT mode
    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    assert!(ctrl.probe.enabled);
    assert!(!ctrl.bve.enabled); // disabled by default, not by DRAT
    assert!(!ctrl.cce.enabled); // disabled by default, not by DRAT
    assert!(!ctrl.bce.enabled); // disabled by default (#8080), not by DRAT
    assert!(!ctrl.condition.enabled); // disabled by default (#8080), not by DRAT
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(ctrl.congruence.enabled); // DRAT: RUP safety gate handles non-RUP batches (#4575)
    assert!(ctrl.decompose.enabled);
    assert!(ctrl.factor.enabled); // DRAT divider+blocked+quotient (#4242)
    assert!(ctrl.sweep.enabled); // #7913: DRAT proof emission via RUP-based post-hoc verification
    assert!(ctrl.gate.enabled);
}

#[test]
fn test_lrat_overrides_keep_all_techniques_enabled() {
    // #8105: With backward LRAT reconstruction as the primary proof path,
    // all techniques are now LRAT-compatible. No lrat_override = true remains.
    let ctrl = InprocessingControls::new().with_proof_overrides(true);

    // All techniques remain enabled in LRAT mode (backward reconstruction)
    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    // BCE and condition are disabled by default (#8080), not by LRAT override.
    assert!(!ctrl.bce.enabled);
    assert!(!ctrl.condition.enabled);
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(ctrl.gate.enabled);
    assert!(ctrl.congruence.enabled);
    assert!(
        ctrl.probe.enabled,
        "probe: LRAT-safe with backward reconstruction (#8105)"
    );
    assert!(
        ctrl.sweep.enabled,
        "sweep: LRAT-safe with backward reconstruction (#8105)"
    );
    assert!(ctrl.decompose.enabled);
    assert!(
        ctrl.factor.enabled,
        "factor: LRAT-safe with backward reconstruction (#8105)"
    );
}

#[test]
fn test_default_intervals_match_constants() {
    let ctrl = InprocessingControls::new();

    assert_eq!(ctrl.vivify.next_conflict, VIVIFY_INTERVAL);
    assert_eq!(ctrl.vivify_irred.next_conflict, VIVIFY_IRRED_INTERVAL);
    assert_eq!(ctrl.subsume.next_conflict, SUBSUME_INTERVAL);
    assert_eq!(ctrl.probe.next_conflict, PROBE_INTERVAL);
    assert_eq!(ctrl.backbone.next_conflict, BACKBONE_INTERVAL);
    assert_eq!(ctrl.bve.next_conflict, 0);
    assert_eq!(ctrl.bce.next_conflict, BCE_INTERVAL);
    assert_eq!(ctrl.condition.next_conflict, CONDITION_INTERVAL);
    assert_eq!(ctrl.decompose.next_conflict, 0);
    assert_eq!(ctrl.factor.next_conflict, FACTOR_INTERVAL);
    assert_eq!(ctrl.transred.next_conflict, TRANSRED_INTERVAL);
    assert_eq!(ctrl.htr.next_conflict, HTR_INTERVAL);
    assert_eq!(ctrl.gate.next_conflict, 0);
    assert_eq!(ctrl.congruence.next_conflict, 0);
    assert_eq!(ctrl.sweep.next_conflict, SWEEP_INTERVAL);
    assert_eq!(ctrl.cce.next_conflict, CCE_INTERVAL);
}

#[test]
fn test_should_fire_logic() {
    let tc = TechniqueControl::new(true, 100);
    assert!(!tc.should_fire(99));
    assert!(tc.should_fire(100));
    assert!(tc.should_fire(200));

    let disabled = TechniqueControl::new(false, 0);
    assert!(!disabled.should_fire(0));
    assert!(!disabled.should_fire(1000));
}

#[test]
fn test_reschedule() {
    let mut tc = TechniqueControl::new(true, 0);
    assert!(tc.should_fire(0));

    tc.reschedule(500, 100);
    assert_eq!(tc.next_conflict, 600);
    assert!(!tc.should_fire(599));
    assert!(tc.should_fire(600));
}

#[test]
fn test_reschedule_growing() {
    let mut tc = TechniqueControl::new(true, 5000);
    // First fire at conflict 5000
    assert!(tc.should_fire(5000));

    // 1.5x growth: 5000 → 7500 → 11250 → 16875
    let interval = tc.reschedule_growing(5000, 5000, 3, 2, 80_000);
    assert_eq!(interval, 7500);
    assert_eq!(tc.next_conflict, 12_500);

    let interval = tc.reschedule_growing(12_500, 5000, 3, 2, 80_000);
    assert_eq!(interval, 11_250);
    assert_eq!(tc.next_conflict, 23_750);

    let interval = tc.reschedule_growing(23_750, 5000, 3, 2, 80_000);
    assert_eq!(interval, 16_875);

    // Verify capping at max_interval
    let mut tc2 = TechniqueControl::new(true, 50_000);
    tc2.interval_used = 60_000;
    let interval = tc2.reschedule_growing(100_000, 5000, 3, 2, 80_000);
    assert_eq!(interval, 80_000); // capped at max
}

#[test]
fn test_reset_interval() {
    let mut tc = TechniqueControl::new(true, 5000);
    tc.interval_used = 40_000;
    tc.next_conflict = 100_000;

    tc.reset_interval(5000);
    assert_eq!(tc.next_conflict, 5000);
    assert_eq!(tc.interval_used, 5000);
}
