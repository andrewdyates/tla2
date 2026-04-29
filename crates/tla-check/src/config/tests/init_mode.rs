// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// InitMode helper method tests - Part of #524 self-audit
//
// Note: InitMode::resolve() is not tested here because it reads actual
// environment variables (TLA2_FORCE_Z4, TLA2_USE_Z4). Testing env var logic
// in parallel test suites requires isolation (e.g., serial_test crate or
// temp_env) to avoid tests affecting each other. The logic is simple enough
// (3-way if/else) that the risk of bugs is low. Integration tests exercise
// the full path via TLA2_FORCE_Z4/TLA2_USE_Z4 env vars.

// Part of #2757: z4_decision and should_skip_analysis are gated behind
// cfg(feature = "z4") in production code; tests must match.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_mode_z4_decision_brute_force() {
    // BruteForce should never try z4
    assert_eq!(InitMode::BruteForce.z4_decision(true), (false, false));
    assert_eq!(InitMode::BruteForce.z4_decision(false), (false, false));
}

#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_mode_z4_decision_auto() {
    // Auto should follow analysis recommendation
    assert_eq!(InitMode::Auto.z4_decision(true), (false, true));
    assert_eq!(InitMode::Auto.z4_decision(false), (false, false));
}

#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_mode_z4_decision_force_z4() {
    // ForceZ4 should always try z4
    assert_eq!(InitMode::ForceZ4.z4_decision(true), (true, true));
    assert_eq!(InitMode::ForceZ4.z4_decision(false), (true, true));
}

#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_mode_should_skip_analysis() {
    assert!(InitMode::BruteForce.should_skip_analysis());
    assert!(!InitMode::Auto.should_skip_analysis());
    assert!(!InitMode::ForceZ4.should_skip_analysis());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_config_default_init_mode() {
    let config = Config::default();
    assert_eq!(config.init_mode, InitMode::Auto);
}
