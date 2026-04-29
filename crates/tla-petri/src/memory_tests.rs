// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for memory detection and auto-sizing edge cases.
//!
//! Covers NaN/Infinity/negative fraction handling through the public API
//! (compute_max_states) since sanitize_memory_fraction is private.

use crate::marking::TokenWidth;
use crate::memory::{available_memory_bytes, compute_max_states};

#[test]
fn test_compute_max_states_nan_fraction_returns_minimum() {
    // NaN fraction → sanitize returns 0.0 → budget = 0 → clamp to 1 (MIN_MAX_STATES)
    let max = compute_max_states(50, TokenWidth::U8, f64::NAN, true);
    assert_eq!(max, 1);
}

#[test]
fn test_compute_max_states_positive_infinity_fraction_returns_minimum() {
    // Infinity → sanitize returns 0.0 (not finite) → budget = 0 → clamp to 1
    let max = compute_max_states(50, TokenWidth::U8, f64::INFINITY, true);
    assert_eq!(max, 1);
}

#[test]
fn test_compute_max_states_negative_infinity_fraction_returns_minimum() {
    let max = compute_max_states(50, TokenWidth::U8, f64::NEG_INFINITY, true);
    assert_eq!(max, 1);
}

#[test]
fn test_compute_max_states_negative_fraction_returns_minimum() {
    let max = compute_max_states(50, TokenWidth::U8, -0.5, true);
    assert_eq!(max, 1);
}

#[test]
fn test_compute_max_states_zero_fraction_returns_minimum() {
    let max = compute_max_states(50, TokenWidth::U8, 0.0, true);
    assert_eq!(max, 1);
}

#[test]
fn test_compute_max_states_full_fraction_is_largest() {
    // fraction=1.0 uses all memory, fraction=0.25 uses a quarter
    let max_quarter = compute_max_states(50, TokenWidth::U8, 0.25, true);
    let max_full = compute_max_states(50, TokenWidth::U8, 1.0, true);
    assert!(max_full >= max_quarter);
}

#[test]
fn test_compute_max_states_larger_markings_yield_fewer_states() {
    // With fingerprint mode, both sizes use 32 bytes/state (same budget).
    // Without fingerprint, more places = more memory per state = fewer states.
    let max_small = compute_max_states(10, TokenWidth::U8, 0.25, false);
    let max_large = compute_max_states(1000, TokenWidth::U64, 0.25, false);
    if available_memory_bytes().is_some() {
        assert!(max_small > max_large);
    }
}

#[test]
fn test_available_memory_detected_on_this_platform() {
    if cfg!(any(target_os = "linux", target_os = "macos")) {
        let mem = available_memory_bytes();
        assert!(mem.is_some(), "memory detection should work on macOS/Linux");
        assert!(mem.unwrap() > 1_000_000, "should detect at least 1MB");
    }
}
