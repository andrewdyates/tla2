// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn unknown_reason_display_matches_smtlib_style() {
    assert_eq!(UnknownReason::Timeout.to_string(), "timeout");
    assert_eq!(UnknownReason::ResourceLimit.to_string(), "resourceout");
    assert_eq!(UnknownReason::MemoryLimit.to_string(), "memout");
    assert_eq!(UnknownReason::Interrupted.to_string(), "interrupted");
    assert_eq!(UnknownReason::Incomplete.to_string(), "incomplete");
    assert_eq!(
        UnknownReason::QuantifierRoundLimit.to_string(),
        "(incomplete quantifier-round-limit)"
    );
    assert_eq!(
        UnknownReason::QuantifierDeferred.to_string(),
        "(incomplete quantifier-deferred)"
    );
    assert_eq!(
        UnknownReason::QuantifierUnhandled.to_string(),
        "(incomplete quantifier-unhandled)"
    );
    assert_eq!(
        UnknownReason::QuantifierCegqiIncomplete.to_string(),
        "(incomplete quantifier-cegqi)"
    );
    assert_eq!(
        UnknownReason::QuantifierEmatchingExistsIncomplete.to_string(),
        "(incomplete quantifier-ematching-exists)"
    );
    assert_eq!(UnknownReason::SplitLimit.to_string(), "incomplete");
    assert_eq!(UnknownReason::Unsupported.to_string(), "unsupported");
    assert_eq!(UnknownReason::Unknown.to_string(), "unknown");
}

#[test]
fn stat_value_display_formats_basic_types() {
    assert_eq!(StatValue::Int(7).to_string(), "7");
    assert_eq!(StatValue::Float(1.234).to_string(), "1.23");
    assert_eq!(StatValue::String("x".to_string()).to_string(), "\"x\"");
}

#[test]
fn statistics_get_int_reads_known_and_extra_ints() {
    let mut stats = Statistics::new();
    stats.conflicts = 3;
    stats.set_int("my_stat", 9);
    stats.set_float("my_float", 1.0);

    assert_eq!(stats.get_int("conflicts"), Some(3));
    assert_eq!(stats.get_int("my_stat"), Some(9));
    assert_eq!(stats.get_int("my_float"), None);
    assert_eq!(stats.get_int("missing"), None);
}

#[test]
fn statistics_display_includes_core_fields_and_extra() {
    let mut stats = Statistics::new();
    stats.conflicts = 7;
    stats.set_int("extra_int", 12);

    let s = stats.to_string();
    assert!(s.starts_with("(:statistics\n"));
    assert!(s.contains(":conflicts 7"));
    assert!(s.contains(":extra_int 12"));
    assert!(s.ends_with(')'));
}

#[test]
fn test_debug_assert_consistency_passes_for_valid_stats() {
    let mut stats = Statistics::new();
    stats.conflicts = 10;
    stats.propagations = 20;
    stats.theory_conflicts = 5;
    stats.theory_propagations = 10;
    // Should not panic: theory <= SAT
    stats.debug_assert_consistency();
}

#[test]
fn test_debug_assert_consistency_passes_for_zero_stats() {
    let stats = Statistics::new();
    stats.debug_assert_consistency();
}

#[test]
fn test_debug_assert_consistency_passes_for_equal_stats() {
    let mut stats = Statistics::new();
    stats.conflicts = 5;
    stats.propagations = 5;
    stats.theory_conflicts = 5;
    stats.theory_propagations = 5;
    stats.debug_assert_consistency();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "BUG: theory_conflicts")]
fn test_debug_assert_consistency_panics_when_theory_conflicts_exceed_sat() {
    let mut stats = Statistics::new();
    stats.conflicts = 1;
    stats.propagations = 2;
    stats.theory_conflicts = 2;
    stats.theory_propagations = 2;
    stats.debug_assert_consistency();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "BUG: theory_propagations")]
fn test_debug_assert_consistency_panics_when_theory_propagations_exceed_sat() {
    let mut stats = Statistics::new();
    stats.conflicts = 2;
    stats.propagations = 1;
    stats.theory_conflicts = 2;
    stats.theory_propagations = 2;
    stats.debug_assert_consistency();
}
