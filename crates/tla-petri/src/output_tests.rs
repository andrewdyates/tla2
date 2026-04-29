// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for MCC output formatting contract.
//!
//! The MCC infrastructure parses `FORMULA <name> <verdict> TECHNIQUES <list>`
//! lines from stdout. Any formatting deviation produces invalid competition
//! output for ALL examinations.

use crate::output::{cannot_compute_line, formula_line, Verdict};

#[test]
fn test_verdict_display_true() {
    assert_eq!(Verdict::True.to_string(), "TRUE");
}

#[test]
fn test_verdict_display_false() {
    assert_eq!(Verdict::False.to_string(), "FALSE");
}

#[test]
fn test_verdict_display_cannot_compute() {
    assert_eq!(Verdict::CannotCompute.to_string(), "CANNOT_COMPUTE");
}

#[test]
fn test_formula_line_true_format() {
    let line = formula_line("ModelA-PT-001", "ReachabilityFireability-00", Verdict::True);
    assert_eq!(
        line,
        "FORMULA ModelA-PT-001-ReachabilityFireability-00 TRUE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_formula_line_false_format() {
    let line = formula_line(
        "ModelA-PT-001",
        "ReachabilityFireability-01",
        Verdict::False,
    );
    assert_eq!(
        line,
        "FORMULA ModelA-PT-001-ReachabilityFireability-01 FALSE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_cannot_compute_line_format() {
    let line = cannot_compute_line("ModelA-PT-001", "StateSpace");
    assert_eq!(
        line,
        "FORMULA ModelA-PT-001-StateSpace CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_formula_line_contains_required_mcc_tokens() {
    // MCC parser requires: "FORMULA" prefix, verdict in {TRUE,FALSE,CANNOT_COMPUTE}, "TECHNIQUES"
    let line = formula_line("X", "Y", Verdict::True);
    assert!(line.starts_with("FORMULA "));
    assert!(line.contains(" TECHNIQUES "));
}
