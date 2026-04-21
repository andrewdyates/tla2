// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::output::{cannot_compute_line, formula_line, Verdict};

use super::super::Examination;

#[test]
fn test_formula_line_true() {
    let line = formula_line("MyModel", "ReachabilityDeadlock", Verdict::True);
    assert_eq!(
        line,
        "FORMULA MyModel-ReachabilityDeadlock TRUE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_formula_line_false() {
    let line = formula_line("TestNet", "OneSafe", Verdict::False);
    assert_eq!(line, "FORMULA TestNet-OneSafe FALSE TECHNIQUES EXPLICIT");
}

#[test]
fn test_formula_line_cannot_compute() {
    let line = formula_line("BigNet", "StateSpace", Verdict::CannotCompute);
    assert_eq!(
        line,
        "FORMULA BigNet-StateSpace CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_cannot_compute_line() {
    let line = cannot_compute_line("ColoredNet", "ReachabilityDeadlock");
    assert_eq!(
        line,
        "FORMULA ColoredNet-ReachabilityDeadlock CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_verdict_display() {
    assert_eq!(format!("{}", Verdict::True), "TRUE");
    assert_eq!(format!("{}", Verdict::False), "FALSE");
    assert_eq!(format!("{}", Verdict::CannotCompute), "CANNOT_COMPUTE");
}

#[test]
fn test_examination_from_name_valid() {
    assert_eq!(
        Examination::from_name("ReachabilityDeadlock").unwrap(),
        Examination::ReachabilityDeadlock
    );
    assert_eq!(
        Examination::from_name("StateSpace").unwrap(),
        Examination::StateSpace
    );
    assert_eq!(
        Examination::from_name("OneSafe").unwrap(),
        Examination::OneSafe
    );
    assert_eq!(
        Examination::from_name("QuasiLiveness").unwrap(),
        Examination::QuasiLiveness
    );
    assert_eq!(
        Examination::from_name("StableMarking").unwrap(),
        Examination::StableMarking
    );
    assert_eq!(
        Examination::from_name("Liveness").unwrap(),
        Examination::Liveness
    );
}

#[test]
fn test_examination_from_name_upper_bounds() {
    assert_eq!(
        Examination::from_name("UpperBounds").unwrap(),
        Examination::UpperBounds
    );
}

#[test]
fn test_examination_from_name_invalid() {
    assert!(Examination::from_name("").is_err());
    assert!(Examination::from_name("reachabilitydeadlock").is_err());
}

#[test]
fn test_examination_from_name_reachability() {
    assert_eq!(
        Examination::from_name("ReachabilityCardinality").unwrap(),
        Examination::ReachabilityCardinality
    );
    assert_eq!(
        Examination::from_name("ReachabilityFireability").unwrap(),
        Examination::ReachabilityFireability
    );
}

#[test]
fn test_examination_as_str_roundtrip() {
    for exam in [
        Examination::ReachabilityDeadlock,
        Examination::ReachabilityCardinality,
        Examination::ReachabilityFireability,
        Examination::StateSpace,
        Examination::OneSafe,
        Examination::QuasiLiveness,
        Examination::StableMarking,
        Examination::UpperBounds,
        Examination::Liveness,
    ] {
        assert_eq!(Examination::from_name(exam.as_str()).unwrap(), exam);
    }
}

#[test]
fn test_needs_property_xml() {
    assert!(Examination::UpperBounds.needs_property_xml());
    assert!(Examination::ReachabilityCardinality.needs_property_xml());
    assert!(Examination::ReachabilityFireability.needs_property_xml());
    assert!(!Examination::ReachabilityDeadlock.needs_property_xml());
    assert!(!Examination::StateSpace.needs_property_xml());
    assert!(!Examination::Liveness.needs_property_xml());
}
