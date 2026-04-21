// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MCC output format compliance tests.
//!
//! The MCC (Model Checking Contest) infrastructure parses stdout lines with
//! the format: `FORMULA <id> <verdict> TECHNIQUES <list>`
//!
//! These tests verify that ALL 13 examination types produce valid MCC output
//! lines, covering:
//! - Non-property examinations (single FORMULA line each)
//! - Property examinations (one FORMULA line per property)
//! - StateSpace (numeric output format)
//! - UpperBounds (numeric bound format)
//! - CANNOT_COMPUTE for unsupported/unavailable examinations
//! - ExaminationRecord::to_mcc_line() for all value types

use crate::examination::{
    Examination, ExaminationRecord, ExaminationValue, StateSpaceReport, Verdict,
};
use crate::output::{cannot_compute_line, formula_line};

// ---------------------------------------------------------------------------
// MCC line format validation helpers
// ---------------------------------------------------------------------------

/// Validates that a line matches the MCC FORMULA output specification.
/// Valid formats:
///   FORMULA <id> TRUE TECHNIQUES <list>
///   FORMULA <id> FALSE TECHNIQUES <list>
///   FORMULA <id> CANNOT_COMPUTE TECHNIQUES <list>
///   FORMULA <id> <number> TECHNIQUES <list>  (for UpperBounds)
///   FORMULA <id> <n> <n> <n> <n> TECHNIQUES <list>  (for StateSpace)
fn is_valid_mcc_line(line: &str) -> bool {
    // Must start with "FORMULA "
    if !line.starts_with("FORMULA ") {
        return false;
    }
    // Must contain " TECHNIQUES " followed by at least one technique name
    if !line.contains(" TECHNIQUES ") {
        return false;
    }
    let techniques_idx = line.find(" TECHNIQUES ").unwrap();
    let after_techniques = &line[techniques_idx + " TECHNIQUES ".len()..];
    if after_techniques.trim().is_empty() {
        return false;
    }
    true
}

/// Validates that a formula line uses one of the standard verdicts.
fn has_standard_verdict(line: &str) -> bool {
    line.contains(" TRUE TECHNIQUES ")
        || line.contains(" FALSE TECHNIQUES ")
        || line.contains(" CANNOT_COMPUTE TECHNIQUES ")
}

/// Extract the formula ID from an MCC line.
fn extract_formula_id(line: &str) -> &str {
    let after_formula = &line["FORMULA ".len()..];
    // ID ends at the first space that starts a verdict or number
    after_formula.split_whitespace().next().unwrap_or("")
}

// ---------------------------------------------------------------------------
// ExaminationRecord::to_mcc_line() tests for all value types
// ---------------------------------------------------------------------------

#[test]
fn test_record_to_mcc_line_verdict_true() {
    let record = ExaminationRecord::new(
        "Model-PT-001-ReachabilityDeadlock".to_string(),
        ExaminationValue::Verdict(Verdict::True),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-ReachabilityDeadlock TRUE TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
}

#[test]
fn test_record_to_mcc_line_verdict_false() {
    let record = ExaminationRecord::new(
        "Model-PT-001-OneSafe".to_string(),
        ExaminationValue::Verdict(Verdict::False),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-OneSafe FALSE TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
}

#[test]
fn test_record_to_mcc_line_verdict_cannot_compute() {
    let record = ExaminationRecord::new(
        "Model-PT-001-Liveness".to_string(),
        ExaminationValue::Verdict(Verdict::CannotCompute),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-Liveness CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
}

#[test]
fn test_record_to_mcc_line_optional_bound_some() {
    let record = ExaminationRecord::new(
        "Model-PT-001-UpperBounds-03".to_string(),
        ExaminationValue::OptionalBound(Some(42)),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-UpperBounds-03 42 TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
}

#[test]
fn test_record_to_mcc_line_optional_bound_none() {
    let record = ExaminationRecord::new(
        "Model-PT-001-UpperBounds-07".to_string(),
        ExaminationValue::OptionalBound(None),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-UpperBounds-07 CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
}

#[test]
fn test_record_to_mcc_line_state_space_some() {
    let report = StateSpaceReport::new(1024, 2048, 5, 10);
    let record = ExaminationRecord::new(
        "Model-PT-001-StateSpace".to_string(),
        ExaminationValue::StateSpace(Some(report)),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-StateSpace 1024 2048 5 10 TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
}

#[test]
fn test_record_to_mcc_line_state_space_none() {
    let record = ExaminationRecord::new(
        "Model-PT-001-StateSpace".to_string(),
        ExaminationValue::StateSpace(None),
    );
    let line = record.to_mcc_line();
    assert_eq!(
        line,
        "FORMULA Model-PT-001-StateSpace CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
}

// ---------------------------------------------------------------------------
// output.rs formula_line() and cannot_compute_line() format tests
// ---------------------------------------------------------------------------

#[test]
fn test_formula_line_all_verdicts_valid_mcc_format() {
    for verdict in [Verdict::True, Verdict::False, Verdict::CannotCompute] {
        let line = formula_line("TestModel-PT-001", "ReachabilityDeadlock", verdict);
        assert!(
            is_valid_mcc_line(&line),
            "invalid MCC line for verdict {verdict:?}: {line}"
        );
    }
}

#[test]
fn test_cannot_compute_line_valid_mcc_format() {
    let line = cannot_compute_line("TestModel-PT-001", "CTLCardinality");
    assert!(is_valid_mcc_line(&line));
    assert!(has_standard_verdict(&line));
    assert!(line.contains("CANNOT_COMPUTE"));
}

// ---------------------------------------------------------------------------
// Examination enum coverage: all 13 types parse and roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_all_13_examinations_parse_from_name() {
    let all_names = [
        "ReachabilityDeadlock",
        "ReachabilityCardinality",
        "ReachabilityFireability",
        "CTLCardinality",
        "CTLFireability",
        "LTLCardinality",
        "LTLFireability",
        "StateSpace",
        "OneSafe",
        "QuasiLiveness",
        "StableMarking",
        "UpperBounds",
        "Liveness",
    ];
    assert_eq!(
        all_names.len(),
        13,
        "MCC has exactly 13 examination types"
    );

    for name in all_names {
        let exam = Examination::from_name(name)
            .unwrap_or_else(|_| panic!("failed to parse examination: {name}"));
        assert_eq!(exam.as_str(), name, "roundtrip failed for {name}");
    }
}

#[test]
fn test_all_13_examinations_produce_valid_cannot_compute_line() {
    let all_exams = [
        Examination::ReachabilityDeadlock,
        Examination::ReachabilityCardinality,
        Examination::ReachabilityFireability,
        Examination::CTLCardinality,
        Examination::CTLFireability,
        Examination::LTLCardinality,
        Examination::LTLFireability,
        Examination::StateSpace,
        Examination::OneSafe,
        Examination::QuasiLiveness,
        Examination::StableMarking,
        Examination::UpperBounds,
        Examination::Liveness,
    ];

    for exam in all_exams {
        let line = cannot_compute_line("TestModel-PT-001", exam.as_str());
        assert!(
            is_valid_mcc_line(&line),
            "invalid CANNOT_COMPUTE line for {}: {line}",
            exam.as_str()
        );
        assert!(
            line.contains("CANNOT_COMPUTE"),
            "line should contain CANNOT_COMPUTE for {}: {line}",
            exam.as_str()
        );
        let expected_id = format!("TestModel-PT-001-{}", exam.as_str());
        assert_eq!(
            extract_formula_id(&line),
            expected_id,
            "formula ID mismatch for {}",
            exam.as_str()
        );
    }
}

// ---------------------------------------------------------------------------
// Property vs non-property examination classification
// ---------------------------------------------------------------------------

#[test]
fn test_property_examinations_need_xml() {
    // These 7 examinations require property XML files
    let property_exams = [
        Examination::ReachabilityCardinality,
        Examination::ReachabilityFireability,
        Examination::CTLCardinality,
        Examination::CTLFireability,
        Examination::LTLCardinality,
        Examination::LTLFireability,
        Examination::UpperBounds,
    ];
    for exam in property_exams {
        assert!(
            exam.needs_property_xml(),
            "{} should need property XML",
            exam.as_str()
        );
    }
}

#[test]
fn test_non_property_examinations_do_not_need_xml() {
    // These 6 examinations do NOT require property XML files
    let non_property_exams = [
        Examination::ReachabilityDeadlock,
        Examination::StateSpace,
        Examination::OneSafe,
        Examination::QuasiLiveness,
        Examination::StableMarking,
        Examination::Liveness,
    ];
    for exam in non_property_exams {
        assert!(
            !exam.needs_property_xml(),
            "{} should NOT need property XML",
            exam.as_str()
        );
    }
}

#[test]
fn test_property_plus_non_property_equals_13() {
    let property_count = [
        Examination::ReachabilityCardinality,
        Examination::ReachabilityFireability,
        Examination::CTLCardinality,
        Examination::CTLFireability,
        Examination::LTLCardinality,
        Examination::LTLFireability,
        Examination::UpperBounds,
    ]
    .len();
    let non_property_count = [
        Examination::ReachabilityDeadlock,
        Examination::StateSpace,
        Examination::OneSafe,
        Examination::QuasiLiveness,
        Examination::StableMarking,
        Examination::Liveness,
    ]
    .len();
    assert_eq!(
        property_count + non_property_count,
        13,
        "property + non-property must equal 13 total MCC examinations"
    );
}

// ---------------------------------------------------------------------------
// Formula ID format validation
// ---------------------------------------------------------------------------

#[test]
fn test_non_property_formula_id_format() {
    // Non-property examinations produce IDs like: <model_name>-<examination>
    let model = "TokenRing-PT-010";
    let non_prop_exams = [
        "ReachabilityDeadlock",
        "StateSpace",
        "OneSafe",
        "QuasiLiveness",
        "StableMarking",
        "Liveness",
    ];
    for exam_name in non_prop_exams {
        let expected_id = format!("{model}-{exam_name}");
        let line = formula_line(model, exam_name, Verdict::True);
        assert_eq!(
            extract_formula_id(&line),
            expected_id,
            "formula ID format wrong for {exam_name}"
        );
    }
}

#[test]
fn test_property_formula_id_includes_index() {
    // Property examinations produce IDs with an index suffix from the XML.
    // When used through formula_line(), the examination param includes the index.
    let model = "TokenRing-PT-010";
    let line = formula_line(model, "ReachabilityFireability-03", Verdict::True);
    let id = extract_formula_id(&line);
    assert_eq!(id, "TokenRing-PT-010-ReachabilityFireability-03");
}

// ---------------------------------------------------------------------------
// MCC line strict format validation
// ---------------------------------------------------------------------------

/// Validate that a verdict line has exactly the expected structure:
/// `FORMULA <id> <VERDICT> TECHNIQUES <TECHNIQUE>`
/// where <id> contains no whitespace and <VERDICT> is one of TRUE/FALSE/CANNOT_COMPUTE.
fn validate_verdict_line_structure(line: &str) {
    let parts: Vec<&str> = line.split_whitespace().collect();
    assert!(parts.len() >= 4, "too few tokens in MCC line: {line}");
    assert_eq!(parts[0], "FORMULA", "first token must be FORMULA: {line}");
    // parts[1] is the ID (no whitespace, validated by split)
    assert!(!parts[1].is_empty(), "formula ID must not be empty: {line}");
    // parts[2] must be a valid verdict
    let valid_verdicts = ["TRUE", "FALSE", "CANNOT_COMPUTE"];
    assert!(
        valid_verdicts.contains(&parts[2]),
        "invalid verdict '{}' in line: {line}",
        parts[2]
    );
    assert_eq!(
        parts[3], "TECHNIQUES",
        "fourth token must be TECHNIQUES: {line}"
    );
    assert!(
        parts.len() >= 5,
        "must have at least one technique name: {line}"
    );
    // Technique names should be uppercase alphanumeric with underscores
    for technique in &parts[4..] {
        assert!(
            technique.chars().all(|c| c.is_ascii_uppercase() || c == '_'),
            "technique name '{}' contains invalid chars in: {line}",
            technique
        );
    }
}

#[test]
fn test_verdict_lines_strict_structure() {
    let test_cases = [
        formula_line("M-PT-001", "ReachabilityDeadlock", Verdict::True),
        formula_line("M-PT-001", "OneSafe", Verdict::False),
        formula_line("M-PT-001", "Liveness", Verdict::CannotCompute),
        cannot_compute_line("M-PT-001", "CTLFireability"),
    ];

    for line in &test_cases {
        validate_verdict_line_structure(line);
    }
}

#[test]
fn test_bound_lines_strict_structure() {
    // MCC specification for UpperBounds numeric output:
    // FORMULA <id> <non_negative_integer> TECHNIQUES <technique_list>
    let record = ExaminationRecord::new(
        "M-PT-001-UpperBounds-00".to_string(),
        ExaminationValue::OptionalBound(Some(7)),
    );
    let line = record.to_mcc_line();
    let parts: Vec<&str> = line.split_whitespace().collect();
    assert_eq!(parts[0], "FORMULA");
    assert_eq!(parts[1], "M-PT-001-UpperBounds-00");
    assert_eq!(parts[2], "7", "bound value should be numeric");
    assert_eq!(parts[3], "TECHNIQUES");
    assert_eq!(parts[4], "EXPLICIT");
}

#[test]
fn test_state_space_lines_strict_structure() {
    // MCC specification for StateSpace:
    // FORMULA <id> <states> <edges> <max_token_in_place> <max_token_sum> TECHNIQUES <list>
    let report = StateSpaceReport::new(100, 200, 3, 15);
    let record = ExaminationRecord::new(
        "M-PT-001-StateSpace".to_string(),
        ExaminationValue::StateSpace(Some(report)),
    );
    let line = record.to_mcc_line();
    let parts: Vec<&str> = line.split_whitespace().collect();
    assert_eq!(parts.len(), 8, "StateSpace line should have 8 tokens: {line}");
    assert_eq!(parts[0], "FORMULA");
    assert_eq!(parts[1], "M-PT-001-StateSpace");
    assert_eq!(parts[2], "100", "states");
    assert_eq!(parts[3], "200", "edges");
    assert_eq!(parts[4], "3", "max_token_in_place");
    assert_eq!(parts[5], "15", "max_token_sum");
    assert_eq!(parts[6], "TECHNIQUES");
    assert_eq!(parts[7], "EXPLICIT");
}

// ---------------------------------------------------------------------------
// Stdout cleanliness: only FORMULA lines on stdout
// ---------------------------------------------------------------------------

#[test]
fn test_mcc_output_contains_no_debug_noise() {
    // The output module should produce only FORMULA lines.
    // Verify none of the output functions produce debug/log prefixes.
    let lines = [
        formula_line("M", "X", Verdict::True),
        formula_line("M", "X", Verdict::False),
        formula_line("M", "X", Verdict::CannotCompute),
        cannot_compute_line("M", "X"),
    ];
    let noise_prefixes = ["DEBUG", "INFO", "WARN", "ERROR", "TRACE", "[", "//"];
    for line in &lines {
        for prefix in &noise_prefixes {
            assert!(
                !line.starts_with(prefix),
                "MCC output line starts with noise prefix '{prefix}': {line}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Techniques field
// ---------------------------------------------------------------------------

#[test]
fn test_techniques_field_is_explicit() {
    // Our tool uses "EXPLICIT" as the technique since we use explicit
    // state enumeration. This must be a valid MCC technique identifier.
    let line = formula_line("M", "X", Verdict::True);
    assert!(line.ends_with("TECHNIQUES EXPLICIT"));
}

#[test]
fn test_techniques_field_no_trailing_whitespace() {
    let line = formula_line("Model-PT-001", "ReachabilityDeadlock", Verdict::True);
    assert_eq!(line, line.trim_end(), "MCC line has trailing whitespace");
}

#[test]
fn test_techniques_field_no_leading_whitespace() {
    let line = formula_line("Model-PT-001", "ReachabilityDeadlock", Verdict::True);
    assert_eq!(line, line.trim_start(), "MCC line has leading whitespace");
}
