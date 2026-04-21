// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for model output of FP, String, and Seq sorts.
//!
//! Before this fix, `get-model` emitted default values (zeros, empty strings)
//! for FloatingPoint, String, and Seq variables instead of their actual model
//! values. This caused incorrect counterexamples for consumers.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run Z4 with given SMT-LIB input and return stdout.
fn run_z4(input: &str) -> String {
    let z4_path = env!("CARGO_BIN_EXE_z4");

    let mut child = Command::new(z4_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn z4");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on z4");
    String::from_utf8_lossy(&output.stdout).to_string()
}

/// FP model output should contain actual FP values, not default zeros.
///
/// Before fix: `(define-fun x () (_ FloatingPoint 8 24) (_ +zero 8 24))`
/// After fix:  `(define-fun x () (_ FloatingPoint 8 24) (fp #b0 #b00111111 ...))`
#[test]
#[timeout(30_000)]
fn fp_model_contains_actual_values_not_defaults() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp #b0 #x3f #b00000000000000000000000)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun x ()"),
        "Model should contain definition for x, got: {output}"
    );
    // The value should NOT be the default +zero
    assert!(
        !output.contains("+zero"),
        "FP model value should be actual value, not default +zero. Got: {output}"
    );
    // Should contain an actual (fp ...) value
    assert!(
        output.contains("(fp #b"),
        "FP model should contain (fp #b...) literal. Got: {output}"
    );
}

/// FP model with distinct non-zero values should reflect both correctly.
#[test]
#[timeout(30_000)]
fn fp_model_distinct_values() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (fp.eq a (fp #b0 #x3f #b00000000000000000000000)))
(assert (fp.eq b (fp #b0 #x40 #b00000000000000000000000)))
(assert (not (fp.eq a b)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    // Both a and b should be present in model
    assert!(
        output.contains("(define-fun a ()"),
        "Model should contain a, got: {output}"
    );
    assert!(
        output.contains("(define-fun b ()"),
        "Model should contain b, got: {output}"
    );
}

/// Seq model with explicit concat value should show actual elements, not seq.empty.
///
/// Before fix: `(define-fun s () (Seq Int) (as seq.empty (Seq Int)))`
/// After fix:  `(define-fun s () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2)))`
#[test]
#[timeout(30_000)]
fn seq_model_contains_actual_values_not_empty() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun s ()"),
        "Model should contain definition for s, got: {output}"
    );
    // The value should NOT be the default seq.empty
    assert!(
        !output.contains("seq.empty"),
        "Seq model value should be actual value, not default seq.empty. Got: {output}"
    );
    // Should contain seq.unit elements
    assert!(
        output.contains("seq.unit 1"),
        "Seq model should contain (seq.unit 1). Got: {output}"
    );
    assert!(
        output.contains("seq.unit 2"),
        "Seq model should contain (seq.unit 2). Got: {output}"
    );
}

/// Seq model for a single-element sequence should use seq.unit directly.
#[test]
#[timeout(30_000)]
fn seq_model_single_unit() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.unit 42)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("seq.unit 42"),
        "Seq model should contain (seq.unit 42). Got: {output}"
    );
}

/// Seq model for an empty sequence should correctly show seq.empty.
#[test]
#[timeout(30_000)]
fn seq_model_empty_sequence() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (as seq.empty (Seq Int))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("seq.empty"),
        "Empty Seq model should contain seq.empty. Got: {output}"
    );
}

/// Seq model for a 3+ element sequence must use binary seq.++ (SMT-LIB 2.6).
///
/// Before fix: `(seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))` (n-ary, not parseable)
/// After fix:  `(seq.++ (seq.++ (seq.unit 1) (seq.unit 2)) (seq.unit 3))` (binary, round-trippable)
#[test]
#[timeout(30_000)]
fn seq_model_multi_element_uses_binary_concat() {
    // Use explicit concat assignment so the model reflects 3 concrete elements.
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_z4(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun s ()"),
        "Model should contain definition for s, got: {output}"
    );
    // The model must use binary seq.++ — i.e., each seq.++ has exactly 2 arguments.
    // With 3 elements, the output should be nested: (seq.++ (seq.++ a b) c)
    // NOT n-ary: (seq.++ a b c)
    //
    // Count occurrences of "seq.++" — for 3 elements we need 2 binary applications.
    let concat_count = output.matches("seq.++").count();
    assert!(
        concat_count >= 2,
        "3-element seq model should have at least 2 seq.++ applications (binary nesting), \
         found {concat_count}. Got: {output}"
    );
    // All 3 elements should be present as seq.unit terms
    assert!(
        output.contains("seq.unit 1")
            && output.contains("seq.unit 2")
            && output.contains("seq.unit 3"),
        "All 3 elements should be present in model. Got: {output}"
    );
}
