// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Tests for set constraint encodings (set_intersect, set_diff, set_symdiff,
// set_subset, set_eq, set_ne, set_le, set_lt).

use super::*;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = z4_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

// --- set_intersect ---

#[test]
fn test_set_intersect() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         var set of 1..3: S3;\n\
         constraint set_intersect(S1, S2, S3);\n\
         solve satisfy;\n",
    );
    // S3_bit_i = S1_bit_i and S2_bit_i for each bit
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__0 (and S1__bit__0 S2__bit__0)))"));
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__1 (and S1__bit__1 S2__bit__1)))"));
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__2 (and S1__bit__2 S2__bit__2)))"));
}

#[test]
fn test_set_union_mismatched_lower_bounds_aligns_by_value() {
    let r = translate_fzn(
        "var set of 0..1: S1;\n\
         var set of 0..1: S2;\n\
         var set of 1..1: S3;\n\
         constraint set_union(S1, S2, S3);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (= false (or S1__bit__0 S2__bit__0)))"));
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__0 (or S1__bit__1 S2__bit__1)))"));
}

// --- set_diff ---

#[test]
fn test_set_diff() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         var set of 1..3: S3;\n\
         constraint set_diff(S1, S2, S3);\n\
         solve satisfy;\n",
    );
    // S3_bit_i = S1_bit_i and (not S2_bit_i)
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__0 (and S1__bit__0 (not S2__bit__0))))"));
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__1 (and S1__bit__1 (not S2__bit__1))))"));
}

// --- set_symdiff ---

#[test]
fn test_set_symdiff() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         var set of 1..3: S3;\n\
         constraint set_symdiff(S1, S2, S3);\n\
         solve satisfy;\n",
    );
    // S3_bit_i = S1_bit_i xor S2_bit_i
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__0 (xor S1__bit__0 S2__bit__0)))"));
}

// --- set_subset ---

#[test]
fn test_set_subset() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         constraint set_subset(S1, S2);\n\
         solve satisfy;\n",
    );
    // S1_bit_i => S2_bit_i for each bit
    assert!(r.smtlib.contains("(assert (=> S1__bit__0 S2__bit__0))"));
    assert!(r.smtlib.contains("(assert (=> S1__bit__1 S2__bit__1))"));
    assert!(r.smtlib.contains("(assert (=> S1__bit__2 S2__bit__2))"));
}

// --- set_superset ---

#[test]
fn test_set_superset() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         constraint set_superset(S1, S2);\n\
         solve satisfy;\n",
    );
    // S2_bit_i => S1_bit_i (reverse of subset)
    assert!(r.smtlib.contains("(assert (=> S2__bit__0 S1__bit__0))"));
    assert!(r.smtlib.contains("(assert (=> S2__bit__1 S1__bit__1))"));
}

// --- set_eq ---

#[test]
fn test_set_eq() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         constraint set_eq(S1, S2);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= S1__bit__0 S2__bit__0))"));
    assert!(r.smtlib.contains("(assert (= S1__bit__1 S2__bit__1))"));
}

// --- set_ne ---

#[test]
fn test_set_ne() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         constraint set_ne(S1, S2);\n\
         solve satisfy;\n",
    );
    // At least one bit differs
    assert!(r
        .smtlib
        .contains("(assert (or (xor S1__bit__0 S2__bit__0) (xor S1__bit__1 S2__bit__1)))"));
}

// --- set_le ---

#[test]
fn test_set_le() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         constraint set_le(S1, S2);\n\
         solve satisfy;\n",
    );
    // S1 subset-or-equal S2: S1_bit_i => S2_bit_i
    assert!(r.smtlib.contains("(assert (=> S1__bit__0 S2__bit__0))"));
    assert!(r.smtlib.contains("(assert (=> S1__bit__1 S2__bit__1))"));
}

// --- set_lt ---

#[test]
fn test_set_lt() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         constraint set_lt(S1, S2);\n\
         solve satisfy;\n",
    );
    // S1 strict subset of S2: subset + at least one bit differs
    assert!(r.smtlib.contains("(assert (=> S1__bit__0 S2__bit__0))"));
    assert!(r
        .smtlib
        .contains("(assert (or (xor S1__bit__0 S2__bit__0) (xor S1__bit__1 S2__bit__1)))"));
}

// --- single-element set domain ---

#[test]
fn test_set_intersect_single_bit() {
    let r = translate_fzn(
        "var set of 5..5: S1;\n\
         var set of 5..5: S2;\n\
         var set of 5..5: S3;\n\
         constraint set_intersect(S1, S2, S3);\n\
         solve satisfy;\n",
    );
    // Width 1: only one bit assertion
    assert!(r
        .smtlib
        .contains("(assert (= S3__bit__0 (and S1__bit__0 S2__bit__0)))"));
    // No bit__1 should exist
    assert!(!r.smtlib.contains("__bit__1"));
}

// --- set_eq_reif ---

#[test]
fn test_set_eq_reif() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         var bool: r;\n\
         constraint set_eq_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // r <=> (S1_bit_0 = S2_bit_0) and (S1_bit_1 = S2_bit_1)
    assert!(r
        .smtlib
        .contains("(assert (=> r (and (= S1__bit__0 S2__bit__0) (= S1__bit__1 S2__bit__1))))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (and (= S1__bit__0 S2__bit__0) (= S1__bit__1 S2__bit__1)) r))"));
}

#[test]
fn test_set_eq_reif_single_bit() {
    let r = translate_fzn(
        "var set of 5..5: S1;\n\
         var set of 5..5: S2;\n\
         var bool: r;\n\
         constraint set_eq_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // Width 1: single equality, no (and ...)
    assert!(r
        .smtlib
        .contains("(assert (=> r (= S1__bit__0 S2__bit__0)))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (= S1__bit__0 S2__bit__0) r))"));
}

// --- set_ne_reif ---

#[test]
fn test_set_ne_reif() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         var bool: r;\n\
         constraint set_ne_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // r <=> (xor bit_0) or (xor bit_1)
    assert!(r
        .smtlib
        .contains("(assert (=> r (or (xor S1__bit__0 S2__bit__0) (xor S1__bit__1 S2__bit__1))))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (or (xor S1__bit__0 S2__bit__0) (xor S1__bit__1 S2__bit__1)) r))"));
}

#[test]
fn test_set_ne_reif_single_bit() {
    let r = translate_fzn(
        "var set of 3..3: S1;\n\
         var set of 3..3: S2;\n\
         var bool: r;\n\
         constraint set_ne_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // Width 1: single xor, no (or ...)
    assert!(r
        .smtlib
        .contains("(assert (=> r (xor S1__bit__0 S2__bit__0)))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (xor S1__bit__0 S2__bit__0) r))"));
}

// --- set_subset_reif ---

#[test]
fn test_set_subset_reif() {
    let r = translate_fzn(
        "var set of 1..3: S1;\n\
         var set of 1..3: S2;\n\
         var bool: r;\n\
         constraint set_subset_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // r <=> (S1_bit_0 => S2_bit_0) and ... and (S1_bit_2 => S2_bit_2)
    assert!(r.smtlib.contains("(assert (=> r (and (=> S1__bit__0 S2__bit__0) (=> S1__bit__1 S2__bit__1) (=> S1__bit__2 S2__bit__2))))"));
    assert!(r.smtlib.contains("(assert (=> (and (=> S1__bit__0 S2__bit__0) (=> S1__bit__1 S2__bit__1) (=> S1__bit__2 S2__bit__2)) r))"));
}

// --- set_le_reif ---

#[test]
fn test_set_le_reif() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         var bool: r;\n\
         constraint set_le_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // set_le_reif delegates to set_subset_reif
    assert!(r
        .smtlib
        .contains("(assert (=> r (and (=> S1__bit__0 S2__bit__0) (=> S1__bit__1 S2__bit__1))))"));
}

// --- set_lt_reif ---

#[test]
fn test_set_lt_reif() {
    let r = translate_fzn(
        "var set of 1..2: S1;\n\
         var set of 1..2: S2;\n\
         var bool: r;\n\
         constraint set_lt_reif(S1, S2, r);\n\
         solve satisfy;\n",
    );
    // r <=> (subset_cond and ne_cond)
    let smt = &r.smtlib;
    assert!(smt.contains("(assert (=> r (and (and (=> S1__bit__0 S2__bit__0) (=> S1__bit__1 S2__bit__1)) (or (xor S1__bit__0 S2__bit__0) (xor S1__bit__1 S2__bit__1)))))"));
}

// --- set output variable registration ---

#[test]
fn test_set_output_var_registered() {
    let r = translate_fzn(
        "var set of 1..3: S :: output_var;\n\
         solve satisfy;\n",
    );
    // output_vars should contain S with is_set=true
    assert_eq!(r.output_vars.len(), 1);
    let ov = &r.output_vars[0];
    assert_eq!(ov.fzn_name, "S");
    assert!(ov.is_set);
    assert_eq!(ov.set_range, Some((1, 3)));
    assert_eq!(ov.smt_names, vec!["S__bit__0", "S__bit__1", "S__bit__2"]);
}

#[test]
fn test_set_output_var_not_registered_without_annotation() {
    let r = translate_fzn(
        "var set of 1..3: S;\n\
         solve satisfy;\n",
    );
    // No output annotation → no output vars
    assert!(r.output_vars.is_empty());
}

#[test]
fn test_set_output_smt_names_included() {
    let r = translate_fzn(
        "var set of 5..6: S :: output_var;\n\
         solve satisfy;\n",
    );
    // output_smt_names should contain the bit variable names
    assert!(r.output_smt_names.contains(&"S__bit__0".to_string()));
    assert!(r.output_smt_names.contains(&"S__bit__1".to_string()));
}
