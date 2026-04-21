// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::{AletheRule, Sort};

// Note: quote_symbol tests are in z4-core::smtlib

#[test]
fn test_empty_proof() {
    let proof = Proof::new();
    let terms = TermStore::new();
    let output = export_alethe(&proof, &terms);
    assert_eq!(output, "");
}

#[test]
fn test_assume_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(declare-fun x () Bool)"),
        "Missing declaration for x: {output}"
    );
    assert!(output.contains("(assume t0 x)"), "Missing assume: {output}");
}

#[test]
fn test_step_with_premises() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(x, None);
    let h2 = proof.add_assume(not_x, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![], // empty clause = contradiction
        vec![h1, h2],
        vec![x], // pivot
    );

    let output = export_alethe(&proof, &terms);
    // Declaration preamble + 3 proof steps
    assert!(
        output.contains("(declare-fun x () Bool)"),
        "Missing declaration: {output}"
    );
    assert!(
        output.contains("(assume t0 x)"),
        "Missing assume h1: {output}"
    );
    assert!(
        output.contains("(assume t1 (not x))"),
        "Missing assume h2: {output}"
    );
    assert!(
        output.contains(":rule resolution"),
        "Missing resolution: {output}"
    );
    assert!(
        output.contains(":premises (t0 t1)"),
        "Missing premises: {output}"
    );
}

#[test]
fn test_theory_lemma_generic() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq = terms.mk_eq(a, b);

    let mut proof = Proof::new();
    proof.add_theory_lemma("EUF", vec![eq]);

    let output = export_alethe(&proof, &terms);
    // Generic lemmas use "trust" rule
    assert!(output.contains(":rule trust"));
    assert!(output.contains("(= a b)"));
}

#[test]
fn test_theory_lemma_with_kind() {
    use z4_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    // Build transitivity clause: (not (= a b)) OR (not (= b c)) OR (= a c)
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule eq_transitive"),
        "Expected eq_transitive rule, got: {output}"
    );
}

#[test]
fn test_theory_lemma_la_generic_with_farkas() {
    use num_rational::Rational64;
    use z4_core::FarkasAnnotation;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(
        10,
    )));

    // x <= 5
    let x_le_5 = terms.mk_le(x, five);
    // x >= 10 (negated as x < 10)
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]),
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule la_generic"),
        "Expected la_generic rule, got: {output}"
    );
    assert!(
        output.contains(":args (1 1)"),
        "Expected :args (1 1), got: {output}"
    );
}

#[test]
fn test_theory_lemma_la_generic_fractional_farkas() {
    use num_rational::Rational64;
    use z4_core::FarkasAnnotation;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(
        10,
    )));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    // Use fractional coefficients: 1/2 and 3/4
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::new(vec![Rational64::new(1, 2), Rational64::new(3, 4)]),
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule la_generic"),
        "Expected la_generic rule, got: {output}"
    );
    // Fractional coefficients must use Real literals for Carcara: (/ 1.0 2.0)
    assert!(
        output.contains("(/ 1.0 2.0)"),
        "Expected (/ 1.0 2.0) for 1/2, got: {output}"
    );
    assert!(
        output.contains("(/ 3.0 4.0)"),
        "Expected (/ 3.0 4.0) for 3/4, got: {output}"
    );
}

#[test]
fn test_format_rational() {
    let mut terms = TermStore::new();
    let rat = terms.mk_rational(num_rational::BigRational::new(1.into(), 2.into()));

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(rat);
    assert_eq!(output, "(/ 1.0 2.0)");
}

#[test]
fn test_format_negative_rational() {
    let mut terms = TermStore::new();
    let rat = terms.mk_rational(num_rational::BigRational::new((-3).into(), 4.into()));

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(rat);
    assert_eq!(output, "(- (/ 3.0 4.0))");
}

#[test]
fn test_format_bitvector() {
    let mut terms = TermStore::new();
    let bv = terms.mk_bitvec(5.into(), 4);

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(bv);
    assert_eq!(output, "#b0101");
}

#[test]
fn test_export_alethe_with_problem_scope_declares_auxiliary_symbols_only() {
    let mut terms = TermStore::new();
    let user_a = terms.mk_var("a", Sort::Int);
    let user_b = terms.mk_var("b", Sort::Int);
    let mod_q = terms.mk_var("_mod_q_2", Sort::Int);
    let mod_r = terms.mk_var("_mod_r_3", Sort::Int);
    let sk = terms.mk_var("__ext_diff_1_2", Sort::Int);

    let user_eq = terms.mk_eq(user_a, user_b);
    let q_eq = terms.mk_eq(mod_q, user_a);
    let r_eq = terms.mk_eq(mod_r, user_b);
    let sk_eq = terms.mk_eq(sk, user_a);

    let mut proof = Proof::new();
    proof.add_assume(q_eq, None);
    proof.add_assume(r_eq, None);
    proof.add_assume(sk_eq, None);

    let output = export_alethe_with_problem_scope(&proof, &terms, &[user_eq]);
    assert!(output.contains("(declare-fun _mod_q_2 () Int)"), "{output}");
    assert!(output.contains("(declare-fun _mod_r_3 () Int)"), "{output}");
    assert!(
        output.contains("(declare-fun __ext_diff_1_2 () Int)"),
        "{output}"
    );
    assert!(!output.contains("(declare-fun a () Int)"), "{output}");
    assert!(!output.contains("(declare-fun b () Int)"), "{output}");
}

#[test]
fn test_export_alethe_with_problem_scope_ignores_bound_auxiliary_names() {
    let mut terms = TermStore::new();
    let aux_name = "_mod_q_2".to_string();
    let aux = terms.mk_var(aux_name.clone(), Sort::Int);
    let body = terms.mk_eq(aux, aux);
    let quantified = terms.mk_forall(vec![(aux_name, Sort::Int)], body);

    let mut proof = Proof::new();
    proof.add_assume(quantified, None);

    let output = export_alethe_with_problem_scope(&proof, &terms, &[]);
    assert!(
        !output.contains("(declare-fun _mod_q_2 () Int)"),
        "bound quantifier variable must not be declared as a free symbol: {output}"
    );
}

#[test]
fn test_skolem_variables_declared() {
    let mut terms = TermStore::new();
    // User-declared variable
    let x = terms.mk_var("x", Sort::Int);
    // Skolem variables (mk_fresh_var, not registered in names map)
    let q = terms.mk_fresh_var("_mod_q", Sort::Int);
    let r = terms.mk_fresh_var("_mod_r", Sort::Int);

    // Build a clause referencing all three variables
    let eq_xq = terms.mk_eq(x, q);
    let eq_xr = terms.mk_eq(x, r);

    let mut proof = Proof::new();
    proof.add_theory_lemma("LIA", vec![eq_xq, eq_xr]);

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(declare-fun x () Int)"),
        "Missing declaration for user var x: {output}"
    );
    assert!(
        output.contains("(declare-fun _mod_q_"),
        "Missing declaration for Skolem _mod_q_*: {output}"
    );
    assert!(
        output.contains("(declare-fun _mod_r_"),
        "Missing declaration for Skolem _mod_r_*: {output}"
    );
    // Declarations must appear before proof steps
    let decl_pos = output.find("(declare-fun").unwrap();
    let step_pos = output.find("(step").unwrap();
    assert!(decl_pos < step_pos, "Declarations must precede proof steps");
}

#[test]
fn test_declarations_sorted_by_name() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let a = terms.mk_var("a", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(b, None);
    proof.add_assume(a, None);

    let output = export_alethe(&proof, &terms);
    let a_pos = output.find("(declare-fun a").unwrap();
    let b_pos = output.find("(declare-fun b").unwrap();
    assert!(a_pos < b_pos, "Declarations must be sorted by name");
}

// NOTE: Carcara integration tests deleted - required external carcara tool (#596)
// Deleted tests: test_carcara_verification, test_carcara_eq_transitive,
// test_carcara_eq_congruent, test_carcara_la_generic
// Run carcara tests manually with: cargo install carcara && CARCARA_PATH=carcara cargo test
