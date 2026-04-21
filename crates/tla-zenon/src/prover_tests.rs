// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn prove(goal: Formula) -> bool {
    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());
    result.is_valid()
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_tautology_excluded_middle() {
    // P ∨ ¬P
    let p = Formula::atom("P");
    let goal = Formula::or(p.clone(), Formula::not(p));
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_tautology_double_negation() {
    // ¬¬P → P
    let p = Formula::atom("P");
    let goal = Formula::implies(Formula::not(Formula::not(p.clone())), p);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_tautology_modus_ponens() {
    // ((P → Q) ∧ P) → Q
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(Formula::and(Formula::implies(p.clone(), q.clone()), p), q);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_tautology_and_elim() {
    // (P ∧ Q) → P
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(Formula::and(p.clone(), q), p);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_tautology_or_intro() {
    // P → (P ∨ Q)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(p.clone(), Formula::or(p, q));
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_de_morgan_1() {
    // ¬(P ∧ Q) ↔ (¬P ∨ ¬Q)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::equiv(
        Formula::not(Formula::and(p.clone(), q.clone())),
        Formula::or(Formula::not(p), Formula::not(q)),
    );
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_de_morgan_2() {
    // ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::equiv(
        Formula::not(Formula::or(p.clone(), q.clone())),
        Formula::and(Formula::not(p), Formula::not(q)),
    );
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_contrapositive() {
    // (P → Q) ↔ (¬Q → ¬P)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::equiv(
        Formula::implies(p.clone(), q.clone()),
        Formula::implies(Formula::not(q), Formula::not(p)),
    );
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_forall_implies() {
    // (∀x. P(x)) → P(c)
    let x = Term::var("x");
    let c = Term::constant("c");
    let px = Formula::pred("P", vec![x]);
    let pc = Formula::pred("P", vec![c]);

    let goal = Formula::implies(Formula::forall("x", px), pc);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_exists_intro() {
    // P(c) → (∃x. P(x))
    let x = Term::var("x");
    let c = Term::constant("c");
    let px = Formula::pred("P", vec![x]);
    let pc = Formula::pred("P", vec![c]);

    let goal = Formula::implies(pc, Formula::exists("x", px));
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invalid_formula() {
    // P (not a tautology)
    let p = Formula::atom("P");
    assert!(!prove(p));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invalid_implies() {
    // P → Q (not a tautology)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(p, q);
    assert!(!prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_true() {
    assert!(prove(Formula::True));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_not_prove_false() {
    assert!(!prove(Formula::False));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_not_false() {
    // ¬⊥
    assert!(prove(Formula::not(Formula::False)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_syllogism() {
    // ((P → Q) ∧ (Q → R)) → (P → R)
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let r = Formula::atom("R");
    let goal = Formula::implies(
        Formula::and(
            Formula::implies(p.clone(), q.clone()),
            Formula::implies(q, r.clone()),
        ),
        Formula::implies(p, r),
    );
    assert!(prove(goal));
}

// Equality tests

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_eq_reflexivity() {
    // x = x
    let x = Term::var("x");
    let goal = Formula::eq(x.clone(), x);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_eq_reflexivity_const() {
    // c = c
    let c = Term::constant("c");
    let goal = Formula::eq(c.clone(), c);
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_eq_reflexivity_in_context() {
    // P(x) => x = x
    let x = Term::var("x");
    let px = Formula::pred("P", vec![x.clone()]);
    let goal = Formula::implies(px, Formula::eq(x.clone(), x));
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_not_not_eq_refl() {
    // ¬¬(x = x)
    let x = Term::var("x");
    let goal = Formula::not(Formula::not(Formula::eq(x.clone(), x)));
    assert!(prove(goal));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prove_eq_or() {
    // (x = x) ∨ P
    let x = Term::var("x");
    let p = Formula::atom("P");
    let goal = Formula::or(Formula::eq(x.clone(), x), p);
    assert!(prove(goal));
}
