// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_simple() {
    // ∀x. P(x) ≡ ∀y. P(y)
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let py = Formula::Predicate("P".to_string(), vec![Term::Var("y".to_string())]);
    let forall_x_px = Formula::Forall("x".to_string(), Box::new(px));
    let forall_y_py = Formula::Forall("y".to_string(), Box::new(py));

    assert!(alpha_equiv(&forall_x_px, &forall_y_py));
    assert!(alpha_equiv(&forall_y_py, &forall_x_px)); // symmetric
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_exists() {
    // ∃x. Q(x) ≡ ∃z. Q(z)
    let qx = Formula::Predicate("Q".to_string(), vec![Term::Var("x".to_string())]);
    let qz = Formula::Predicate("Q".to_string(), vec![Term::Var("z".to_string())]);
    let exists_x_qx = Formula::Exists("x".to_string(), Box::new(qx));
    let exists_z_qz = Formula::Exists("z".to_string(), Box::new(qz));

    assert!(alpha_equiv(&exists_x_qx, &exists_z_qz));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_nested() {
    // ∀x. ∃y. R(x, y) ≡ ∀a. ∃b. R(a, b)
    let rxy = Formula::Predicate(
        "R".to_string(),
        vec![Term::Var("x".to_string()), Term::Var("y".to_string())],
    );
    let rab = Formula::Predicate(
        "R".to_string(),
        vec![Term::Var("a".to_string()), Term::Var("b".to_string())],
    );

    let f1 = Formula::Forall(
        "x".to_string(),
        Box::new(Formula::Exists("y".to_string(), Box::new(rxy))),
    );
    let f2 = Formula::Forall(
        "a".to_string(),
        Box::new(Formula::Exists("b".to_string(), Box::new(rab))),
    );

    assert!(alpha_equiv(&f1, &f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_not_equiv_different_structure() {
    // ∀x. P(x) ≢ ∃x. P(x)
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let forall_x_px = Formula::Forall("x".to_string(), Box::new(px.clone()));
    let exists_x_px = Formula::Exists("x".to_string(), Box::new(px));

    assert!(!alpha_equiv(&forall_x_px, &exists_x_px));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_not_equiv_free_vars() {
    // P(x) ≢ P(y) (free variables must match)
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let py = Formula::Predicate("P".to_string(), vec![Term::Var("y".to_string())]);

    assert!(!alpha_equiv(&px, &py));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_with_free_and_bound() {
    // ∀x. R(x, z) ≡ ∀y. R(y, z) (z is free in both, x/y are bound)
    let rxz = Formula::Predicate(
        "R".to_string(),
        vec![Term::Var("x".to_string()), Term::Var("z".to_string())],
    );
    let ryz = Formula::Predicate(
        "R".to_string(),
        vec![Term::Var("y".to_string()), Term::Var("z".to_string())],
    );

    let f1 = Formula::Forall("x".to_string(), Box::new(rxz));
    let f2 = Formula::Forall("y".to_string(), Box::new(ryz));

    assert!(alpha_equiv(&f1, &f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_shadowing() {
    // ∀x. ∀x. P(x) ≡ ∀y. ∀z. P(z) (inner binding shadows outer)
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let pz = Formula::Predicate("P".to_string(), vec![Term::Var("z".to_string())]);

    let f1 = Formula::Forall(
        "x".to_string(),
        Box::new(Formula::Forall("x".to_string(), Box::new(px))),
    );
    let f2 = Formula::Forall(
        "y".to_string(),
        Box::new(Formula::Forall("z".to_string(), Box::new(pz))),
    );

    assert!(alpha_equiv(&f1, &f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_complex_formula() {
    // (∀x. P(x)) ∧ (∃y. Q(y)) ≡ (∀a. P(a)) ∧ (∃b. Q(b))
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let pa = Formula::Predicate("P".to_string(), vec![Term::Var("a".to_string())]);
    let qy = Formula::Predicate("Q".to_string(), vec![Term::Var("y".to_string())]);
    let qb = Formula::Predicate("Q".to_string(), vec![Term::Var("b".to_string())]);

    let f1 = Formula::And(
        Box::new(Formula::Forall("x".to_string(), Box::new(px))),
        Box::new(Formula::Exists("y".to_string(), Box::new(qy))),
    );
    let f2 = Formula::And(
        Box::new(Formula::Forall("a".to_string(), Box::new(pa))),
        Box::new(Formula::Exists("b".to_string(), Box::new(qb))),
    );

    assert!(alpha_equiv(&f1, &f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alpha_equiv_function_app() {
    // ∀x. f(x, x) = g(x) ≡ ∀y. f(y, y) = g(y)
    let fxx = Term::App(
        "f".to_string(),
        vec![Term::Var("x".to_string()), Term::Var("x".to_string())],
    );
    let fyy = Term::App(
        "f".to_string(),
        vec![Term::Var("y".to_string()), Term::Var("y".to_string())],
    );
    let gx = Term::App("g".to_string(), vec![Term::Var("x".to_string())]);
    let gy = Term::App("g".to_string(), vec![Term::Var("y".to_string())]);

    let f1 = Formula::Forall("x".to_string(), Box::new(Formula::Eq(fxx, gx)));
    let f2 = Formula::Forall("y".to_string(), Box::new(Formula::Eq(fyy, gy)));

    assert!(alpha_equiv(&f1, &f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_goal_check_with_alpha_equiv() {
    // Certificate where goal uses different variable name than final step
    // Goal: ∀y. P(y)
    // Final step proves: ∀x. P(x)
    // These should be considered equivalent

    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let py = Formula::Predicate("P".to_string(), vec![Term::Var("y".to_string())]);
    let forall_x_px = Formula::Forall("x".to_string(), Box::new(px));
    let forall_y_py = Formula::Forall("y".to_string(), Box::new(py));

    // Axiom: P → (Q → P) gives us a formula with any P, including ∀x.P(x)
    let cert = Certificate {
        id: "alpha-equiv-goal".to_string(),
        goal: forall_y_py.clone(),             // Goal uses y
        hypotheses: vec![forall_x_px.clone()], // Hypothesis uses x
        steps: vec![CertificateStep {
            id: 100,
            formula: forall_x_px.clone(), // Final step uses x
            justification: Justification::Hypothesis(0),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    // Should pass due to alpha-equivalence
    assert!(result.is_valid());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_existential_intro_with_alpha_renamed_inner() {
    // From P(a) ∧ ∀y. Q(y), derive ∃x. P(x) ∧ ∀z. Q(z)
    // The inner quantifier uses different variable name (y vs z)

    let pa = Formula::Predicate("P".to_string(), vec![Term::Const("a".to_string())]);
    let qy = Formula::Predicate("Q".to_string(), vec![Term::Var("y".to_string())]);
    let forall_y_qy = Formula::Forall("y".to_string(), Box::new(qy));
    let witness = Formula::And(Box::new(pa), Box::new(forall_y_qy));

    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let qz = Formula::Predicate("Q".to_string(), vec![Term::Var("z".to_string())]);
    let forall_z_qz = Formula::Forall("z".to_string(), Box::new(qz));
    let body = Formula::And(Box::new(px), Box::new(forall_z_qz));
    let exists_formula = Formula::Exists("x".to_string(), Box::new(body));

    let cert = Certificate {
        id: "test".to_string(),
        goal: exists_formula.clone(),
        hypotheses: vec![witness.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: witness.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: exists_formula.clone(),
                justification: Justification::ExistentialIntro {
                    witness: 100,
                    variable: "x".to_string(),
                },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    // Should pass due to alpha-equivalence of inner quantifiers
    assert!(
        result.is_valid(),
        "Expected valid, got: {:?}",
        result.error()
    );
}
