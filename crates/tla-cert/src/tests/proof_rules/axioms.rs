// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for positive axiom verification: weakening, equality symmetry,
//! equality transitivity, add-zero, add-commutativity.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_weakening() {
    // P → (Q → P) is an axiom
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let q_implies_p = Formula::Implies(Box::new(q), Box::new(p.clone()));
    let weakening = Formula::Implies(Box::new(p), Box::new(q_implies_p));

    let cert = Certificate {
        id: "test".to_string(),
        goal: weakening.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: weakening.clone(),
            justification: Justification::Axiom(Axiom::Weakening),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_equality_sym() {
    // (a = b) → (b = a) is an axiom
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let eq_ab = Formula::Eq(a.clone(), b.clone());
    let eq_ba = Formula::Eq(b, a);
    let sym = Formula::Implies(Box::new(eq_ab), Box::new(eq_ba));

    let cert = Certificate {
        id: "test".to_string(),
        goal: sym.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: sym.clone(),
            justification: Justification::Axiom(Axiom::EqualitySym),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_equality_trans() {
    // (a = b ∧ b = c) → (a = c) is an axiom
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let c = Term::Const("c".to_string());
    let eq_ab = Formula::Eq(a.clone(), b.clone());
    let eq_bc = Formula::Eq(b, c.clone());
    let eq_ac = Formula::Eq(a, c);
    let ante = Formula::And(Box::new(eq_ab), Box::new(eq_bc));
    let trans = Formula::Implies(Box::new(ante), Box::new(eq_ac));

    let cert = Certificate {
        id: "test".to_string(),
        goal: trans.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: trans.clone(),
            justification: Justification::Axiom(Axiom::EqualityTrans),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_add_zero() {
    // 0 + a = a is an arithmetic axiom
    let a = Term::Var("a".to_string());
    let zero_plus_a = Term::App("+".to_string(), vec![Term::Int(0), a.clone()]);
    let eq = Formula::Eq(zero_plus_a, a);

    let cert = Certificate {
        id: "test".to_string(),
        goal: eq.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: eq.clone(),
            justification: Justification::Axiom(Axiom::Arithmetic(ArithmeticAxiom::AddZero)),
        }],
        backend: Backend::Z3,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_add_comm() {
    // a + b = b + a is an arithmetic axiom
    let a = Term::Var("a".to_string());
    let b = Term::Var("b".to_string());
    let a_plus_b = Term::App("+".to_string(), vec![a.clone(), b.clone()]);
    let b_plus_a = Term::App("+".to_string(), vec![b, a]);
    let eq = Formula::Eq(a_plus_b, b_plus_a);

    let cert = Certificate {
        id: "test".to_string(),
        goal: eq.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: eq.clone(),
            justification: Justification::Axiom(Axiom::Arithmetic(ArithmeticAxiom::AddComm)),
        }],
        backend: Backend::Z3,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}
