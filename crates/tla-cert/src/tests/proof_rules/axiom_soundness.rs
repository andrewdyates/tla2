// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Negative axiom tests (soundness): every axiom verifier must REJECT invalid
//! instantiations. Without these, a checker bug could accept unsound proofs.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_weakening_invalid() {
    // P → (Q → R) is NOT weakening when R ≠ P
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let r = Formula::Predicate("R".to_string(), vec![]);
    let q_implies_r = Formula::Implies(Box::new(q), Box::new(r));
    let invalid_weakening = Formula::Implies(Box::new(p), Box::new(q_implies_r));

    let cert = Certificate {
        id: "test".to_string(),
        goal: invalid_weakening.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: invalid_weakening.clone(),
            justification: Justification::Axiom(Axiom::Weakening),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(
        matches!(
            result,
            VerificationResult::Invalid(VerificationError::InvalidAxiom(_))
        ),
        "Weakening should reject P → (Q → R) when R ≠ P, got {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_equality_sym_invalid() {
    // (a = b) → (a = b) is NOT symmetry (should be (a = b) → (b = a))
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let eq_ab = Formula::Eq(a.clone(), b.clone());
    let invalid_sym = Formula::Implies(Box::new(eq_ab.clone()), Box::new(eq_ab));

    let cert = Certificate {
        id: "test".to_string(),
        goal: invalid_sym.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: invalid_sym.clone(),
            justification: Justification::Axiom(Axiom::EqualitySym),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(
        matches!(
            result,
            VerificationResult::Invalid(VerificationError::InvalidAxiom(_))
        ),
        "Symmetry should reject (a = b) → (a = b), got {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_equality_trans_invalid() {
    // (a = b ∧ b = c) → (b = c) is NOT transitivity (should conclude a = c)
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let c = Term::Const("c".to_string());
    let eq_ab = Formula::Eq(a, b.clone());
    let eq_bc = Formula::Eq(b.clone(), c.clone());
    let ante = Formula::And(Box::new(eq_ab), Box::new(eq_bc.clone()));
    let invalid_trans = Formula::Implies(Box::new(ante), Box::new(eq_bc));

    let cert = Certificate {
        id: "test".to_string(),
        goal: invalid_trans.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: invalid_trans.clone(),
            justification: Justification::Axiom(Axiom::EqualityTrans),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(
        matches!(
            result,
            VerificationResult::Invalid(VerificationError::InvalidAxiom(_))
        ),
        "Transitivity should reject (a = b ∧ b = c) → (b = c), got {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_add_zero_invalid() {
    // 1 + a = a is NOT AddZero (should be 0 + a = a)
    let a = Term::Var("a".to_string());
    let one_plus_a = Term::App("+".to_string(), vec![Term::Int(1), a.clone()]);
    let invalid_eq = Formula::Eq(one_plus_a, a);

    let cert = Certificate {
        id: "test".to_string(),
        goal: invalid_eq.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: invalid_eq.clone(),
            justification: Justification::Axiom(Axiom::Arithmetic(ArithmeticAxiom::AddZero)),
        }],
        backend: Backend::Z3,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(
        matches!(
            result,
            VerificationResult::Invalid(VerificationError::InvalidAxiom(_))
        ),
        "AddZero should reject 1 + a = a, got {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_axiom_equality_refl_invalid() {
    // a = b is NOT reflexivity (should be a = a)
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let invalid_refl = Formula::Eq(a, b);

    let cert = Certificate {
        id: "test".to_string(),
        goal: invalid_refl.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: invalid_refl.clone(),
            justification: Justification::Axiom(Axiom::EqualityRefl),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(
        matches!(
            result,
            VerificationResult::Invalid(VerificationError::InvalidAxiom(_))
        ),
        "Reflexivity should reject a = b, got {:?}",
        result
    );
}
