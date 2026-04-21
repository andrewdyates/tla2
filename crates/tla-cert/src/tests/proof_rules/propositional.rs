// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for propositional logic proof rules: hypothesis, modus ponens,
//! and-intro, or-intro, double negation elimination, rewrite.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_proof() {
    // Prove: Given P, prove P
    let p = Formula::Predicate("P".to_string(), vec![]);

    let cert = Certificate {
        id: "test".to_string(),
        goal: p.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![CertificateStep {
            id: 100,
            formula: p.clone(),
            justification: Justification::Hypothesis(0),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_modus_ponens() {
    // Prove: Given P and P => Q, prove Q
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let p_implies_q = Formula::Implies(Box::new(p.clone()), Box::new(q.clone()));

    let cert = Certificate {
        id: "test".to_string(),
        goal: q.clone(),
        hypotheses: vec![p.clone(), p_implies_q.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: p_implies_q.clone(),
                justification: Justification::Hypothesis(1),
            },
            CertificateStep {
                id: 102,
                formula: q.clone(),
                justification: Justification::ModusPonens {
                    premise: 100,
                    implication: 101,
                },
            },
        ],
        backend: Backend::Z3,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_and_intro() {
    // Prove: Given P and Q, prove P ∧ Q
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let p_and_q = Formula::And(Box::new(p.clone()), Box::new(q.clone()));

    let cert = Certificate {
        id: "test".to_string(),
        goal: p_and_q.clone(),
        hypotheses: vec![p.clone(), q.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: q.clone(),
                justification: Justification::Hypothesis(1),
            },
            CertificateStep {
                id: 102,
                formula: p_and_q.clone(),
                justification: Justification::AndIntro {
                    left: 100,
                    right: 101,
                },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invalid_proof() {
    // Invalid: trying to prove Q from P alone
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);

    let cert = Certificate {
        id: "test".to_string(),
        goal: q.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![CertificateStep {
            id: 100,
            formula: p.clone(),
            justification: Justification::Hypothesis(0),
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);

    assert!(matches!(
        result,
        VerificationResult::Invalid(VerificationError::GoalMismatch)
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_or_intro_left() {
    // Prove: Given P, prove P ∨ Q
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let p_or_q = Formula::Or(Box::new(p.clone()), Box::new(q.clone()));

    let cert = Certificate {
        id: "test".to_string(),
        goal: p_or_q.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: p_or_q.clone(),
                justification: Justification::OrIntroLeft {
                    premise: 100,
                    right: q.clone(),
                },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_or_intro_right() {
    // Prove: Given Q, prove P ∨ Q
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);
    let p_or_q = Formula::Or(Box::new(p.clone()), Box::new(q.clone()));

    let cert = Certificate {
        id: "test".to_string(),
        goal: p_or_q.clone(),
        hypotheses: vec![q.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: q.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: p_or_q.clone(),
                justification: Justification::OrIntroRight {
                    left: p.clone(),
                    premise: 100,
                },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_double_neg_elim() {
    // Prove: Given ¬¬P, prove P
    let p = Formula::Predicate("P".to_string(), vec![]);
    let not_p = Formula::Not(Box::new(p.clone()));
    let not_not_p = Formula::Not(Box::new(not_p));

    let cert = Certificate {
        id: "test".to_string(),
        goal: p.clone(),
        hypotheses: vec![not_not_p.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: not_not_p.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: p.clone(),
                justification: Justification::DoubleNegElim { premise: 100 },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_rewrite() {
    // Prove: Given a = b and P(a), derive P(b)
    let a = Term::Const("a".to_string());
    let b = Term::Const("b".to_string());
    let eq_ab = Formula::Eq(a.clone(), b.clone());
    let pa = Formula::Predicate("P".to_string(), vec![a]);
    let pb = Formula::Predicate("P".to_string(), vec![b]);

    let cert = Certificate {
        id: "test".to_string(),
        goal: pb.clone(),
        hypotheses: vec![eq_ab.clone(), pa.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: eq_ab.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: pa.clone(),
                justification: Justification::Hypothesis(1),
            },
            CertificateStep {
                id: 102,
                formula: pb.clone(),
                justification: Justification::Rewrite {
                    equality: 100,
                    target: 101,
                },
            },
        ],
        backend: Backend::Z3,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}
