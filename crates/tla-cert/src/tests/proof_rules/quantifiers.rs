// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for quantifier proof rules: universal instantiation, existential
//! introduction (simple, multi-occurrence, shadowed, invalid), definition.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_universal_instantiation() {
    // Prove: Given ∀x. P(x), derive P(a)
    let x = "x".to_string();
    let a = Term::Const("a".to_string());
    let px = Formula::Predicate("P".to_string(), vec![Term::Var(x.clone())]);
    let pa = Formula::Predicate("P".to_string(), vec![a.clone()]);
    let forall_px = Formula::Forall(x.clone(), Box::new(px));

    let cert = Certificate {
        id: "test".to_string(),
        goal: pa.clone(),
        hypotheses: vec![forall_px.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: forall_px.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: pa.clone(),
                justification: Justification::UniversalInstantiation {
                    forall: 100,
                    term: a,
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
fn test_existential_intro_simple() {
    // From P(a), derive ∃x. P(x)
    let pa = Formula::Predicate("P".to_string(), vec![Term::Const("a".to_string())]);
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let exists_px = Formula::Exists("x".to_string(), Box::new(px));

    let cert = Certificate {
        id: "test".to_string(),
        goal: exists_px.clone(),
        hypotheses: vec![pa.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: pa.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: exists_px.clone(),
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
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_existential_intro_multi_occurrence() {
    // From P(a) ∧ Q(a), derive ∃x. P(x) ∧ Q(x)
    let pa = Formula::Predicate("P".to_string(), vec![Term::Const("a".to_string())]);
    let qa = Formula::Predicate("Q".to_string(), vec![Term::Const("a".to_string())]);
    let witness = Formula::And(Box::new(pa), Box::new(qa));

    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let qx = Formula::Predicate("Q".to_string(), vec![Term::Var("x".to_string())]);
    let exists_body = Formula::And(Box::new(px), Box::new(qx));
    let exists_formula = Formula::Exists("x".to_string(), Box::new(exists_body));

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
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_existential_intro_shadowed_var() {
    // From ∀x. P(x), derive ∃x. ∀x. P(x) (existential var is unused/shadowed)
    let px = Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]);
    let forall_px = Formula::Forall("x".to_string(), Box::new(px));
    let exists_forall_px = Formula::Exists("x".to_string(), Box::new(forall_px.clone()));

    let cert = Certificate {
        id: "test".to_string(),
        goal: exists_forall_px.clone(),
        hypotheses: vec![forall_px.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: forall_px.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: exists_forall_px.clone(),
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
    assert!(matches!(result, VerificationResult::Valid));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_existential_intro_invalid() {
    // Invalid: From P(a), cannot derive ∃x. Q(x)
    let pa = Formula::Predicate("P".to_string(), vec![Term::Const("a".to_string())]);
    let qx = Formula::Predicate("Q".to_string(), vec![Term::Var("x".to_string())]);
    let exists_qx = Formula::Exists("x".to_string(), Box::new(qx));

    let cert = Certificate {
        id: "test".to_string(),
        goal: exists_qx.clone(),
        hypotheses: vec![pa.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: pa.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: exists_qx.clone(),
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
    assert!(matches!(
        result,
        VerificationResult::Invalid(VerificationError::InvalidJustification { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_definition() {
    // Prove P using a definition
    let p = Formula::Predicate("P".to_string(), vec![]);

    let cert = Certificate {
        id: "test".to_string(),
        goal: p.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: p.clone(),
            justification: Justification::Definition {
                name: "MyDef".to_string(),
            },
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    checker.add_definition("MyDef".to_string(), p.clone());
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}
