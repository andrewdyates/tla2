// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_json_roundtrip() {
    let p = Formula::Predicate("P".to_string(), vec![Term::Const("a".to_string())]);
    let q = Formula::Predicate("Q".to_string(), vec![Term::Var("x".to_string())]);
    let p_and_q = Formula::And(Box::new(p.clone()), Box::new(q.clone()));

    let cert = Certificate {
        id: "roundtrip-test".to_string(),
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

    // Serialize to JSON
    let json = cert.to_json().expect("serialization failed");

    // Deserialize back
    let restored = Certificate::from_json(&json).expect("deserialization failed");

    // Verify fields match
    assert_eq!(cert.id, restored.id);
    assert_eq!(cert.goal, restored.goal);
    assert_eq!(cert.hypotheses, restored.hypotheses);
    assert_eq!(cert.steps.len(), restored.steps.len());
    assert_eq!(cert.backend, restored.backend);

    // Verify the restored certificate still verifies
    let mut checker = CertificateChecker::new();
    let result = checker.verify(&restored);
    assert!(result.is_valid());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_json_pretty() {
    let p = Formula::Bool(true);
    let cert = Certificate {
        id: "pretty-test".to_string(),
        goal: p.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![CertificateStep {
            id: 0,
            formula: p,
            justification: Justification::Hypothesis(0),
        }],
        backend: Backend::Z3,
    };

    let pretty_json = cert.to_json_pretty().expect("pretty serialization failed");

    // Pretty JSON should contain newlines
    assert!(pretty_json.contains('\n'));

    // Should still deserialize correctly
    let restored = Certificate::from_json(&pretty_json).expect("deserialization failed");
    assert_eq!(cert.id, restored.id);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_justification_variants_serialize() {
    // Test that all Justification variants can serialize/deserialize
    let justifications = vec![
        Justification::Axiom(Axiom::ExcludedMiddle(Formula::Bool(true))),
        Justification::Hypothesis(0),
        Justification::ModusPonens {
            premise: 1,
            implication: 2,
        },
        Justification::UniversalInstantiation {
            forall: 1,
            term: Term::Const("c".to_string()),
        },
        Justification::ExistentialIntro {
            witness: 1,
            variable: "x".to_string(),
        },
        Justification::Definition {
            name: "Def1".to_string(),
        },
        Justification::AndIntro { left: 1, right: 2 },
        Justification::AndElimLeft { conjunction: 1 },
        Justification::AndElimRight { conjunction: 1 },
        Justification::OrIntroLeft {
            premise: 1,
            right: Formula::Bool(false),
        },
        Justification::OrIntroRight {
            left: Formula::Bool(true),
            premise: 1,
        },
        Justification::DoubleNegElim { premise: 1 },
        Justification::Rewrite {
            equality: 1,
            target: 2,
        },
    ];

    for just in justifications {
        let json = serde_json::to_string(&just).expect("serialization failed");
        let restored: Justification = serde_json::from_str(&json).expect("deserialization failed");
        // Compare debug representations since Justification doesn't impl Eq
        assert_eq!(format!("{:?}", just), format!("{:?}", restored));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_axiom_variants_serialize() {
    let axioms = vec![
        Axiom::ExcludedMiddle(Formula::Bool(true)),
        Axiom::Identity(Formula::Bool(false)),
        Axiom::Weakening,
        Axiom::EqualityRefl,
        Axiom::EqualitySym,
        Axiom::EqualityTrans,
        Axiom::Arithmetic(ArithmeticAxiom::AddZero),
        Axiom::Arithmetic(ArithmeticAxiom::AddComm),
        Axiom::Arithmetic(ArithmeticAxiom::AddAssoc),
        Axiom::Arithmetic(ArithmeticAxiom::MulOne),
        Axiom::Arithmetic(ArithmeticAxiom::MulZero),
        Axiom::SetTheory(SetAxiom::EmptySet),
        Axiom::SetTheory(SetAxiom::Singleton),
        Axiom::SetTheory(SetAxiom::Union),
        Axiom::SetTheory(SetAxiom::Intersection),
    ];

    for axiom in axioms {
        let json = serde_json::to_string(&axiom).expect("serialization failed");
        let restored: Axiom = serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(format!("{:?}", axiom), format!("{:?}", restored));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_formula_variants_serialize() {
    let formulas = vec![
        Formula::Bool(true),
        Formula::Predicate("P".to_string(), vec![Term::Var("x".to_string())]),
        Formula::Not(Box::new(Formula::Bool(false))),
        Formula::And(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
        ),
        Formula::Or(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
        ),
        Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
        ),
        Formula::Equiv(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true))),
        Formula::Forall("x".to_string(), Box::new(Formula::Bool(true))),
        Formula::Exists("y".to_string(), Box::new(Formula::Bool(false))),
        Formula::Eq(Term::Var("a".to_string()), Term::Var("b".to_string())),
    ];

    for formula in formulas {
        let json = serde_json::to_string(&formula).expect("serialization failed");
        let restored: Formula = serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(formula, restored);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_term_variants_serialize() {
    let terms = vec![
        Term::Var("x".to_string()),
        Term::Const("c".to_string()),
        Term::Int(42),
        Term::Int(-100),
        Term::App("f".to_string(), vec![Term::Var("x".to_string())]),
        Term::App(
            "+".to_string(),
            vec![Term::Int(1), Term::Int(2), Term::Int(3)],
        ),
    ];

    for term in terms {
        let json = serde_json::to_string(&term).expect("serialization failed");
        let restored: Term = serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(term, restored);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_backend_variants_serialize() {
    let backends = vec![Backend::Zenon, Backend::Z3, Backend::CVC5, Backend::Lean4];

    for backend in backends {
        let json = serde_json::to_string(&backend).expect("serialization failed");
        let restored: Backend = serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(backend, restored);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_verification_result_serialize() {
    let valid = VerificationResult::Valid;
    let invalid = VerificationResult::Invalid(VerificationError::GoalMismatch);
    let invalid_step = VerificationResult::Invalid(VerificationError::UnknownStep(42));

    for result in [valid, invalid, invalid_step] {
        let json = serde_json::to_string(&result).expect("serialization failed");
        let restored: VerificationResult =
            serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(format!("{:?}", result), format!("{:?}", restored));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_complex_certificate_roundtrip() {
    // Build a more complex certificate with nested structures
    let x = Term::Var("x".to_string());
    let a = Term::Const("a".to_string());
    let px = Formula::Predicate("P".to_string(), vec![x.clone()]);
    let pa = Formula::Predicate("P".to_string(), vec![a.clone()]);
    let forall_px = Formula::Forall("x".to_string(), Box::new(px));
    let exists_pa = Formula::Exists("y".to_string(), Box::new(pa.clone()));

    let nested = Formula::Implies(
        Box::new(forall_px.clone()),
        Box::new(Formula::And(
            Box::new(pa.clone()),
            Box::new(exists_pa.clone()),
        )),
    );

    let cert = Certificate {
        id: "complex-test-αβγ".to_string(), // Unicode in ID
        goal: nested.clone(),
        hypotheses: vec![forall_px.clone()],
        steps: vec![
            CertificateStep {
                id: 0,
                formula: forall_px.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 1,
                formula: pa.clone(),
                justification: Justification::UniversalInstantiation {
                    forall: 0,
                    term: a.clone(),
                },
            },
        ],
        backend: Backend::Zenon,
    };

    let json = cert.to_json_pretty().expect("serialization failed");
    let restored = Certificate::from_json(&json).expect("deserialization failed");

    assert_eq!(cert.id, restored.id);
    assert_eq!(cert.goal, restored.goal);
    assert_eq!(cert.hypotheses.len(), restored.hypotheses.len());
    assert_eq!(cert.steps.len(), restored.steps.len());
}
