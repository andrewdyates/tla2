// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_decomposition_valid() {
    // Identity decomposition: conclusion matches premise.
    let p = Formula::Predicate("P".to_string(), vec![]);

    let cert = Certificate {
        id: "tableau-decomp-valid".to_string(),
        goal: p.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p.clone(),
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: p.clone(),
                justification: Justification::TableauDecomposition { premise: 100 },
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
fn test_tableau_decomposition_unknown_premise() {
    let p = Formula::Predicate("P".to_string(), vec![]);

    let cert = Certificate {
        id: "tableau-decomp-missing-premise".to_string(),
        goal: p.clone(),
        hypotheses: vec![],
        steps: vec![CertificateStep {
            id: 100,
            formula: p,
            justification: Justification::TableauDecomposition { premise: 42 },
        }],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(
        result,
        VerificationResult::Invalid(VerificationError::UnknownStep(42))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_decomposition_rejects_unrelated_formula() {
    let p = Formula::Predicate("P".to_string(), vec![]);
    let q = Formula::Predicate("Q".to_string(), vec![]);

    let cert = Certificate {
        id: "tableau-decomp-unrelated".to_string(),
        goal: q.clone(),
        hypotheses: vec![p.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p,
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: q,
                justification: Justification::TableauDecomposition { premise: 100 },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(
        result,
        VerificationResult::Invalid(VerificationError::InvalidJustification { step: 101, .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_decomposition_allows_ex_falso_after_contradiction() {
    let p = Formula::Predicate("P".to_string(), vec![]);
    let not_p = Formula::Not(Box::new(p.clone()));
    let q = Formula::Predicate("Q".to_string(), vec![]);

    let cert = Certificate {
        id: "tableau-decomp-ex-falso".to_string(),
        goal: q.clone(),
        hypotheses: vec![p.clone(), not_p.clone()],
        steps: vec![
            CertificateStep {
                id: 100,
                formula: p,
                justification: Justification::Hypothesis(0),
            },
            CertificateStep {
                id: 101,
                formula: not_p,
                justification: Justification::Hypothesis(1),
            },
            CertificateStep {
                id: 102,
                formula: q,
                justification: Justification::TableauDecomposition { premise: 100 },
            },
        ],
        backend: Backend::Zenon,
    };

    let mut checker = CertificateChecker::new();
    let result = checker.verify(&cert);
    assert!(matches!(result, VerificationResult::Valid));
}
