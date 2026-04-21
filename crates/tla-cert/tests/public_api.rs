// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_cert::{
    alpha_equiv, ArithmeticAxiom, Axiom, Backend, Certificate, CertificateIoError, CertificateStep,
    Formula, Justification, SetAxiom, StepId, Term, VerificationError, VerificationResult,
};

#[test]
fn root_reexports_cover_certificate_api() {
    let term = Term::Const("a".to_string());
    let formula = Formula::Eq(term.clone(), term);
    let step_id: StepId = 1;
    let step = CertificateStep {
        id: step_id,
        formula: formula.clone(),
        justification: Justification::Axiom(Axiom::Arithmetic(ArithmeticAxiom::AddZero)),
    };
    let cert = Certificate {
        id: "api".to_string(),
        goal: formula,
        hypotheses: Vec::new(),
        steps: vec![step],
        backend: Backend::Zenon,
    };

    assert_eq!(cert.steps.len(), 1);
    assert!(matches!(SetAxiom::EmptySet, SetAxiom::EmptySet));
    assert!(matches!(
        VerificationResult::Invalid(VerificationError::GoalMismatch),
        VerificationResult::Invalid(VerificationError::GoalMismatch)
    ));

    let io_err = std::io::Error::other("io");
    let _cert_io_err: CertificateIoError = io_err.into();
}

#[test]
fn alpha_equiv_reexport_handles_bound_var_renaming() {
    let f1 = Formula::Forall(
        "x".to_string(),
        Box::new(Formula::Predicate(
            "P".to_string(),
            vec![Term::Var("x".to_string())],
        )),
    );
    let f2 = Formula::Forall(
        "y".to_string(),
        Box::new(Formula::Predicate(
            "P".to_string(),
            vec![Term::Var("y".to_string())],
        )),
    );
    let non_equiv = Formula::Forall(
        "y".to_string(),
        Box::new(Formula::Predicate(
            "P".to_string(),
            vec![Term::Var("z".to_string())],
        )),
    );

    assert!(alpha_equiv(&f1, &f2));
    assert!(!alpha_equiv(&f1, &non_equiv));
}
