// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Zenon-to-certificate type conversion and basic certificate generation.

use super::super::*;
use crate::formula::{Formula, Term};
use crate::prover::{Prover, ProverConfig};
use tla_cert::{CertificateChecker, Formula as CertFormula};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_term_var() {
    use crate::formula::Term as ZenonTerm;
    let zenon_term = ZenonTerm::Var("x".to_string());
    let cert_term = convert_term(&zenon_term);
    assert!(matches!(cert_term, tla_cert::Term::Var(ref name) if name == "x"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_term_const() {
    use crate::formula::Term as ZenonTerm;
    let zenon_term = ZenonTerm::Const("c".to_string());
    let cert_term = convert_term(&zenon_term);
    assert!(matches!(cert_term, tla_cert::Term::Const(ref name) if name == "c"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_term_app() {
    use crate::formula::Term as ZenonTerm;
    let zenon_term = ZenonTerm::App(
        "f".to_string(),
        vec![
            ZenonTerm::Var("x".to_string()),
            ZenonTerm::Const("c".to_string()),
        ],
    );
    let cert_term = convert_term(&zenon_term);
    if let tla_cert::Term::App(name, args) = cert_term {
        assert_eq!(name, "f");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected App term");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_formula_bool() {
    use crate::formula::Formula as ZenonFormula;
    assert_eq!(
        convert_formula(&ZenonFormula::True),
        CertFormula::Bool(true)
    );
    assert_eq!(
        convert_formula(&ZenonFormula::False),
        CertFormula::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_formula_atom() {
    use crate::formula::Formula as ZenonFormula;
    let zenon = ZenonFormula::Atom("P".to_string());
    let cert = convert_formula(&zenon);
    assert!(
        matches!(cert, CertFormula::Predicate(ref name, ref args) if name == "P" && args.is_empty())
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_formula_pred() {
    use crate::formula::{Formula as ZenonFormula, Term as ZenonTerm};
    let zenon = ZenonFormula::Pred("P".to_string(), vec![ZenonTerm::Var("x".to_string())]);
    let cert = convert_formula(&zenon);
    if let CertFormula::Predicate(name, args) = cert {
        assert_eq!(name, "P");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected Predicate");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_formula_logical() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");

    let and = Formula::and(p.clone(), q.clone());
    let cert_and = convert_formula(&and);
    assert!(matches!(cert_and, CertFormula::And(_, _)));

    let or = Formula::or(p.clone(), q.clone());
    let cert_or = convert_formula(&or);
    assert!(matches!(cert_or, CertFormula::Or(_, _)));

    let not = Formula::not(p.clone());
    let cert_not = convert_formula(&not);
    assert!(matches!(cert_not, CertFormula::Not(_)));

    let implies = Formula::implies(p.clone(), q.clone());
    let cert_implies = convert_formula(&implies);
    assert!(matches!(cert_implies, CertFormula::Implies(_, _)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_formula_quantifiers() {
    let px = Formula::pred("P", vec![Term::var("x")]);

    let forall = Formula::forall("x", px.clone());
    let cert_forall = convert_formula(&forall);
    assert!(matches!(cert_forall, CertFormula::Forall(ref var, _) if var == "x"));

    let exists = Formula::exists("x", px);
    let cert_exists = convert_formula(&exists);
    assert!(matches!(cert_exists, CertFormula::Exists(ref var, _) if var == "x"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proof_to_certificate_simple() {
    let p = Formula::atom("P");
    let goal = Formula::or(p.clone(), Formula::not(p));

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "test".to_string());
        assert_eq!(cert.backend, tla_cert::Backend::Zenon);
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Excluded middle certificate failed verification: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proof_to_certificate_and_elim() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(Formula::and(p.clone(), q), p);

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "and_elim".to_string());
        assert_eq!(cert.id, "and_elim");
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "And-elim certificate failed verification: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proof_to_certificate_double_neg() {
    let p = Formula::atom("P");
    let goal = Formula::implies(Formula::not(Formula::not(p.clone())), p);

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "double_neg".to_string());
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Double negation certificate failed verification: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}
