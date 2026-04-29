// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Round-trip certificate verification tests and regression tests.

use super::super::*;
use crate::formula::Formula;
use crate::proof::ProofRule;
use crate::prover::{Prover, ProverConfig};
use tla_cert::{CertificateChecker, Formula as CertFormula, Justification};

fn find_rule_node<'a, F>(
    node: &'a crate::proof::ProofNode,
    predicate: &F,
) -> Option<&'a crate::proof::ProofNode>
where
    F: Fn(&ProofRule) -> bool,
{
    if predicate(&node.rule) {
        return Some(node);
    }
    for child in &node.children {
        if let Some(found) = find_rule_node(child, predicate) {
            return Some(found);
        }
    }
    None
}

fn find_step_id(cert: &tla_cert::Certificate, formula: &CertFormula) -> tla_cert::StepId {
    cert.steps
        .iter()
        .find(|step| step.formula == *formula)
        .map(|step| step.id)
        .expect("formula should be present in certificate")
}

fn assert_rule_conclusions_reference_principal<F>(
    proof: &crate::proof::Proof,
    cert: &tla_cert::Certificate,
    predicate: F,
) where
    F: Fn(&ProofRule) -> bool,
{
    let rule_node = find_rule_node(&proof.tree, &predicate).expect("target rule must appear");
    let principal = rule_node
        .rule
        .principal()
        .expect("target rule should have principal formula");
    let principal_step = find_step_id(cert, &convert_formula(principal));

    for conclusion in &rule_node.conclusions {
        let conclusion_formula = convert_formula(conclusion);
        let conclusion_step = cert
            .steps
            .iter()
            .find(|step| step.formula == conclusion_formula)
            .expect("rule conclusion should be present in certificate");
        match conclusion_step.justification {
            Justification::TableauDecomposition { premise } => {
                assert_eq!(
                    premise, principal_step,
                    "conclusion {:?} should reference principal step",
                    conclusion
                );
            }
            _ => panic!(
                "conclusion {:?} should use TableauDecomposition",
                conclusion
            ),
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_verifiable() {
    let p = Formula::atom("P");
    let goal = Formula::implies(p.clone(), p);

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "identity".to_string());
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Certificate verification failed: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_round_trip_excluded_middle() {
    let p = Formula::atom("P");
    let goal = Formula::or(p.clone(), Formula::not(p));

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "excl_mid".to_string());
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Excluded middle certificate failed: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_round_trip_and_elim_verify() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(Formula::and(p.clone(), q), p);

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "and_elim_verify".to_string());
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "And-elim certificate failed: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_round_trip_double_neg_verify() {
    let p = Formula::atom("P");
    let goal = Formula::implies(Formula::not(Formula::not(p.clone())), p);

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "double_neg_verify".to_string());
        assert!(!cert.steps.is_empty());

        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Double negation certificate failed: {:?}",
            verification.error(),
        );
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_notimplies_rule_chain() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(
        Formula::not(Formula::implies(p.clone(), q.clone())),
        Formula::and(p.clone(), Formula::not(q.clone())),
    );

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "not_implies_chain".to_string());
        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "NotImplies certificate should verify: {:?}",
            verification.error(),
        );

        assert_rule_conclusions_reference_principal(&proof, &cert, |rule| {
            matches!(rule, ProofRule::NotImplies(_))
        });
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_notor_rule_chain() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(
        Formula::not(Formula::or(p.clone(), q.clone())),
        Formula::and(Formula::not(p.clone()), Formula::not(q.clone())),
    );

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "not_or_chain".to_string());
        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "NotOr certificate should verify: {:?}",
            verification.error(),
        );

        assert_rule_conclusions_reference_principal(&proof, &cert, |rule| {
            matches!(rule, ProofRule::NotOr(_))
        });
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_equivelim_rule_chain() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(
        Formula::equiv(p.clone(), q.clone()),
        Formula::and(
            Formula::implies(p.clone(), q.clone()),
            Formula::implies(q.clone(), p.clone()),
        ),
    );

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "equiv_elim_chain".to_string());
        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "EquivElim certificate should verify: {:?}",
            verification.error(),
        );

        assert_rule_conclusions_reference_principal(&proof, &cert, |rule| {
            matches!(rule, ProofRule::EquivElim(_))
        });
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_false_elim_uses_branch_not_true_premise() {
    // Regression test for sibling-branch premise contamination (#1241).
    use crate::proof::{Proof, ProofNode, ProofRule};

    let l = Formula::atom("L");
    let not_true = Formula::not(Formula::True);
    let goal = Formula::or(l.clone(), not_true.clone());

    let proof = Proof {
        goal: goal.clone(),
        tree: ProofNode {
            rule: ProofRule::Refute(goal.clone()),
            conclusions: vec![Formula::not(goal)],
            children: vec![ProofNode {
                rule: ProofRule::OrElim(Formula::or(l.clone(), not_true.clone())),
                conclusions: vec![],
                children: vec![
                    ProofNode {
                        rule: ProofRule::TrueIntro,
                        conclusions: vec![l.clone()],
                        children: vec![ProofNode {
                            rule: ProofRule::Close(l.clone(), Formula::not(l.clone())),
                            conclusions: vec![],
                            children: vec![],
                        }],
                    },
                    ProofNode {
                        rule: ProofRule::FalseElim,
                        conclusions: vec![not_true.clone()],
                        children: vec![],
                    },
                ],
            }],
        },
    };

    let cert = proof_to_certificate(&proof, "false_elim_branch".to_string());

    let false_formula = CertFormula::Bool(false);
    let false_step = cert.steps.iter().find(|step| step.formula == false_formula);

    if let Some(step) = false_step {
        let not_true_cert = CertFormula::Not(Box::new(CertFormula::Bool(true)));
        let not_true_step_id = cert
            .steps
            .iter()
            .find(|s| s.formula == not_true_cert)
            .map(|s| s.id);

        if let (Justification::TableauDecomposition { premise }, Some(expected_premise)) =
            (&step.justification, not_true_step_id)
        {
            assert_eq!(
                *premise, expected_premise,
                "FalseElim should decompose the branch's ¬True formula, not a sibling step"
            );
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_beta_split_right_branch_premise() {
    let p = Formula::atom("P");
    let q = Formula::atom("Q");
    let goal = Formula::implies(
        Formula::implies(p.clone(), q.clone()),
        Formula::or(Formula::not(p.clone()), q.clone()),
    );

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "beta_split_right".to_string());
        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "Beta-split right branch certificate should verify: {:?}",
            verification.error(),
        );

        if let Some(node) = find_rule_node(&proof.tree, &|rule| {
            matches!(rule, ProofRule::ImpliesElim(_))
        }) {
            let principal = node.rule.principal().unwrap();
            let principal_cert = convert_formula(principal);
            let principal_step_id = find_step_id(&cert, &principal_cert);

            for conclusion in &node.conclusions {
                let cert_conc = convert_formula(conclusion);
                if let Some(step) = cert.steps.iter().find(|s| s.formula == cert_conc) {
                    if let Justification::TableauDecomposition { premise } = &step.justification {
                        assert_eq!(
                            *premise, principal_step_id,
                            "Conclusion {:?} should reference ImpliesElim principal, not sibling",
                            conclusion
                        );
                    }
                }
            }
        }
    } else {
        panic!("Expected valid proof");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_certificate_forall_elim_uses_instantiation_term() {
    use crate::formula::Term;

    let goal = Formula::implies(
        Formula::forall("x", Formula::pred("P", vec![Term::var("x")])),
        Formula::pred("P", vec![Term::constant("c0")]),
    );

    let mut prover = Prover::new();
    let result = prover.prove(&goal, ProverConfig::default());

    if let crate::prover::ProofResult::Valid(proof) = result {
        let cert = proof_to_certificate(&proof, "forall_elim_term".to_string());
        let mut checker = CertificateChecker::new();
        let verification = checker.verify(&cert);
        assert!(
            verification.is_valid(),
            "ForallElim certificate should verify: {:?}",
            verification.error(),
        );

        let rule_node = find_rule_node(&proof.tree, &|rule| {
            matches!(rule, ProofRule::ForallElim(_, _))
        })
        .expect("ForallElim node must appear in proof");

        let (principal_formula, rule_term) = match &rule_node.rule {
            ProofRule::ForallElim(formula, term) => (formula, term),
            _ => panic!("expected ForallElim rule"),
        };

        let principal_step = find_step_id(&cert, &convert_formula(principal_formula));
        let conclusion = rule_node
            .conclusions
            .first()
            .expect("ForallElim should derive one conclusion");
        let conclusion_step = cert
            .steps
            .iter()
            .find(|step| step.formula == convert_formula(conclusion))
            .expect("ForallElim conclusion should be present in certificate");

        match &conclusion_step.justification {
            Justification::UniversalInstantiation { forall, term } => {
                assert_eq!(
                    *forall, principal_step,
                    "UniversalInstantiation should reference Forall premise"
                );
                assert_eq!(
                    *term,
                    convert_term(rule_term),
                    "UniversalInstantiation should use the rule instantiation term"
                );
            }
            other => panic!(
                "ForallElim conclusion should use UniversalInstantiation, got {:?}",
                other
            ),
        }
    } else {
        panic!("Expected valid proof");
    }
}
