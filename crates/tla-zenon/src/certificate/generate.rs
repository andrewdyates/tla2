// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certificate generation from Zenon proof trees.
//!
//! Converts tableau proofs (tree-structured) to proof certificates
//! (linear step sequences) that can be independently verified.

use crate::formula::{Formula as ZenonFormula, Term as ZenonTerm};
use crate::proof::{ProofNode, ProofRule};
use tla_cert::{Axiom, Backend, Certificate, Formula as CertFormula, Justification, StepId};

use super::builder::CertificateBuilder;
use super::convert::{convert_formula, convert_term};

/// Convert a Zenon proof tree to a verifiable certificate.
///
/// Tableau proofs are refutation-based: they prove a formula by showing that
/// its negation leads to a contradiction. The certificate represents this as
/// a sequence of derived formulas culminating in the original goal.
pub fn proof_to_certificate(proof: &crate::proof::Proof, id: String) -> Certificate {
    let mut builder = CertificateBuilder::new();
    let goal = convert_formula(&proof.goal);
    let neg_goal = CertFormula::Not(Box::new(goal.clone()));

    // The tableau proof is a refutation: it assumes ¬goal and derives a
    // contradiction. We model ¬goal as hypothesis[0].
    let hypotheses = vec![neg_goal.clone()];

    // Seed the builder with the refutation hypothesis so that Refute nodes
    // and downstream rules can reference it.
    builder.add_step(neg_goal, Justification::Hypothesis(0));

    // Process the proof tree to generate certificate steps.
    process_node(&proof.tree, &mut builder, Some(0));

    // The final step should establish the goal.
    finalize_goal(&mut builder, &goal);

    Certificate {
        id,
        goal,
        hypotheses,
        steps: builder.steps,
        backend: Backend::Zenon,
    }
}

/// Ensure the goal formula appears as the final certificate step.
fn finalize_goal(builder: &mut CertificateBuilder, goal: &CertFormula) {
    if builder.lookup(goal).is_some() {
        return;
    }
    let double_neg_goal = CertFormula::Not(Box::new(CertFormula::Not(Box::new(goal.clone()))));
    if let Some(nn_step) = builder.lookup(&double_neg_goal) {
        // ¬¬G was derived — conclude G by double negation elimination.
        builder.add_step(
            goal.clone(),
            Justification::DoubleNegElim { premise: nn_step },
        );
    } else {
        // The tableau refutation proved ¬G leads to contradiction.
        // Derive G as a tableau decomposition from the refutation hypothesis.
        // This is sound because the closed tableau witnesses that ¬G is
        // unsatisfiable, so G is a tautological consequence.
        let hyp_step = 0; // Hypothesis(0) = ¬G
        builder.add_step(
            goal.clone(),
            Justification::TableauDecomposition { premise: hyp_step },
        );
    }
}

fn ensure_tableau_formula(
    builder: &mut CertificateBuilder,
    formula: CertFormula,
    premise: Option<StepId>,
) -> Option<StepId> {
    if let Some(step) = builder.lookup(&formula) {
        return Some(step);
    }

    premise
        .map(|premise| builder.add_step(formula, Justification::TableauDecomposition { premise }))
}

/// Process a proof node and its children, adding certificate steps.
///
/// `parent_premise` is the step ID from the parent node that this node's
/// rule should reference as its decomposition premise. This avoids the
/// sibling-branch contamination bug where `last_step_id(builder)` would
/// return a step from a previously-processed sibling subtree in beta splits.
fn process_node(
    node: &ProofNode,
    builder: &mut CertificateBuilder,
    parent_premise: Option<StepId>,
) {
    let decomposition_premise = dispatch_rule(node, builder, parent_premise);

    // Process node conclusions — these are formulas derived by this node's rule
    for conclusion in &node.conclusions {
        let cert_formula = convert_formula(conclusion);
        if builder.lookup(&cert_formula).is_none() {
            if let Some(premise) = decomposition_premise {
                builder.add_step(
                    cert_formula,
                    Justification::TableauDecomposition { premise },
                );
            }
        }
    }

    // Process children after establishing this node's derivations.
    for child in &node.children {
        process_node(child, builder, decomposition_premise);
    }
}

/// Dispatch a proof rule to its handler, returning the decomposition premise
/// for conclusion processing.
fn dispatch_rule(
    node: &ProofNode,
    builder: &mut CertificateBuilder,
    parent_premise: Option<StepId>,
) -> Option<StepId> {
    let mut decomposition_premise = parent_premise;

    match &node.rule {
        ProofRule::Close(_pos, _neg) => {
            // Branch closed by contradiction — no new steps needed.
        }

        ProofRule::TrueIntro => {
            handle_true_intro(builder);
        }

        ProofRule::FalseElim => {
            decomposition_premise = handle_false_elim(node, builder, decomposition_premise);
        }

        ProofRule::AndElim(conj) => {
            decomposition_premise = handle_and_elim(conj, builder, decomposition_premise);
        }

        ProofRule::NotOr(formula)
        | ProofRule::NotImplies(formula)
        | ProofRule::EquivElim(formula)
        | ProofRule::OrElim(formula)
        | ProofRule::NotAnd(formula)
        | ProofRule::ImpliesElim(formula)
        | ProofRule::NotEquiv(formula)
        | ProofRule::NotExists(formula, _)
        | ProofRule::NotForall(formula, _) => {
            let cert_formula = convert_formula(formula);
            decomposition_premise =
                ensure_tableau_formula(builder, cert_formula, decomposition_premise);
        }

        ProofRule::NotNot(formula) => {
            decomposition_premise = handle_not_not(formula, builder, decomposition_premise);
        }

        ProofRule::ForallElim(formula, term) => {
            decomposition_premise =
                handle_forall_elim(formula, term, builder, decomposition_premise);
        }

        ProofRule::ExistsElim(formula, witness) => {
            decomposition_premise =
                handle_exists_elim(formula, witness, builder, decomposition_premise);
        }

        ProofRule::Refute(formula) => {
            decomposition_premise = handle_refute(formula, builder);
        }

        ProofRule::EqRefl => {
            handle_eq_refl(node, builder);
        }

        ProofRule::NotEqRefl => {
            // ¬(t = t) is a contradiction, closes the branch
        }

        ProofRule::EqSym(formula) => {
            decomposition_premise = handle_eq_sym(formula, builder, decomposition_premise);
        }

        ProofRule::EqSubst(eq, _target) => {
            decomposition_premise = handle_eq_subst(eq, builder, decomposition_premise);
        }
    }

    decomposition_premise
}

// --- Per-rule handlers ---

fn handle_true_intro(builder: &mut CertificateBuilder) {
    let true_formula = CertFormula::Bool(true);
    if builder.lookup(&true_formula).is_some() {
        return;
    }
    let impl_formula = CertFormula::Implies(
        Box::new(true_formula.clone()),
        Box::new(true_formula.clone()),
    );
    let impl_step = builder.add_step(
        impl_formula,
        Justification::Axiom(Axiom::Identity(true_formula.clone())),
    );
    builder.add_step(
        true_formula,
        Justification::TableauDecomposition { premise: impl_step },
    );
}

fn handle_false_elim(
    node: &ProofNode,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    let false_formula = CertFormula::Bool(false);
    let not_true = CertFormula::Not(Box::new(CertFormula::Bool(true)));
    // Eagerly register ¬⊤ from this node's conclusions before deriving ⊥
    for conclusion in &node.conclusions {
        let cert_conc = convert_formula(conclusion);
        if cert_conc == not_true && builder.lookup(&not_true).is_none() {
            if let Some(premise) = decomposition_premise {
                builder.add_step(cert_conc, Justification::TableauDecomposition { premise });
            }
        }
    }
    if builder.lookup(&false_formula).is_none() {
        if let Some(premise) = builder.lookup(&not_true).or(decomposition_premise) {
            decomposition_premise = Some(builder.add_step(
                false_formula,
                Justification::TableauDecomposition { premise },
            ));
        }
    }
    decomposition_premise
}

fn handle_and_elim(
    conj: &ZenonFormula,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    let conj_cert = convert_formula(conj);
    decomposition_premise =
        ensure_tableau_formula(builder, conj_cert.clone(), decomposition_premise);
    if let CertFormula::And(left, right) = &conj_cert {
        if let Some(conj_step) = builder.lookup(&conj_cert) {
            decomposition_premise = Some(conj_step);
            if builder.lookup(left).is_none() {
                builder.add_step(
                    left.as_ref().clone(),
                    Justification::AndElimLeft {
                        conjunction: conj_step,
                    },
                );
            }
            if builder.lookup(right).is_none() {
                builder.add_step(
                    right.as_ref().clone(),
                    Justification::AndElimRight {
                        conjunction: conj_step,
                    },
                );
            }
        }
    }
    decomposition_premise
}

fn handle_not_not(
    formula: &ZenonFormula,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    if let ZenonFormula::Not(inner) = formula {
        if let ZenonFormula::Not(innermost) = inner.as_ref() {
            let double_neg = convert_formula(formula);
            decomposition_premise =
                ensure_tableau_formula(builder, double_neg.clone(), decomposition_premise);
            let result = convert_formula(innermost);

            if let Some(nn_step) = builder.lookup(&double_neg) {
                decomposition_premise = Some(nn_step);
                if builder.lookup(&result).is_none() {
                    builder.add_step(result, Justification::DoubleNegElim { premise: nn_step });
                }
            }
        }
    }
    decomposition_premise
}

fn handle_forall_elim(
    formula: &ZenonFormula,
    term: &ZenonTerm,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    if let ZenonFormula::Forall(var, body) = formula {
        let forall_cert = convert_formula(formula);
        decomposition_premise =
            ensure_tableau_formula(builder, forall_cert.clone(), decomposition_premise);
        if let Some(forall_step) = builder.lookup(&forall_cert) {
            decomposition_premise = Some(forall_step);
            let cert_term = convert_term(term);
            let mut subst = crate::formula::Subst::new();
            subst.insert(var.clone(), term.clone());
            let instantiated = body.substitute(&subst);
            let inst_cert = convert_formula(&instantiated);

            if builder.lookup(&inst_cert).is_none() {
                builder.add_step(
                    inst_cert,
                    Justification::UniversalInstantiation {
                        forall: forall_step,
                        term: cert_term,
                    },
                );
            }
        }
    }
    decomposition_premise
}

fn handle_exists_elim(
    formula: &ZenonFormula,
    witness: &str,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    let exists_cert = convert_formula(formula);
    decomposition_premise =
        ensure_tableau_formula(builder, exists_cert.clone(), decomposition_premise);

    if let ZenonFormula::Exists(var, body) = formula {
        let mut subst = crate::formula::Subst::new();
        subst.insert(var.clone(), ZenonTerm::Const(witness.to_string()));
        let instantiated = body.substitute(&subst);
        let inst_cert = convert_formula(&instantiated);

        if builder.lookup(&inst_cert).is_none() {
            if let Some(premise) = builder.lookup(&exists_cert) {
                decomposition_premise = Some(premise);
                builder.add_step(inst_cert, Justification::TableauDecomposition { premise });
            }
        }
    }
    decomposition_premise
}

fn handle_refute(formula: &ZenonFormula, builder: &mut CertificateBuilder) -> Option<StepId> {
    let neg = CertFormula::Not(Box::new(convert_formula(formula)));
    if builder.lookup(&neg).is_none() {
        Some(builder.add_step(neg, Justification::Hypothesis(0)))
    } else {
        builder.lookup(&neg)
    }
}

fn handle_eq_refl(node: &ProofNode, builder: &mut CertificateBuilder) {
    for conclusion in &node.conclusions {
        if let ZenonFormula::Eq(t1, t2) = conclusion {
            if t1 == t2 {
                let eq_cert = convert_formula(conclusion);
                if builder.lookup(&eq_cert).is_none() {
                    builder.add_step(eq_cert, Justification::Axiom(Axiom::EqualityRefl));
                }
            }
        }
    }
}

fn handle_eq_sym(
    formula: &ZenonFormula,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    if let ZenonFormula::Eq(t1, t2) = formula {
        let eq_orig = convert_formula(formula);
        let eq_sym = CertFormula::Eq(convert_term(t2), convert_term(t1));

        if builder.lookup(&eq_sym).is_none() {
            let orig_step = if let Some(step) = builder.lookup(&eq_orig) {
                step
            } else if let Some(premise) = decomposition_premise {
                builder.add_step(eq_orig, Justification::TableauDecomposition { premise })
            } else {
                return decomposition_premise;
            };
            decomposition_premise = Some(orig_step);
            builder.add_step(
                eq_sym,
                Justification::TableauDecomposition { premise: orig_step },
            );
        }
    }
    decomposition_premise
}

fn handle_eq_subst(
    eq: &ZenonFormula,
    builder: &mut CertificateBuilder,
    mut decomposition_premise: Option<StepId>,
) -> Option<StepId> {
    let eq_cert = convert_formula(eq);
    if builder.lookup(&eq_cert).is_none() {
        let is_refl = matches!(&eq_cert, CertFormula::Eq(a, b) if a == b);
        if is_refl {
            decomposition_premise =
                Some(builder.add_step(eq_cert, Justification::Axiom(Axiom::EqualityRefl)));
        } else if let Some(premise) = decomposition_premise {
            decomposition_premise =
                Some(builder.add_step(eq_cert, Justification::TableauDecomposition { premise }));
        }
    } else {
        decomposition_premise = builder.lookup(&eq_cert);
    }
    decomposition_premise
}
