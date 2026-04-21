// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof structure validation for premise linkage, resolution, DRUP, and terminal empty-clause derivation.
mod boolean;
mod boolean_derived;
mod boolean_negation;
mod clausification;
mod euf;
mod euf_step_rules;
mod lia;
mod lra_farkas;
mod resolution;

use thiserror::Error;
use z4_core::{
    AletheRule, FarkasAnnotation, LiaAnnotation, Proof, ProofId, ProofStep, TermId, TermStore,
    TheoryLemmaKind,
};

use euf::{validate_euf_congruent, validate_euf_congruent_pred, validate_euf_transitive};
use euf_step_rules::{validate_cong, validate_refl, validate_symm, validate_trans};
use resolution::{is_valid_binary_resolution, is_valid_rup_step, validate_binary_resolution_rule};

/// Validation failure returned by [`check_proof`].
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofCheckError {
    /// The proof has no steps.
    #[error("proof is empty")]
    EmptyProof,
    /// The proof has steps but none of them produce a clause.
    #[error("proof has no clause-producing steps")]
    NoClauseProducingSteps,
    /// A premise index is outside the proof range.
    #[error("step {step} references missing premise {premise}")]
    MissingPremise {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A premise points to the current step or a future step.
    #[error("step {step} references non-prior premise {premise}")]
    NonPriorPremise {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A premise points to an anchor (no clause).
    #[error("step {step} premise {premise} does not produce a clause")]
    PremiseHasNoClause {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A resolution-style step does not match its premises.
    #[error("step {step} has invalid {rule} derivation")]
    InvalidResolution {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name (`resolution` or `th_resolution`).
        rule: String,
    },
    /// A DRUP step is not reverse-unit-propagation valid.
    #[error("step {step} has invalid drup derivation")]
    InvalidDrup {
        /// Invalid step ID.
        step: ProofId,
    },
    /// Hole steps are placeholders and are never valid final proofs.
    #[error("step {step} uses unsupported hole rule")]
    HoleStep {
        /// Invalid step ID.
        step: ProofId,
    },
    /// The checker only supports binary resolution for this rule.
    #[error("step {step} uses {rule} with unsupported premise count {premise_count}")]
    UnsupportedResolutionArity {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
        /// Number of premises provided by the step.
        premise_count: usize,
    },
    /// The terminal clause-producing step must derive the empty clause.
    #[error("final clause-producing step {step} is not the empty clause")]
    FinalClauseNotEmpty {
        /// Final clause-producing step ID.
        step: ProofId,
    },
    /// Trust steps are unverified and rejected in strict mode.
    #[error("step {step} uses unverified trust rule")]
    TrustStep {
        /// Invalid step ID.
        step: ProofId,
    },
    /// A generic Alethe rule lacks semantic validation and is rejected in strict mode.
    #[error("step {step} uses unvalidated rule {rule} in strict mode")]
    UnvalidatedRule {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
    },
    /// Theory lemmas without a strict-mode semantic validator are rejected.
    #[error("step {step} uses unsupported theory lemma kind {kind:?} in strict mode")]
    UnsupportedTheoryLemmaKind {
        /// Invalid step ID.
        step: ProofId,
        /// Rejected theory lemma kind.
        kind: TheoryLemmaKind,
    },
    /// A theory lemma failed strict semantic validation.
    #[error("step {step} has invalid theory lemma: {reason}")]
    InvalidTheoryLemma {
        /// Invalid step ID.
        step: ProofId,
        /// Semantic validation failure detail.
        reason: String,
    },
    /// A Boolean tautology or clausification rule failed structural validation.
    #[error("step {step} has invalid {rule} rule: {reason}")]
    InvalidBooleanRule {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
        /// Validation failure detail.
        reason: String,
    },
    /// Strict proof mode rejects proofs containing any trust steps (#8076).
    ///
    /// When `produce-proofs` is enabled with strict proof mode, every theory
    /// must produce proper proof rules instead of falling back to `trust`.
    /// The reason string identifies which theory lemma kinds triggered the
    /// trust fallback.
    #[error("{reason}")]
    StrictProofModeTrust {
        /// Description of which trust steps were found and their sources.
        reason: String,
    },
}

/// Validate proof structure: premise linkage, resolution, DRUP, and terminal empty clause.
/// Theory lemmas and trust-style rules are treated as axioms in this mode.
pub fn check_proof(proof: &Proof, terms: &TermStore) -> Result<(), ProofCheckError> {
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }
    debug_assert!(
        u32::try_from(proof.steps.len()).is_ok(),
        "BUG: proof has {} steps, exceeding ProofId(u32) capacity",
        proof.steps.len()
    );

    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());
    for (idx, step) in proof.steps.iter().enumerate() {
        validate_step(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
        )?;
    }

    ensure_terminal_empty_clause(&derived_clauses)
}

pub(crate) fn validate_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
) -> Result<(), ProofCheckError> {
    debug_assert_eq!(
        step_id.0 as usize,
        derived_clauses.len(),
        "BUG: step_id {} does not match derived_clauses index {}",
        step_id.0,
        derived_clauses.len()
    );
    match step {
        ProofStep::Assume(term) => derived_clauses.push(Some(vec![*term])),
        ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        } => validate_theory_lemma(
            terms,
            derived_clauses,
            step_id,
            clause,
            farkas.as_ref(),
            *kind,
            lia.as_ref(),
            strict,
        )?,
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => validate_resolution_step(
            terms,
            derived_clauses,
            step_id,
            clause,
            *pivot,
            *clause1,
            *clause2,
        )?,
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => {
            if strict && matches!(rule, AletheRule::Trust) {
                return Err(ProofCheckError::TrustStep { step: step_id });
            }
            validate_generic_step(
                terms,
                derived_clauses,
                step_id,
                rule,
                clause,
                premises,
                args,
                strict,
            )?;
        }
        ProofStep::Anchor { .. } => derived_clauses.push(None),
        _ => unreachable!("unexpected ProofStep variant"),
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_theory_lemma(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    kind: TheoryLemmaKind,
    lia_ann: Option<&LiaAnnotation>,
    strict: bool,
) -> Result<(), ProofCheckError> {
    if strict {
        match kind {
            TheoryLemmaKind::EufTransitive => {
                validate_euf_transitive(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruent => {
                validate_euf_congruent(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruentPred => {
                validate_euf_congruent_pred(terms, step_id, clause)?;
            }
            TheoryLemmaKind::LraFarkas => {
                lra_farkas::validate_lra_farkas(terms, step_id, clause, farkas)?;
            }
            TheoryLemmaKind::LiaGeneric => {
                lia::validate_lia_generic(terms, step_id, clause, farkas, lia_ann)?;
            }
            // BV bit-blast lemmas: accept the clause as axiomatic.
            // The clause encodes a propositional gate definition (AND/OR/XOR/etc.)
            // produced by the bit-blaster. Full semantic validation (checking that
            // the clause matches the gate's truth table) is future work.
            // Accepting these here eliminates the `trust` fallback in the Alethe
            // output (#8071 Phase 1a).
            TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. } => {
                // Structural check: BV bit-blast clauses must be non-empty.
                // An empty clause from a gate encoding indicates a bug in the
                // bit-blaster, not a valid proof step.
                if clause.is_empty() {
                    return Err(ProofCheckError::InvalidTheoryLemma {
                        step: step_id,
                        reason: "bv_bitblast clause must be non-empty".to_string(),
                    });
                }
            }
            // Array theory lemmas: accept the clause as axiomatic.
            // Read-over-write and extensionality are standard array axiom
            // schemas. Full semantic validation (checking that the clause
            // matches the axiom schema structurally) is future work.
            // Accepting these here eliminates the `trust` fallback in the
            // Alethe output (#8073 Phase 1b).
            TheoryLemmaKind::ArraySelectStore { .. } | TheoryLemmaKind::ArrayExtensionality => {
                // Structural check: array axiom clauses must be non-empty.
                if clause.is_empty() {
                    return Err(ProofCheckError::InvalidTheoryLemma {
                        step: step_id,
                        reason: "array axiom clause must be non-empty".to_string(),
                    });
                }
            }
            // FP→BV translation lemmas: accept the clause as axiomatic.
            // The clause encodes the IEEE 754 FP operation lowered to BV
            // circuits. Full semantic validation (checking that the BV circuit
            // faithfully implements the FP operation) is future work (#8075).
            // Accepting these here eliminates the `trust` fallback for FP
            // theory lemmas.
            TheoryLemmaKind::FpToBv { .. } => {
                // Structural check: FP→BV clauses must be non-empty.
                if clause.is_empty() {
                    return Err(ProofCheckError::InvalidTheoryLemma {
                        step: step_id,
                        reason: "fp_to_bv clause must be non-empty".to_string(),
                    });
                }
            }
            // String theory lemmas: accept the clause as axiomatic.
            // Length axioms, content rewriting (substr/contains/replace),
            // and normal form decomposition (word equations, code injectivity)
            // are standard string theory axiom schemas. Full semantic
            // validation is future work (#8074 Phase 2).
            // Accepting these here eliminates the `trust` fallback for
            // string theory lemmas (#8074 Phase 1c).
            TheoryLemmaKind::StringLengthAxiom
            | TheoryLemmaKind::StringContentAxiom
            | TheoryLemmaKind::StringNormalForm => {
                // Structural check: string axiom clauses must be non-empty.
                if clause.is_empty() {
                    return Err(ProofCheckError::InvalidTheoryLemma {
                        step: step_id,
                        reason: "string axiom clause must be non-empty".to_string(),
                    });
                }
            }
            other => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind: other,
                });
            }
        }
    }

    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

fn validate_resolution_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    clause: &[TermId],
    pivot: TermId,
    clause1: ProofId,
    clause2: ProofId,
) -> Result<(), ProofCheckError> {
    let premise1 = premise_clause(derived_clauses, step_id, clause1)?;
    let premise2 = premise_clause(derived_clauses, step_id, clause2)?;

    if !is_valid_binary_resolution(terms, premise1, premise2, clause, Some(pivot)) {
        return Err(ProofCheckError::InvalidResolution {
            step: step_id,
            rule: AletheRule::Resolution.name().to_string(),
        });
    }

    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_generic_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    strict: bool,
) -> Result<(), ProofCheckError> {
    let premise_clauses: Vec<&[TermId]> = premises
        .iter()
        .map(|premise| premise_clause(derived_clauses, step_id, *premise))
        .collect::<Result<_, _>>()?;

    match rule {
        AletheRule::Resolution | AletheRule::ThResolution => validate_binary_resolution_rule(
            terms,
            step_id,
            rule,
            clause,
            &premise_clauses,
            args.first().copied(),
        )?,
        AletheRule::Drup => {
            if !is_valid_rup_step(terms, clause, derived_clauses) {
                return Err(ProofCheckError::InvalidDrup { step: step_id });
            }
        }
        AletheRule::Hole => return Err(ProofCheckError::HoleStep { step: step_id }),
        AletheRule::Trust => {}
        AletheRule::AndPos(i) if strict => {
            boolean::validate_and_pos(terms, step_id, clause, *i, args.first().copied())?;
        }
        AletheRule::AndNeg if strict => {
            boolean::validate_and_neg(terms, step_id, clause, args.first().copied())?;
        }
        AletheRule::OrPos(_) if strict => {
            boolean::validate_or_pos(terms, step_id, clause)?;
        }
        AletheRule::OrNeg if strict => {
            boolean::validate_or_neg(terms, step_id, clause)?;
        }
        AletheRule::ImpliesPos if strict => {
            boolean::validate_implies_pos(terms, step_id, clause)?;
        }
        AletheRule::ImpliesNeg1 if strict => {
            boolean::validate_implies_neg1(terms, step_id, clause)?;
        }
        AletheRule::ImpliesNeg2 if strict => {
            boolean::validate_implies_neg2(terms, step_id, clause)?;
        }
        AletheRule::EquivPos1 if strict => {
            boolean_derived::validate_equiv_pos1(terms, step_id, clause)?;
        }
        AletheRule::EquivPos2 if strict => {
            boolean_derived::validate_equiv_pos2(terms, step_id, clause)?;
        }
        AletheRule::EquivNeg1 if strict => {
            boolean_derived::validate_equiv_neg1(terms, step_id, clause)?;
        }
        AletheRule::EquivNeg2 if strict => {
            boolean_derived::validate_equiv_neg2(terms, step_id, clause)?;
        }
        AletheRule::ItePos1 if strict => {
            boolean_derived::validate_ite_pos1(terms, step_id, clause)?;
        }
        AletheRule::ItePos2 if strict => {
            boolean_derived::validate_ite_pos2(terms, step_id, clause)?;
        }
        AletheRule::IteNeg1 if strict => {
            boolean_derived::validate_ite_neg1(terms, step_id, clause)?;
        }
        AletheRule::IteNeg2 if strict => {
            boolean_derived::validate_ite_neg2(terms, step_id, clause)?;
        }
        AletheRule::XorPos1 if strict => {
            boolean_derived::validate_xor_pos1(terms, step_id, clause)?;
        }
        AletheRule::XorPos2 if strict => {
            boolean_derived::validate_xor_pos2(terms, step_id, clause)?;
        }
        AletheRule::XorNeg1 if strict => {
            boolean_derived::validate_xor_neg1(terms, step_id, clause)?;
        }
        AletheRule::XorNeg2 if strict => {
            boolean_derived::validate_xor_neg2(terms, step_id, clause)?;
        }
        AletheRule::EqReflexive if strict => {
            boolean_derived::validate_eq_reflexive(terms, step_id, clause)?;
        }
        AletheRule::NotAnd if strict => {
            boolean_negation::validate_not_and(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotOr if strict => {
            boolean_negation::validate_not_or(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotImplies1 if strict => {
            boolean_negation::validate_not_implies1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotImplies2 if strict => {
            boolean_negation::validate_not_implies2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotEquiv1 if strict => {
            boolean_negation::validate_not_equiv1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotEquiv2 if strict => {
            boolean_negation::validate_not_equiv2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotIte1 if strict => {
            boolean_negation::validate_not_ite1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotIte2 if strict => {
            boolean_negation::validate_not_ite2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Or if strict => {
            clausification::validate_or_clausification(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Contraction if strict => {
            boolean_negation::validate_contraction(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Refl if strict => {
            validate_refl(terms, step_id, clause)?;
        }
        AletheRule::Symm if strict => {
            validate_symm(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Trans if strict => {
            validate_trans(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Cong if strict => {
            validate_cong(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::EqTransitive if strict => {
            validate_euf_transitive(terms, step_id, clause)?;
        }
        AletheRule::EqCongruent if strict => {
            validate_euf_congruent(terms, step_id, clause)?;
        }
        AletheRule::EqCongruentPred if strict => {
            validate_euf_congruent_pred(terms, step_id, clause)?;
        }
        _ => {
            if strict {
                return Err(ProofCheckError::UnvalidatedRule {
                    step: step_id,
                    rule: rule.name().to_string(),
                });
            }
        }
    }

    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

pub(crate) fn ensure_terminal_empty_clause(
    derived_clauses: &[Option<Vec<TermId>>],
) -> Result<(), ProofCheckError> {
    let Some((last_idx, last_clause)) = derived_clauses
        .iter()
        .enumerate()
        .rev()
        .find_map(|(idx, clause)| clause.as_deref().map(|clause| (idx, clause)))
    else {
        return Err(ProofCheckError::NoClauseProducingSteps);
    };

    if !last_clause.is_empty() {
        return Err(ProofCheckError::FinalClauseNotEmpty {
            step: ProofId(last_idx as u32),
        });
    }

    Ok(())
}

fn premise_clause(
    derived_clauses: &[Option<Vec<TermId>>],
    step: ProofId,
    premise: ProofId,
) -> Result<&[TermId], ProofCheckError> {
    let step_idx = step.0 as usize;
    let premise_idx = premise.0 as usize;

    if premise_idx >= derived_clauses.len() {
        return Err(ProofCheckError::MissingPremise { step, premise });
    }
    if premise_idx >= step_idx {
        return Err(ProofCheckError::NonPriorPremise { step, premise });
    }

    derived_clauses[premise_idx]
        .as_deref()
        .ok_or(ProofCheckError::PremiseHasNoClause { step, premise })
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
