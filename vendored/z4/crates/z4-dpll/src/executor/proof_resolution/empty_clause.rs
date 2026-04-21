// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermData;
use z4_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaKind};

/// Collect assumptions and theory lemmas that are eligible for
/// `th_resolution`-style empty-clause reconstruction.
#[allow(clippy::type_complexity)]
pub(crate) fn collect_assumptions_and_theory_lemmas(
    proof: &Proof,
) -> (Vec<(ProofId, TermId)>, Vec<(ProofId, Vec<TermId>)>) {
    let mut assumptions = Vec::new();
    let mut theory_lemmas = Vec::new();

    for (idx, step) in proof.steps.iter().enumerate() {
        let id = ProofId(idx as u32);
        match step {
            ProofStep::Assume(term) => assumptions.push((id, *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => assumptions.push((id, clause[0])),
            ProofStep::TheoryLemma { clause, .. } => {
                theory_lemmas.push((id, clause.clone()));
            }
            _ => {}
        }
    }

    (assumptions, theory_lemmas)
}

/// Try to derive the empty clause via a th_resolution chain (#340 Phase 0).
pub(crate) fn try_derive_empty_via_th_resolution(terms: &TermStore, proof: &mut Proof) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);

    if assumptions.is_empty() || theory_lemmas.is_empty() {
        return false;
    }

    for (lemma_id, lemma_clause) in &theory_lemmas {
        if let Some(chain) = match_lemma_against_assumptions(terms, lemma_clause, &assumptions) {
            build_th_resolution_chain(proof, *lemma_id, lemma_clause, chain);
            return true;
        }
    }
    false
}

/// Try to derive the empty clause from two theory lemmas that each reduce
/// to complementary unit clauses against the active assumptions.
pub(crate) fn try_derive_empty_via_theory_packet_resolution(
    terms: &TermStore,
    proof: &mut Proof,
) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);
    if assumptions.is_empty() || theory_lemmas.len() < 2 {
        return false;
    }

    for (idx, (lhs_lemma_id, lhs_clause)) in theory_lemmas.iter().enumerate() {
        let Some((lhs_chain, lhs_unit)) =
            match_lemma_against_assumptions_to_unit(terms, lhs_clause, &assumptions)
        else {
            continue;
        };

        for (rhs_lemma_id, rhs_clause) in theory_lemmas.iter().skip(idx + 1) {
            let Some((rhs_chain, rhs_unit)) =
                match_lemma_against_assumptions_to_unit(terms, rhs_clause, &assumptions)
            else {
                continue;
            };
            if !literals_are_complementary(terms, lhs_unit, rhs_unit) {
                continue;
            }

            let lhs_id = apply_th_resolution_chain(proof, *lhs_lemma_id, lhs_clause, &lhs_chain).0;
            let rhs_id = apply_th_resolution_chain(proof, *rhs_lemma_id, rhs_clause, &rhs_chain).0;
            proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![],
                premises: vec![lhs_id, rhs_id],
                args: vec![],
            });
            return true;
        }
    }

    false
}

/// Match a theory lemma's literals against assumptions for resolution.
/// Returns the resolution chain if all lemma literals can be resolved.
pub(crate) fn match_lemma_against_assumptions(
    terms: &TermStore,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
) -> Option<Vec<(ProofId, TermId)>> {
    let mut neg_in_lemma: HashMap<TermId, TermId> = HashMap::new();
    let mut pos_in_lemma: HashMap<TermId, TermId> = HashMap::new();
    for &lit in lemma_clause {
        if let TermData::Not(inner) = terms.get(lit) {
            neg_in_lemma.insert(*inner, lit);
        } else {
            pos_in_lemma.insert(lit, lit);
        }
    }

    let mut remaining_clause: Vec<TermId> = lemma_clause.to_vec();
    let mut resolution_chain: Vec<(ProofId, TermId)> = Vec::new();

    for &(assume_id, assume_term) in assumptions {
        if let Some(lemma_lit) = neg_in_lemma.remove(&assume_term) {
            resolution_chain.push((assume_id, lemma_lit));
            remaining_clause.retain(|&t| t != lemma_lit);
        } else if let TermData::Not(inner) = terms.get(assume_term) {
            if let Some(lemma_lit) = pos_in_lemma.remove(inner) {
                resolution_chain.push((assume_id, lemma_lit));
                remaining_clause.retain(|&t| t != lemma_lit);
            }
        }
    }

    if remaining_clause.is_empty() && !resolution_chain.is_empty() {
        Some(resolution_chain)
    } else {
        None
    }
}

/// Match a theory lemma's literals against assumptions, leaving exactly one
/// residual literal for a final packet-resolution step.
pub(crate) fn match_lemma_against_assumptions_to_unit(
    terms: &TermStore,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
) -> Option<(Vec<(ProofId, TermId)>, TermId)> {
    let mut neg_in_lemma: HashMap<TermId, TermId> = HashMap::new();
    let mut pos_in_lemma: HashMap<TermId, TermId> = HashMap::new();
    for &lit in lemma_clause {
        if let TermData::Not(inner) = terms.get(lit) {
            neg_in_lemma.insert(*inner, lit);
        } else {
            pos_in_lemma.insert(lit, lit);
        }
    }

    let mut remaining_clause = lemma_clause.to_vec();
    let mut resolution_chain = Vec::new();
    for &(assume_id, assume_term) in assumptions {
        if let Some(lemma_lit) = neg_in_lemma.remove(&assume_term) {
            resolution_chain.push((assume_id, lemma_lit));
            remaining_clause.retain(|&t| t != lemma_lit);
        } else if let TermData::Not(inner) = terms.get(assume_term) {
            if let Some(lemma_lit) = pos_in_lemma.remove(inner) {
                resolution_chain.push((assume_id, lemma_lit));
                remaining_clause.retain(|&t| t != lemma_lit);
            }
        }
    }

    match remaining_clause.as_slice() {
        [unit] => Some((resolution_chain, *unit)),
        _ => None,
    }
}

/// Build a th_resolution chain from matched assumptions and lemma.
pub(crate) fn build_th_resolution_chain(
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    resolution_chain: Vec<(ProofId, TermId)>,
) {
    let (_, current_clause) =
        apply_th_resolution_chain(proof, lemma_id, lemma_clause, &resolution_chain);
    debug_assert!(current_clause.is_empty());
}

pub(crate) fn apply_th_resolution_chain(
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    resolution_chain: &[(ProofId, TermId)],
) -> (ProofId, Vec<TermId>) {
    let mut current_clause = lemma_clause.to_vec();
    let mut current_id = lemma_id;

    for &(assume_id, lemma_lit) in resolution_chain {
        current_clause.retain(|&t| t != lemma_lit);
        current_id = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: current_clause.clone(),
            premises: vec![current_id, assume_id],
            args: vec![],
        });
    }
    (current_id, current_clause)
}

pub(crate) fn literals_are_complementary(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    match terms.get(lhs) {
        TermData::Not(inner) => *inner == rhs,
        _ => matches!(terms.get(rhs), TermData::Not(inner) if *inner == lhs),
    }
}

/// Try to derive the empty clause from contradictory assumptions.
pub(crate) fn try_derive_empty_via_contradictory_assumptions(
    terms: &TermStore,
    proof: &mut Proof,
) -> bool {
    let assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => Some((ProofId(idx as u32), clause[0])),
            _ => None,
        })
        .collect();

    if assumptions.len() < 2 {
        return false;
    }

    let mut pos_atoms: HashMap<TermId, (ProofId, TermId)> = HashMap::new();
    let mut neg_atoms: Vec<(ProofId, TermId, TermId)> = Vec::new();

    for &(id, term) in &assumptions {
        if let TermData::Not(inner) = terms.get(term) {
            neg_atoms.push((id, term, *inner));
        } else {
            pos_atoms.insert(term, (id, term));
        }
    }

    for (neg_id, _neg_term, inner) in &neg_atoms {
        if let Some(&(pos_id, pos_term)) = pos_atoms.get(inner) {
            proof.add_step(ProofStep::Resolution {
                clause: vec![],
                pivot: pos_term,
                clause1: pos_id,
                clause2: *neg_id,
            });
            return true;
        }
    }

    false
}

/// Try to derive the empty clause from contradictory equality assumptions.
///
/// When the proof contains two assumptions `(= t c1)` and `(= t c2)` with
/// `c1 != c2`, synthesize a `LiaGeneric` theory lemma
/// `(not (= t c1)) (not (= t c2))` with Farkas coefficients and resolve it
/// against the two assumptions to derive the empty clause.
///
/// This handles the case where LIA preprocessing substituted `x -> c1` from
/// `(= x c1)`, making `(= x c2)` trivially false at the SAT level before the
/// theory solver produces a conflict. Without this, the proof falls through to
/// a trust-lemma fallback.
pub(crate) fn try_derive_empty_via_equality_contradiction(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    use z4_core::{Sort, Symbol};

    let assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            _ => None,
        })
        .collect();

    if assumptions.len() < 2 {
        return false;
    }

    struct EqInfo {
        proof_id: ProofId,
        eq_term: TermId,
        key: TermId,
        constant: i64,
    }

    let extract_int_const = |term: TermId| -> Option<i64> {
        match terms.get(term) {
            TermData::Const(z4_core::Constant::Int(n)) => n.try_into().ok(),
            _ => None,
        }
    };

    let mut eq_assumptions: Vec<EqInfo> = Vec::new();
    for &(id, term) in &assumptions {
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => continue,
        };
        if !matches!(terms.sort(lhs), Sort::Int) {
            continue;
        }
        if let Some(c) = extract_int_const(rhs) {
            eq_assumptions.push(EqInfo {
                proof_id: id,
                eq_term: term,
                key: lhs,
                constant: c,
            });
        } else if let Some(c) = extract_int_const(lhs) {
            eq_assumptions.push(EqInfo {
                proof_id: id,
                eq_term: term,
                key: rhs,
                constant: c,
            });
        }
    }

    for i in 0..eq_assumptions.len() {
        for j in (i + 1)..eq_assumptions.len() {
            if eq_assumptions[i].key != eq_assumptions[j].key {
                continue;
            }
            if eq_assumptions[i].constant == eq_assumptions[j].constant {
                continue;
            }

            let a = &eq_assumptions[i];
            let b = &eq_assumptions[j];

            let neg_a = terms.mk_not_raw(a.eq_term);
            let neg_b = terms.mk_not_raw(b.eq_term);
            let clause = vec![neg_a, neg_b];

            let farkas = crate::executor::proof_farkas::synthesize_equality_farkas(terms, &clause);

            let Some(farkas) = farkas else {
                continue;
            };

            let lemma_id = proof.add_step(ProofStep::TheoryLemma {
                theory: String::from("LIA"),
                kind: TheoryLemmaKind::LiaGeneric,
                clause,
                farkas: Some(farkas),
                lia: None,
            });

            let after_first = proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![neg_b],
                premises: vec![lemma_id, a.proof_id],
                args: vec![],
            });

            proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![],
                premises: vec![after_first, b.proof_id],
                args: vec![],
            });

            return true;
        }
    }

    false
}

/// Derive the empty clause by adding a trust theory lemma and resolving.
pub(crate) fn derive_empty_via_trust_lemma(terms: &mut TermStore, proof: &mut Proof) {
    let assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => Some((ProofId(idx as u32), clause[0])),
            _ => None,
        })
        .collect();

    if assumptions.is_empty() {
        return;
    }

    let mut negation_map: HashMap<TermId, TermId> = HashMap::new();
    let negated_clause: Vec<TermId> = assumptions
        .iter()
        .map(|&(_, term)| {
            let neg = if let TermData::Not(inner) = terms.get(term) {
                *inner
            } else {
                terms.mk_not_raw(term)
            };
            negation_map.insert(term, neg);
            neg
        })
        .collect();

    // TODO(#8106): This trust fallback is used during SAT proof reconstruction
    // when resolution cannot derive the empty clause from existing steps.
    // It is an inherent trust step (not a theory lemma), so Generic is correct
    // until proper SAT proof reconstruction eliminates the need for it.
    let lemma_id =
        proof.add_theory_lemma_with_kind("trust", negated_clause.clone(), TheoryLemmaKind::Generic);

    let mut current_clause = negated_clause;
    let mut current_id = lemma_id;

    for (assume_id, assume_term) in &assumptions {
        let neg_term = negation_map[assume_term];
        current_clause.retain(|&t| t != neg_term);

        current_id = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: current_clause.clone(),
            premises: vec![current_id, *assume_id],
            args: vec![],
        });
    }

    debug_assert!(
        current_clause.is_empty(),
        "trust-lemma th_resolution chain did not derive empty clause"
    );
}
