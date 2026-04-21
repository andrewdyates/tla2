// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory conflict inference for Alethe proof generation.
//!
//! This module maps theory solver conflicts to structured Alethe proof rules
//! (EUF congruence, transitivity, LRA Farkas). When a structured rule can be
//! inferred the proof is more precise than the generic `trust` fallback.
//!
//! Extracted from `proof_tracker.rs` for file-size hygiene (#4534).
//! Split into submodules for code health (#5970):
//! - `euf`: EUF congruence/transitivity lemma inference
//! - `decompose`: Combined real-theory lemma decomposition

mod decompose;
mod euf;

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{
    FarkasAnnotation, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryConflict,
    TheoryLemmaKind, TheoryLit,
};

use crate::proof_tracker::ProofTracker;

// Re-export pub(crate) items from submodules.
pub(crate) use decompose::decompose_generic_combined_real_lemma;

/// Record a theory conflict and infer the most specific Alethe rule.
pub(crate) fn record_theory_conflict_unsat(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<ProofId> {
    if !tracker.is_enabled() {
        return None;
    }

    let Some(clause) = build_blocking_clause_terms(negations, conflict) else {
        return tracker.add_theory_lemma(conflict.iter().map(|lit| lit.term).collect::<Vec<_>>());
    };

    // TODO(#8106): When neither EUF nor arithmetic inference succeeds,
    // this falls back to Generic/trust. Potential improvements: string theory
    // classifier, array axiom classifier, or combined-theory decomposition.
    let (kind, ordered_clause) = if let Some(terms) = terms {
        let result = euf::infer_euf_lemma(terms, negations, conflict)
            .or_else(|| infer_arith_farkas(terms, conflict, &clause));
        result.unwrap_or((TheoryLemmaKind::Generic, clause))
    } else {
        (TheoryLemmaKind::Generic, clause)
    };

    match kind {
        TheoryLemmaKind::Generic => tracker.add_theory_lemma(ordered_clause),
        TheoryLemmaKind::LiaGeneric => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]);
            tracker.add_theory_lemma_with_farkas_and_kind(ordered_clause, unit_farkas, kind)
        }
        TheoryLemmaKind::LraFarkas => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]);
            tracker.add_theory_lemma_with_farkas_and_kind(ordered_clause, unit_farkas, kind)
        }
        _ => tracker.add_theory_lemma_with_kind(ordered_clause, kind),
    }
}

/// Infer the most specific proof kind available for an already-materialized
/// theory lemma clause.
#[must_use]
pub(crate) fn infer_theory_lemma_kind_from_clause_terms(
    terms: &TermStore,
    clause: &[TermId],
) -> TheoryLemmaKind {
    infer_theory_lemma_kind_from_clause_terms_and_farkas(terms, clause, None)
}

/// Infer the most specific proof kind available for an already-materialized
/// theory lemma clause, using semantic Farkas validation when coefficients are
/// already available.
#[must_use]
pub(crate) fn infer_theory_lemma_kind_from_clause_terms_and_farkas(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    if let Some(farkas) = farkas {
        let conflict = blocking_clause_to_conflict_lits(terms, clause);
        let kind = classify_arith_conflict_kind(terms, &conflict, Some(farkas));
        if kind != TheoryLemmaKind::Generic {
            return kind;
        }
    }

    if clause_contains_integer_arith_literal(terms, clause) {
        TheoryLemmaKind::LiaGeneric
    } else {
        // TODO(#8106): Non-integer, non-LRA clause with no Farkas classification.
        // Could be EUF, string, array, or combined theory. Needs classifier.
        TheoryLemmaKind::Generic
    }
}

/// Infer the proof kind for a theory conflict that will be materialized as an
/// original SAT clause in the clause trace.
#[must_use]
pub(crate) fn infer_theory_conflict_kind(
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    match terms {
        Some(terms) => {
            if let Some(farkas) = farkas {
                let kind = classify_arith_conflict_kind(terms, conflict, Some(farkas));
                if kind != TheoryLemmaKind::Generic {
                    return kind;
                }
            }

            if !conflict.is_empty() && conflict_all_arith_literals(terms, conflict) {
                let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
                let kind = classify_arith_conflict_kind(terms, conflict, Some(&unit_farkas));
                if kind == TheoryLemmaKind::LraFarkas {
                    return kind;
                }
            }

            euf::infer_euf_lemma(terms, negations, conflict).map_or_else(
                || {
                    if arith_conflict_is_integer(terms, conflict) {
                        TheoryLemmaKind::LiaGeneric
                    } else {
                        // TODO(#8106): Non-EUF, non-arith conflict. Needs classifier
                        // for string, array, or combined theory conflicts.
                        TheoryLemmaKind::Generic
                    }
                },
                |(kind, _)| kind,
            )
        }
        // TODO(#8106): No TermStore available -- cannot classify. This path is
        // hit when proof generation is disabled or terms are not accessible.
        None => TheoryLemmaKind::Generic,
    }
}

/// Record a theory conflict with Farkas coefficients (arithmetic theories).
pub(crate) fn record_theory_conflict_unsat_with_farkas(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &TheoryConflict,
) -> Option<ProofId> {
    if !tracker.is_enabled() {
        return None;
    }

    let Some(farkas) = conflict.farkas.clone() else {
        let clause = build_blocking_clause_terms(negations, &conflict.literals)?;
        return tracker.add_theory_lemma(clause);
    };

    let clause = build_blocking_clause_terms(negations, &conflict.literals)?;

    let kind = match terms {
        Some(terms) => classify_arith_conflict_kind(terms, &conflict.literals, Some(&farkas)),
        // TODO(#8106): No TermStore -- cannot classify Farkas conflict.
        None => TheoryLemmaKind::Generic,
    };

    match kind {
        TheoryLemmaKind::Generic => tracker.add_theory_lemma(clause),
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => {
            tracker.add_theory_lemma_with_farkas_and_kind(clause, farkas, kind)
        }
        _ => tracker.add_theory_lemma_with_kind(clause, kind),
    }
}

fn build_blocking_clause_terms(
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<Vec<TermId>> {
    let mut out = Vec::with_capacity(conflict.len());
    for &lit in conflict {
        if lit.value {
            out.push(*negations.get(&lit.term)?);
        } else {
            out.push(lit.term);
        }
    }
    Some(out)
}

fn blocking_clause_to_conflict_lits(terms: &TermStore, clause: &[TermId]) -> Vec<TheoryLit> {
    clause
        .iter()
        .map(|&lit| match terms.get(lit) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(lit, false),
        })
        .collect()
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Infer an arithmetic proof kind when all conflict literals are comparisons.
///
/// The certificate boundary is semantic, not sort-based: any conflict whose
/// coefficients pass the shared Farkas verifier exports as `LraFarkas`, even if
/// the atoms mention `Int` terms. Integer arithmetic only falls back to
/// `LiaGeneric` when the coefficients are not Farkas-valid. Returns `None` if
/// any literal is non-arithmetic (#6365).
fn infer_arith_farkas(
    terms: &TermStore,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    if conflict.is_empty() {
        return None;
    }
    if !conflict_all_arith_literals(terms, conflict) {
        return None;
    }
    let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
    let kind = classify_arith_conflict_kind(terms, conflict, Some(&unit_farkas));
    Some((kind, clause.to_vec()))
}

fn classify_arith_conflict_kind(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    if let Some(farkas) = farkas {
        // Structural shape check only (O(k)): verify coefficient count matches
        // and all coefficients are non-negative.  The full semantic verification
        // (`verify_farkas_conflict_lits_full`) parses every term into BigRational,
        // explores up to 2^n equality-alternative combinations, and was measured
        // at 42% of total QF_LRA solver time on clocksynchro/sc-* benchmarks.
        // Classification only determines the Alethe proof rule; correctness does
        // not depend on it.  Full semantic validation remains available in
        // debug_assertions builds at the conflict-emission sites.
        if z4_core::proof_validation::verify_farkas_annotation_shape(farkas, conflict.len()).is_ok()
        {
            return TheoryLemmaKind::LraFarkas;
        }
    }

    if arith_conflict_is_integer(terms, conflict) {
        TheoryLemmaKind::LiaGeneric
    } else {
        // TODO(#8106): Arith conflict that is neither LRA Farkas-valid
        // nor integer. Could be a real-valued conflict with bad Farkas
        // annotation shape, or a mixed-theory conflict. Needs LRA fallback.
        TheoryLemmaKind::Generic
    }
}

fn strip_not(terms: &TermStore, term: TermId) -> TermId {
    match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    }
}

fn arith_conflict_is_integer(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    conflict.iter().any(|lit| {
        let atom = strip_not(terms, lit.term);
        match terms.get(atom) {
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2 =>
            {
                matches!(terms.sort(args[0]), Sort::Int) || matches!(terms.sort(args[1]), Sort::Int)
            }
            _ => false,
        }
    })
}

fn clause_contains_integer_arith_literal(terms: &TermStore, clause: &[TermId]) -> bool {
    clause.iter().any(|&lit| {
        let base = strip_not(terms, lit);
        match terms.get(base) {
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2 =>
            {
                matches!(terms.sort(args[0]), Sort::Int) || matches!(terms.sort(args[1]), Sort::Int)
            }
            _ => false,
        }
    })
}

fn conflict_all_arith_literals(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    conflict.iter().all(|lit| {
        matches!(
            terms.get(strip_not(terms, lit.term)),
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn test_infer_theory_lemma_kind_from_clause_terms_and_farkas_strict_int_bounds() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let ten = terms.mk_int(BigInt::from(10));
        let five = terms.mk_int(BigInt::from(5));
        let gt = terms.mk_gt(x, ten);
        let lt = terms.mk_lt(x, five);
        let clause = vec![terms.mk_not(gt), terms.mk_not(lt)];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);

        assert_eq!(
            infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, Some(&farkas)),
            TheoryLemmaKind::LraFarkas
        );
    }
}
