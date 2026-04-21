// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolution and RUP verification engine.
//!
//! Implements propositional resolution checking and reverse-unit-propagation
//! (RUP) for DRUP proof steps in Alethe proofs.

use super::boolean::{matches_negation_of_term, matches_positive_literal_of_term};
use std::collections::{HashMap, HashSet};
use z4_core::{AletheRule, ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SignedLiteral {
    pub(crate) atom: TermId,
    pub(crate) positive: bool,
}

impl SignedLiteral {
    pub(crate) fn negated(self) -> Self {
        Self {
            atom: self.atom,
            positive: !self.positive,
        }
    }
}

pub(crate) fn decode_literal(terms: &TermStore, literal: TermId) -> SignedLiteral {
    match terms.get(literal) {
        TermData::Not(inner) => SignedLiteral {
            atom: *inner,
            positive: false,
        },
        _ => SignedLiteral {
            atom: literal,
            positive: true,
        },
    }
}

fn clause_as_set(terms: &TermStore, clause: &[TermId]) -> HashSet<SignedLiteral> {
    clause
        .iter()
        .map(|literal| decode_literal(terms, *literal))
        .collect()
}

pub(crate) fn is_valid_binary_resolution(
    terms: &TermStore,
    clause1: &[TermId],
    clause2: &[TermId],
    conclusion: &[TermId],
    pivot: Option<TermId>,
) -> bool {
    let clause1_set = clause_as_set(terms, clause1);
    let clause2_set = clause_as_set(terms, clause2);
    let conclusion_set = clause_as_set(terms, conclusion);

    if let Some(pivot_term) = pivot {
        let pivot_lit = decode_literal(terms, pivot_term);
        if resolve_on_pivot(&clause1_set, &clause2_set, pivot_lit, &conclusion_set)
            || resolve_on_pivot(
                &clause1_set,
                &clause2_set,
                pivot_lit.negated(),
                &conclusion_set,
            )
        {
            return true;
        }

        return resolve_on_semantic_pivot(terms, clause1, clause2, conclusion, Some(pivot_term));
    }

    if clause1_set
        .iter()
        .any(|pivot_lit| resolve_on_pivot(&clause1_set, &clause2_set, *pivot_lit, &conclusion_set))
        || clause2_set.iter().any(|pivot_lit| {
            resolve_on_pivot(&clause2_set, &clause1_set, *pivot_lit, &conclusion_set)
        })
    {
        return true;
    }

    resolve_on_semantic_pivot(terms, clause1, clause2, conclusion, None)
}

fn resolve_on_pivot(
    left: &HashSet<SignedLiteral>,
    right: &HashSet<SignedLiteral>,
    pivot: SignedLiteral,
    expected: &HashSet<SignedLiteral>,
) -> bool {
    if !left.contains(&pivot) || !right.contains(&pivot.negated()) {
        return false;
    }

    let mut resolvent: HashSet<SignedLiteral> = Default::default();
    for literal in left {
        if *literal != pivot {
            resolvent.insert(*literal);
        }
    }
    for literal in right {
        if *literal != pivot.negated() {
            resolvent.insert(*literal);
        }
    }

    &resolvent == expected
}

fn resolve_on_semantic_pivot(
    terms: &TermStore,
    left: &[TermId],
    right: &[TermId],
    expected: &[TermId],
    pivot: Option<TermId>,
) -> bool {
    let expected_set: HashSet<TermId> = expected.iter().copied().collect();
    for (left_idx, &left_lit) in left.iter().enumerate() {
        for (right_idx, &right_lit) in right.iter().enumerate() {
            if !are_complements(terms, left_lit, right_lit) {
                continue;
            }
            if let Some(pivot_term) = pivot {
                if !pair_matches_pivot(terms, left_lit, right_lit, pivot_term) {
                    continue;
                }
            }

            let mut resolvent: HashSet<TermId> = HashSet::new();
            for (idx, &lit) in left.iter().enumerate() {
                if idx != left_idx {
                    resolvent.insert(lit);
                }
            }
            for (idx, &lit) in right.iter().enumerate() {
                if idx != right_idx {
                    resolvent.insert(lit);
                }
            }

            if resolvent == expected_set {
                return true;
            }
        }
    }
    false
}

fn are_complements(terms: &TermStore, left: TermId, right: TermId) -> bool {
    matches_negation_of_term(terms, left, right) || matches_negation_of_term(terms, right, left)
}

fn pair_matches_pivot(terms: &TermStore, left: TermId, right: TermId, pivot: TermId) -> bool {
    // Either left matches pivot positively and right matches negation, or vice versa.
    // (Previous version had 4 arms; arms 3 and 4 duplicated arms 2 and 1.)
    (matches_positive_literal_of_term(terms, left, pivot)
        && matches_negation_of_term(terms, right, pivot))
        || (matches_positive_literal_of_term(terms, right, pivot)
            && matches_negation_of_term(terms, left, pivot))
}

pub(crate) fn is_valid_rup_step(
    terms: &TermStore,
    clause: &[TermId],
    prior_clauses: &[Option<Vec<TermId>>],
) -> bool {
    let mut assignments: HashMap<TermId, bool> = HashMap::new();

    // RUP checks unsat(F ∧ ¬clause): assign each literal in clause to false.
    for &literal in clause {
        let negated = decode_literal(terms, literal).negated();
        if !assign_literal(&mut assignments, negated) {
            return true;
        }
    }

    // Upper bound on BCP iterations: each pass assigns at least one new atom
    // when `changed` is set. The total distinct atoms across all clauses plus
    // the negated target clause is the hard ceiling.
    let max_iterations: usize = {
        let atom_count = prior_clauses
            .iter()
            .filter_map(Option::as_deref)
            .flat_map(|c| c.iter().map(|&lit| decode_literal(terms, lit).atom))
            .chain(clause.iter().map(|&lit| decode_literal(terms, lit).atom))
            .collect::<HashSet<_>>()
            .len();
        atom_count + 1
    };
    let mut iterations: usize = 0;

    loop {
        iterations += 1;
        debug_assert!(
            iterations <= max_iterations,
            "BUG: RUP propagation exceeded atom count bound ({iterations} > {max_iterations})"
        );
        if iterations > max_iterations {
            return false;
        }
        let mut changed = false;

        for clause in prior_clauses.iter().filter_map(Option::as_deref) {
            let mut unit_literal: Option<SignedLiteral> = None;
            let mut clause_satisfied = false;
            let mut multiple_unassigned = false;

            for &literal in clause {
                let signed = decode_literal(terms, literal);
                match assignments.get(&signed.atom) {
                    Some(value) if *value == signed.positive => {
                        clause_satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        if unit_literal.is_some() {
                            multiple_unassigned = true;
                        } else {
                            unit_literal = Some(signed);
                        }
                    }
                }
            }

            if clause_satisfied {
                continue;
            }

            match (unit_literal, multiple_unassigned) {
                (None, _) => return true,
                (Some(_), true) => continue,
                (Some(unit), false) => {
                    if !assign_literal(&mut assignments, unit) {
                        return true;
                    }
                    changed = true;
                }
            }
        }

        if !changed {
            return false;
        }
    }
}

fn assign_literal(assignments: &mut HashMap<TermId, bool>, literal: SignedLiteral) -> bool {
    match assignments.get(&literal.atom) {
        Some(existing) => *existing == literal.positive,
        None => {
            assignments.insert(literal.atom, literal.positive);
            true
        }
    }
}

pub(crate) fn validate_binary_resolution_rule(
    terms: &TermStore,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    pivot: Option<TermId>,
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 2 {
        return Err(ProofCheckError::UnsupportedResolutionArity {
            step: step_id,
            rule: rule.name().to_string(),
            premise_count: premise_clauses.len(),
        });
    }

    if !is_valid_binary_resolution(terms, premise_clauses[0], premise_clauses[1], clause, pivot) {
        return Err(ProofCheckError::InvalidResolution {
            step: step_id,
            rule: rule.name().to_string(),
        });
    }

    Ok(())
}
