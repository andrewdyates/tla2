// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-level proof manager for translating clause traces to Alethe proofs
//!
//! This module consumes the in-memory clause trace from the SAT solver and
//! translates it into explicit Alethe `resolution` proof steps.
//!
//! ## Design
//!
//! - The SAT solver records clause additions in a `ClauseTrace`
//! - Learned clauses include the conflict-analysis hint chain (`resolution_hints`)
//! - This manager translates SAT literals to SMT terms
//! - For each learned clause, it builds a chain of `ProofStep::Resolution`
//!   nodes and maps SAT clause IDs to proof IDs
//!
//! Author: Andrew Yates

mod derivation;
#[cfg(test)]
mod tests;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    AletheRule, ClausificationProof, Proof, ProofId, ProofStep, TermData, TermId, TermStore,
    TheoryLemmaProof,
};
use z4_sat::{ClauseTrace, Literal};

/// SAT-level proof manager for translating clause traces to Alethe steps
pub(crate) struct SatProofManager<'a> {
    /// Mapping from SAT variable index to SMT term
    var_to_term: &'a HashMap<u32, TermId>,
    /// Term store for creating negations
    terms: &'a mut TermStore,
    /// Clausification proof annotations from Tseitin encoder (#6031).
    /// Parallel to Tseitin clause order — the i-th original clause in the
    /// trace corresponds to `clausification_proofs[i]`.
    clausification_proofs: Option<&'a [Option<ClausificationProof>]>,
    /// Original-clause theory proof annotations aligned by SAT trace order.
    original_clause_theory_proofs: Option<&'a [Option<TheoryLemmaProof>]>,
    /// Theory lemma proof annotations (#6031 Phase 4).
    /// Keyed by normalized clause content (sorted TermIds) — when an original
    /// clause in the trace matches a recorded theory lemma, this map provides
    /// the annotation for emitting a `TheoryLemma` proof step.
    theory_lemma_proofs: Option<&'a HashMap<Vec<TermId>, TheoryLemmaProof>>,
    /// Number of learned clauses that fell back to Trust due to failed
    /// resolution hint reconstruction (#4585).
    trust_fallback_count: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum HintDerivationError {
    NoUsableHints,
    NoResolutionPivot {
        usable_hint_count: usize,
    },
    FinalClauseMismatch {
        expected_clause: Vec<TermId>,
        derived_clause: Vec<TermId>,
    },
}

impl<'a> SatProofManager<'a> {
    /// Create a new SAT proof manager
    pub(crate) fn new(var_to_term: &'a HashMap<u32, TermId>, terms: &'a mut TermStore) -> Self {
        SatProofManager {
            var_to_term,
            terms,
            clausification_proofs: None,
            original_clause_theory_proofs: None,
            theory_lemma_proofs: None,
            trust_fallback_count: 0,
        }
    }

    /// Attach clausification proof annotations from the Tseitin encoder (#6031).
    ///
    /// When set, `add_original_clause_step` emits premiseless tautology rule
    /// steps (e.g., `and_pos`, `or_neg`) for annotated clauses instead of
    /// the generic `assume` + `or` pattern. Annotations are parallel to the
    /// Tseitin clause order (i-th original clause matches annotations[i]).
    pub(crate) fn set_clausification_proofs(&mut self, proofs: &'a [Option<ClausificationProof>]) {
        self.clausification_proofs = Some(proofs);
    }

    /// Attach direct original-clause theory annotations for SAT reconstruction.
    pub(crate) fn set_original_clause_theory_proofs(
        &mut self,
        proofs: &'a [Option<TheoryLemmaProof>],
    ) {
        self.original_clause_theory_proofs = Some(proofs);
    }

    /// Attach theory lemma proof annotations (#6031 Phase 4).
    ///
    /// Keyed by normalized clause content (sorted TermIds). When an original
    /// clause in the clause trace matches a theory lemma annotation,
    /// `add_original_clause_step` emits a `TheoryLemma` proof step with
    /// the proper Alethe rule instead of the generic `assume` + `or` pattern.
    pub(crate) fn set_theory_lemma_proofs(
        &mut self,
        proofs: &'a HashMap<Vec<TermId>, TheoryLemmaProof>,
    ) {
        self.theory_lemma_proofs = Some(proofs);
    }

    /// Convert a SAT literal to an SMT term
    ///
    /// - `pos(v)` -> normalized proof literal for `var_to_term[v]`
    /// - `neg(v)` -> explicit syntactic complement of that literal
    fn lit_to_term(&mut self, lit: Literal) -> Option<TermId> {
        let var_idx = lit.variable().index() as u32;
        let term = *self.var_to_term.get(&var_idx)?;
        let positive_term = self.normalize_positive_literal(term);

        if lit.is_positive() {
            Some(positive_term)
        } else {
            Some(self.negate_term(positive_term))
        }
    }

    /// Normalize a SAT-variable atom for proof-literal emission.
    ///
    /// Returns the term unchanged. Previously converted AND atoms to their
    /// De Morgan dual `(not (or ...))`, but this produced incorrect Alethe
    /// syntax: and_pos expects `(cl (not (and ...)) ti)`, not
    /// `(cl (or (not ...) ...) ti)` (#6365).
    ///
    /// The AND atom stays as-is; `negate_term` produces `mk_not_raw(and_term)`
    /// which is the correct Alethe form for clausification tautology rules.
    fn normalize_positive_literal(&mut self, term: TermId) -> TermId {
        term
    }

    /// Convert a SAT clause to SMT terms.
    fn clause_to_terms(&mut self, clause: &[Literal]) -> Option<Vec<TermId>> {
        clause.iter().map(|&lit| self.lit_to_term(lit)).collect()
    }

    /// Canonicalized clause key (order-insensitive).
    fn normalize_clause(clause: &[TermId]) -> Vec<TermId> {
        let mut normalized = clause.to_vec();
        normalized.sort_unstable();
        normalized.dedup();
        normalized
    }

    /// Check whether clauses are equivalent up to ordering/duplication.
    fn clauses_equivalent(lhs: &[TermId], rhs: &[TermId]) -> bool {
        Self::normalize_clause(lhs) == Self::normalize_clause(rhs)
    }

    /// Compute term negation, reusing cached terms where possible.
    fn negate_term(&mut self, term: TermId) -> TermId {
        if let TermData::Not(inner) = self.terms.get(term) {
            return *inner;
        }
        self.terms.mk_not_raw(term)
    }

    /// Compute a single binary resolution step, if possible.
    fn resolve_once(&mut self, lhs: &[TermId], rhs: &[TermId]) -> Option<(TermId, Vec<TermId>)> {
        let rhs_set: HashSet<TermId> = rhs.iter().copied().collect();

        let pivot = lhs
            .iter()
            .copied()
            .find(|lit| rhs_set.contains(&self.negate_term(*lit)))?;
        let neg_pivot = self.negate_term(pivot);

        let mut resolvent = Vec::with_capacity(lhs.len() + rhs.len());
        let mut seen: HashSet<TermId> = Default::default();

        for &lit in lhs.iter().chain(rhs.iter()) {
            if lit == pivot || lit == neg_pivot {
                continue;
            }
            let neg_lit = self.negate_term(lit);
            if seen.contains(&neg_lit) {
                // Tautological resolvent; skip this candidate.
                return None;
            }
            if seen.insert(lit) {
                resolvent.push(lit);
            }
        }

        Some((pivot, resolvent))
    }

    fn clause_from_step(step: &ProofStep) -> Option<Vec<TermId>> {
        match step {
            ProofStep::Assume(term) => Some(vec![*term]),
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause.clone()),
            ProofStep::Anchor { .. } => None,
            // All current ProofStep variants handled above (#5692).
            // Wildcard covers future variants from #[non_exhaustive].
            other => unreachable!("unhandled ProofStep variant in clause_from_step(): {other:?}"),
        }
    }

    /// Process a clause trace and emit `resolution` proof steps.
    ///
    /// Returns the ProofId of the final empty clause derivation, or None if
    /// the trace cannot be translated to a complete resolution chain.
    pub(crate) fn process_trace(
        &mut self,
        trace: &ClauseTrace,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        if !trace.has_empty_clause() {
            return None;
        }

        let mut clause_terms: HashMap<u64, Vec<TermId>> = HashMap::new();
        let mut clause_proofs: HashMap<u64, ProofId> = HashMap::new();
        let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();
        let mut final_empty: Option<ProofId> = None;
        let mut weak_empty: Option<ProofId> = None;
        let mut original_clause_idx: usize = 0;

        for (idx, step) in proof.steps.iter().enumerate() {
            let Some(clause) = Self::clause_from_step(step) else {
                continue;
            };
            let key = Self::normalize_clause(&clause);
            existing_clause_map
                .entry(key)
                .or_insert(ProofId(idx as u32));
        }

        for entry in trace.entries() {
            let Some(entry_clause_terms) = self.clause_to_terms(&entry.clause) else {
                continue;
            };
            clause_terms.insert(entry.id, entry_clause_terms.clone());

            let clause_proof = if entry.is_original {
                // Look up clausification annotation by original clause index (#6031 Phase 3).
                let annotation = self
                    .clausification_proofs
                    .and_then(|proofs| proofs.get(original_clause_idx))
                    .and_then(|opt| opt.as_ref());
                let indexed_theory_annotation = self
                    .original_clause_theory_proofs
                    .and_then(|proofs| proofs.get(original_clause_idx))
                    .and_then(|opt| opt.as_ref());
                // Look up theory lemma annotation by normalized clause content (#6031 Phase 4).
                let normalized_key = Self::normalize_clause(&entry_clause_terms);
                let theory_annotation = indexed_theory_annotation.or_else(|| {
                    self.theory_lemma_proofs
                        .and_then(|proofs| proofs.get(&normalized_key))
                });
                original_clause_idx += 1;
                Self::add_original_clause_step(
                    self.terms,
                    proof,
                    &entry_clause_terms,
                    &mut existing_clause_map,
                    annotation,
                    theory_annotation,
                )
            } else {
                match self.derive_clause_from_hints(
                    &entry_clause_terms,
                    &entry.resolution_hints,
                    &clause_terms,
                    &clause_proofs,
                    proof,
                ) {
                    Ok(derived) => derived,
                    Err(error) => {
                        // Trust-lemma fallback (#4317 path 2 of 3).
                        // Per-clause fallback when resolution hint reconstruction
                        // fails. Emits the clause as AletheRule::Trust with whatever
                        // premises we could resolve. Sound but not independently
                        // verifiable by the proof checker.
                        // See also: executor/proof.rs derive_empty_via_trust_lemma (path 1)
                        self.trust_fallback_count += 1;
                        let premises: Vec<ProofId> = entry
                            .resolution_hints
                            .iter()
                            .filter_map(|hint| clause_proofs.get(hint).copied())
                            .collect();
                        tracing::warn!(
                            clause_id = entry.id,
                            clause = ?entry_clause_terms,
                            resolution_hints = ?entry.resolution_hints,
                            ?error,
                            trust_fallbacks = self.trust_fallback_count,
                            "sat proof reconstruction fell back to trust"
                        );
                        proof.add_rule_step(
                            AletheRule::Trust,
                            entry_clause_terms.clone(),
                            premises,
                            Vec::new(),
                        )
                    }
                }
            };

            clause_proofs.insert(entry.id, clause_proof);

            if entry_clause_terms.is_empty() {
                // Only accept if the derivation is meaningful (has premises).
                // A premise-less trust step for the empty clause is a fallback
                // that should not prevent derive_empty_from_units/assumptions
                // from producing a better proof (#4686).
                let is_meaningful = match proof.get_step(clause_proof) {
                    Some(ProofStep::Step { premises, .. }) => !premises.is_empty(),
                    Some(ProofStep::Resolution { .. }) => true,
                    _ => false,
                };
                if is_meaningful {
                    final_empty = Some(clause_proof);
                } else if weak_empty.is_none() {
                    weak_empty = Some(clause_proof);
                }
            }
        }

        final_empty
            .or_else(|| self.derive_empty_from_units(&clause_terms, &clause_proofs, proof))
            .or_else(|| self.derive_empty_from_assumptions(proof))
            // Keep a premise-less empty trust step as a last resort so
            // process_trace can still return a contradiction when no better
            // derivation exists (e.g., original empty clause inputs).
            .or(weak_empty)
    }

    /// Number of learned clauses that fell back to `AletheRule::Trust` due
    /// to failed resolution hint reconstruction.
    ///
    /// A non-zero count means the proof contains unverified steps. The proof
    /// is structurally valid but the trust nodes bypass independent checking.
    pub(crate) fn trust_fallback_count(&self) -> u32 {
        self.trust_fallback_count
    }

    /// Check if the trace can be processed (has necessary variable mappings).
    ///
    /// Note: This method checks if clauses can be translated without actually
    /// modifying the TermStore, so it uses the var_to_term map directly.
    pub(crate) fn can_process(&self, trace: &ClauseTrace) -> bool {
        if trace.is_empty() {
            return trace.has_empty_clause();
        }

        trace.entries().iter().any(|entry| {
            entry.clause.iter().all(|lit| {
                let var_idx = lit.variable().index() as u32;
                self.var_to_term.contains_key(&var_idx)
            })
        })
    }
}
