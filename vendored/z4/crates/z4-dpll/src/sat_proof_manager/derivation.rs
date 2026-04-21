// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof derivation methods for [`SatProofManager`].
//!
//! Extracted from `mod.rs` — contains `add_original_clause_step`,
//! `derive_clause_from_hints`, `close_clause_via_originals`,
//! `derive_empty_from_units`, and `derive_empty_from_assumptions`.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    AletheRule, ClausificationProof, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaProof,
};

use super::{HintDerivationError, SatProofManager};

impl SatProofManager<'_> {
    pub(super) fn add_original_clause_step(
        terms: &mut TermStore,
        proof: &mut Proof,
        clause: &[TermId],
        existing_clause_map: &mut HashMap<Vec<TermId>, ProofId>,
        annotation: Option<&ClausificationProof>,
        theory_annotation: Option<&TheoryLemmaProof>,
    ) -> ProofId {
        let key = Self::normalize_clause(clause);
        if let Some(&id) = existing_clause_map.get(&key) {
            return id;
        }

        // Check for clausification proof annotation (#6031 Phase 3). When present,
        // emit a premiseless tautology rule step instead of assume + or.
        // Tautology rules (and_pos, or_neg, etc.) are axiomatic in Alethe.
        if let Some(annot) = annotation {
            let id = proof.add_rule_step(
                annot.rule.clone(),
                clause.to_vec(),
                Vec::new(),
                vec![annot.source_term],
            );
            existing_clause_map.insert(key, id);
            return id;
        }

        // Check for theory lemma annotation (#6031 Phase 4). When present,
        // emit a TheoryLemma proof step with the proper Alethe rule.
        if let Some(theory_annot) = theory_annotation {
            let id = if let Some(lia) = theory_annot.lia.clone() {
                proof.add_theory_lemma_with_lia(
                    "theory",
                    clause.to_vec(),
                    theory_annot.farkas.clone(),
                    theory_annot.kind,
                    lia,
                )
            } else {
                proof.add_theory_lemma_with_farkas_and_kind_opt(
                    "theory",
                    clause.to_vec(),
                    theory_annot.farkas.clone(),
                    theory_annot.kind,
                )
            };
            existing_clause_map.insert(key, id);
            return id;
        }

        // Original clauses are input axioms. Emit as Alethe `assume` steps
        // instead of `trust` so carcara accepts them without --allowed-rules
        // trust (#5420 Phase B).
        //
        // Unit clause: (assume hN literal)
        // Multi-literal: (assume hN (or l1 l2 ...))
        //                (step tM (cl l1 l2 ...) :rule or :premises (hN))
        let id = if clause.len() == 1 {
            let assume_id = proof.add_assume(clause[0], None);
            existing_clause_map.insert(key, assume_id);
            return assume_id;
        } else if clause.is_empty() {
            // Empty clause = trivially UNSAT input. Keep as trust since
            // (assume false) + decomposition is non-standard.
            let id =
                proof.add_rule_step(AletheRule::Trust, clause.to_vec(), Vec::new(), Vec::new());
            existing_clause_map.insert(key, id);
            return id;
        } else {
            // Multi-literal: assume the disjunction, then decompose via `or` rule.
            let or_term = terms.mk_or(clause.to_vec());
            let assume_id = proof.add_assume(or_term, None);
            proof.add_rule_step(AletheRule::Or, clause.to_vec(), vec![assume_id], Vec::new())
        };
        existing_clause_map.insert(key, id);
        id
    }

    pub(super) fn derive_clause_from_hints(
        &mut self,
        target_clause: &[TermId],
        resolution_hints: &[u64],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Result<ProofId, HintDerivationError> {
        let mut hint_ids = Vec::with_capacity(resolution_hints.len());
        let mut seen_hint_ids: HashSet<u64> = Default::default();
        for &hint_id in resolution_hints {
            if !seen_hint_ids.insert(hint_id) {
                continue;
            }
            if clause_terms.contains_key(&hint_id) && clause_proofs.contains_key(&hint_id) {
                hint_ids.push(hint_id);
            }
        }

        let (&first_id, rest) = hint_ids
            .split_first()
            .ok_or(HintDerivationError::NoUsableHints)?;
        let Some(first_clause) = clause_terms.get(&first_id) else {
            return Err(HintDerivationError::NoUsableHints);
        };
        let Some(&first_proof) = clause_proofs.get(&first_id) else {
            return Err(HintDerivationError::NoUsableHints);
        };
        let mut current_clause = first_clause.clone();
        let mut current_proof = first_proof;
        let mut resolved_any = false;

        for &hint_id in rest {
            let rhs_clause = match clause_terms.get(&hint_id) {
                Some(clause) => clause,
                None => continue,
            };
            let rhs_proof = match clause_proofs.get(&hint_id).copied() {
                Some(id) => id,
                None => continue,
            };

            let Some((pivot, resolvent)) = self.resolve_once(&current_clause, rhs_clause) else {
                continue;
            };

            current_proof =
                proof.add_resolution(resolvent.clone(), pivot, current_proof, rhs_proof);
            current_clause = resolvent;
            resolved_any = true;
        }

        if !resolved_any {
            if Self::clauses_equivalent(&current_clause, target_clause) {
                return Ok(current_proof);
            }
            // Try second-pass closure over existing original clauses before giving up.
            if let Some(closed_proof) = self.close_clause_via_originals(
                current_clause.clone(),
                current_proof,
                target_clause,
                clause_terms,
                clause_proofs,
                proof,
            ) {
                return Ok(closed_proof);
            }
            return Err(HintDerivationError::NoResolutionPivot {
                usable_hint_count: hint_ids.len(),
            });
        }

        if Self::clauses_equivalent(&current_clause, target_clause) {
            return Ok(current_proof);
        }

        // Second-pass closure: try resolving with already-emitted original clauses
        // to close the gap between the derived clause and the target (#6365).
        if let Some(closed_proof) = self.close_clause_via_originals(
            current_clause.clone(),
            current_proof,
            target_clause,
            clause_terms,
            clause_proofs,
            proof,
        ) {
            return Ok(closed_proof);
        }

        Err(HintDerivationError::FinalClauseMismatch {
            expected_clause: target_clause.to_vec(),
            derived_clause: current_clause,
        })
    }

    /// Second-pass closure over already-emitted original clauses (#6365).
    ///
    /// When direct hint replay produces a clause that doesn't match the target,
    /// search existing clause/proof pairs for resolution candidates that bring
    /// the current clause strictly closer to the target. Only uses clauses that
    /// already have proof IDs — no new axioms are synthesized.
    ///
    /// Progress metric: each resolution step must strictly reduce the number of
    /// literals in the current clause that are absent from the target clause.
    /// This guarantees termination and soundness.
    pub(super) fn close_clause_via_originals(
        &mut self,
        mut current_clause: Vec<TermId>,
        mut current_proof: ProofId,
        target_clause: &[TermId],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        let target_set: HashSet<TermId> = target_clause.iter().copied().collect();

        // Collect candidate clause IDs to avoid borrowing conflicts.
        let candidate_ids: Vec<u64> = clause_proofs.keys().copied().collect();

        let mismatch_count = |clause: &[TermId], target: &HashSet<TermId>| -> usize {
            clause.iter().filter(|lit| !target.contains(*lit)).count()
        };

        let mut current_mismatch = mismatch_count(&current_clause, &target_set);

        // Bounded iteration: at most one resolution step per round, restart
        // scan after each successful resolution. Progress is strictly monotone
        // (mismatch count must decrease), guaranteeing termination.
        const MAX_CLOSURE_ROUNDS: usize = 32;
        for _ in 0..MAX_CLOSURE_ROUNDS {
            if current_mismatch == 0 {
                break;
            }

            let mut made_progress = false;
            for &cid in &candidate_ids {
                let Some(rhs_clause) = clause_terms.get(&cid) else {
                    continue;
                };
                let Some(&rhs_proof) = clause_proofs.get(&cid) else {
                    continue;
                };

                let Some((pivot, resolvent)) = self.resolve_once(&current_clause, rhs_clause)
                else {
                    continue;
                };

                let new_mismatch = mismatch_count(&resolvent, &target_set);
                if new_mismatch < current_mismatch {
                    current_proof =
                        proof.add_resolution(resolvent.clone(), pivot, current_proof, rhs_proof);
                    current_clause = resolvent;
                    current_mismatch = new_mismatch;
                    made_progress = true;
                    break; // restart scan with the new clause
                }
            }

            if !made_progress {
                break;
            }
        }

        Self::clauses_equivalent(&current_clause, target_clause).then_some(current_proof)
    }

    pub(super) fn derive_empty_from_units(
        &mut self,
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        let mut unit_map: HashMap<TermId, ProofId> = HashMap::new();
        for (&clause_id, clause) in clause_terms {
            if clause.len() != 1 {
                continue;
            }
            let lit = clause[0];
            let Some(&lit_proof) = clause_proofs.get(&clause_id) else {
                continue;
            };
            let neg_lit = self.negate_term(lit);
            if let Some(&neg_proof) = unit_map.get(&neg_lit) {
                return Some(proof.add_resolution(Vec::new(), lit, lit_proof, neg_proof));
            }
            unit_map.insert(lit, lit_proof);
        }

        None
    }

    pub(super) fn derive_empty_from_assumptions(&mut self, proof: &mut Proof) -> Option<ProofId> {
        let assumptions: Vec<(ProofId, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(idx, step)| match step {
                ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
                _ => None,
            })
            .collect();

        let mut seen: HashMap<TermId, ProofId> = HashMap::new();
        for (id, term) in assumptions {
            let neg_term = self.negate_term(term);
            if let Some(&neg_id) = seen.get(&neg_term) {
                return Some(proof.add_resolution(Vec::new(), term, id, neg_id));
            }
            seen.insert(term, id);
        }

        None
    }
}
