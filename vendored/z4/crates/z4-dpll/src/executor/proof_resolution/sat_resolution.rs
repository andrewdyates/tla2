// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{Proof, ProofStep, TermId, TheoryLemmaProof};

use super::congruence::try_derive_empty_via_congruence_bridging;
use super::empty_clause::{
    derive_empty_via_trust_lemma, try_derive_empty_via_contradictory_assumptions,
    try_derive_empty_via_equality_contradiction, try_derive_empty_via_th_resolution,
    try_derive_empty_via_theory_packet_resolution,
};
use crate::executor::Executor;

/// Extract theory lemma annotations from the accumulated proof (#6031 Phase 4).
fn extract_theory_lemma_proofs(proof: &Proof) -> HashMap<Vec<TermId>, TheoryLemmaProof> {
    let mut map = HashMap::new();
    for step in proof.steps.iter() {
        if let ProofStep::TheoryLemma {
            clause,
            farkas,
            kind,
            lia,
            ..
        } = step
        {
            let mut normalized = clause.clone();
            normalized.sort_unstable();
            normalized.dedup();
            map.entry(normalized).or_insert_with(|| TheoryLemmaProof {
                kind: *kind,
                farkas: farkas.clone(),
                lia: lia.clone(),
            });
        }
    }
    map
}

impl Executor {
    /// Ensure the proof derives the empty clause. Tries multiple strategies
    /// in order: single-lemma th_resolution, two-lemma packet resolution,
    /// congruence bridging, equality contradiction, SAT resolution,
    /// contradictory assumptions, then trust-lemma fallback.
    pub(crate) fn ensure_empty_clause_derivation(&mut self, proof: &mut Proof) {
        if Self::proof_derives_empty_clause(proof) {
            return;
        }
        if try_derive_empty_via_th_resolution(&self.ctx.terms, proof) {
            return;
        }
        if try_derive_empty_via_theory_packet_resolution(&self.ctx.terms, proof) {
            return;
        }
        if try_derive_empty_via_congruence_bridging(&mut self.ctx.terms, proof) {
            return;
        }
        // (#7913) Try equality contradiction before SAT resolution: the SAT
        // trace for preprocessed equality contradictions yields only trust
        // fallbacks. This strategy produces a proper LiaGeneric theory lemma.
        if try_derive_empty_via_equality_contradiction(&mut self.ctx.terms, proof) {
            return;
        }
        if self.try_derive_empty_via_sat_resolution(proof) {
            return;
        }
        if try_derive_empty_via_contradictory_assumptions(&self.ctx.terms, proof) {
            return;
        }
        derive_empty_via_trust_lemma(&mut self.ctx.terms, proof);
    }

    /// Try to derive the empty clause via SAT resolution reconstruction.
    ///
    /// Returns true if successful, false if the clause trace is not available or
    /// doesn't lead to an empty-clause derivation.
    fn try_derive_empty_via_sat_resolution(&mut self, proof: &mut Proof) -> bool {
        let trace = match self.last_clause_trace.take() {
            Some(t) => t,
            None => return false,
        };

        if !trace.has_empty_clause() {
            self.last_clause_trace = Some(trace);
            return false;
        }

        let var_to_term = match self.last_var_to_term.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                return false;
            }
        };

        let _negations = match self.last_negations.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                self.last_var_to_term = Some(var_to_term);
                return false;
            }
        };

        let theory_lemma_map = extract_theory_lemma_proofs(proof);

        let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
        if let Some(ref cp) = self.last_clausification_proofs {
            manager.set_clausification_proofs(cp);
        }
        if let Some(ref tp) = self.last_original_clause_theory_proofs {
            manager.set_original_clause_theory_proofs(tp);
        }
        if !theory_lemma_map.is_empty() {
            manager.set_theory_lemma_proofs(&theory_lemma_map);
        }

        if !manager.can_process(&trace) {
            return false;
        }

        let result = manager.process_trace(&trace, proof);
        let trust_count = manager.trust_fallback_count();
        if trust_count > 0 {
            tracing::warn!(
                trust_fallbacks = trust_count,
                "SAT proof reconstruction used {trust_count} trust fallback(s) — \
                 proof contains unverified steps"
            );
        }
        result.is_some_and(|empty_id| {
            let step = proof.get_step(empty_id);
            matches!(
                step,
                Some(ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. })
                    if clause.is_empty()
            )
        })
    }
}
