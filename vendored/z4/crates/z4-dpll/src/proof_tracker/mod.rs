// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof Tracking for SMT Solving
//!
//! This module provides proof generation during SMT solving. When enabled,
//! the solver collects proof steps that can be exported in Alethe format
//! for independent verification using tools like carcara.
//!
//! ## tRust Integration
//!
//! Proof certificates are critical for tRust (verified Rust compiler):
//! - Verification conditions are checked by Z4
//! - Proof certificates allow independent verification of results
//! - Unsat proofs are especially important for proving safety properties
//!
//! ## Alethe Proof Format
//!
//! The proof tracker generates steps compatible with the Alethe format:
//! - `assume`: Input assertions from the SMT-LIB problem
//! - `step`: Inference steps with rules, premises, and conclusion clauses
//! - Theory lemmas are recorded with appropriate theory-specific rules
//!
//! ## Usage
//!
//! ```no_run
//! use z4_dpll::Executor;
//! use z4_frontend::parse;
//! use z4_proof::export_alethe;
//!
//! let input = r#"
//!     (set-option :produce-proofs true)
//!     (set-logic QF_UF)
//!     (declare-const a Bool)
//!     (assert a)
//!     (assert (not a))
//!     (check-sat)
//! "#;
//! let commands = parse(input).unwrap();
//! let mut exec = Executor::new();
//! let outputs = exec.execute_all(&commands).unwrap();
//! assert_eq!(outputs, vec!["unsat"]);
//!
//! if let Some(proof) = exec.last_proof() {
//!     let alethe = export_alethe(proof, exec.terms());
//!     println!("{}", alethe);
//! }
//! ```

#[cfg(test)]
mod tests;

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::TermId;
use z4_core::{FarkasAnnotation, Proof, ProofId, TheoryLemmaKind};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct LemmaKey {
    kind: TheoryLemmaKind,
    clause: Vec<TermId>,
    farkas: Option<Vec<(i64, i64)>>,
}

impl LemmaKey {
    fn new(kind: TheoryLemmaKind, clause: &[TermId], farkas: Option<&FarkasAnnotation>) -> Self {
        Self {
            kind,
            clause: clause.to_vec(),
            farkas: farkas.map(|f| {
                f.coefficients
                    .iter()
                    .map(|c| {
                        let mut numer = *c.numer();
                        let mut denom = *c.denom();
                        if denom < 0 {
                            numer = -numer;
                            denom = -denom;
                        }
                        (numer, denom)
                    })
                    .collect()
            }),
        }
    }
}

/// Proof tracker for collecting SMT proof steps during solving
///
/// The tracker collects:
/// 1. Assumptions from input assertions
/// 2. Theory lemmas from theory solver conflicts
/// 3. Resolution steps from SAT solver (when available)
///
/// ## Incremental scoping
///
/// Push/pop scope the accumulated proof steps. On `pop()`, all proof steps
/// added since the matching `push()` are removed, along with their
/// deduplication entries. This prevents stale theory lemmas from appearing
/// in proofs after a scope retraction (#4534).
#[derive(Debug, Default)]
pub(crate) struct ProofTracker {
    /// The accumulated proof
    proof: Proof,
    /// Mapping from assertion term IDs to their proof step IDs
    assumption_map: HashMap<TermId, ProofId>,
    /// Mapping from theory lemma content to proof step IDs
    lemma_map: HashMap<LemmaKey, ProofId>,
    /// Whether proof tracking is enabled
    enabled: bool,
    /// Theory name for the current solving context
    theory_name: String,
    /// Scope stack for incremental push/pop (stores proof step watermarks)
    scope_stack: Vec<usize>,
}

impl ProofTracker {
    /// Create a new proof tracker (disabled by default)
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            proof: Proof::new(),
            assumption_map: HashMap::new(),
            lemma_map: HashMap::new(),
            enabled: false,
            theory_name: "UNKNOWN".to_string(),
            scope_stack: Vec::new(),
        }
    }

    /// Enable proof tracking
    pub(crate) fn enable(&mut self) {
        self.enabled = true;
    }

    /// Disable proof tracking
    pub(crate) fn disable(&mut self) {
        self.enabled = false;
    }

    /// Check if proof tracking is enabled
    #[must_use]
    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Set the theory name for subsequent theory lemmas
    pub(crate) fn set_theory(&mut self, theory: impl Into<String>) {
        self.theory_name = theory.into();
    }

    /// Record an assumption (input assertion)
    ///
    /// Returns the proof step ID for this assumption, or None if tracking is disabled.
    pub(crate) fn add_assumption(&mut self, term: TermId, name: Option<String>) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        // Check if we already have this assumption
        if let Some(&id) = self.assumption_map.get(&term) {
            return Some(id);
        }

        let id = self.proof.add_assume(term, name);
        self.assumption_map.insert(term, id);
        Some(id)
    }

    /// Record a theory lemma (conflict clause from theory solver)
    ///
    /// The clause is the disjunction of literals that the theory solver derived.
    /// Returns the proof step ID for this lemma, or None if tracking is disabled.
    pub(crate) fn add_theory_lemma(&mut self, clause: Vec<TermId>) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        let key = LemmaKey::new(TheoryLemmaKind::Generic, &clause, None);

        // Check if we already have this lemma
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

        let id = self.proof.add_theory_lemma(&self.theory_name, clause);
        self.lemma_map.insert(key, id);
        Some(id)
    }

    /// Record a theory lemma (conflict clause) with a specified Alethe rule kind.
    pub(crate) fn add_theory_lemma_with_kind(
        &mut self,
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        let key = LemmaKey::new(kind, &clause, None);
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

        let id = self
            .proof
            .add_theory_lemma_with_kind(&self.theory_name, clause, kind);
        self.lemma_map.insert(key, id);
        Some(id)
    }

    /// Record an arithmetic theory lemma with Farkas coefficients and explicit kind.
    pub(crate) fn add_theory_lemma_with_farkas_and_kind(
        &mut self,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
        kind: TheoryLemmaKind,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        debug_assert!(
            farkas.coefficients.len() == clause.len(),
            "BUG: Farkas coefficient count ({}) != clause length ({})",
            farkas.coefficients.len(),
            clause.len()
        );

        let key = LemmaKey::new(kind, &clause, Some(&farkas));
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

        let id = self.proof.add_theory_lemma_with_farkas_and_kind(
            &self.theory_name,
            clause,
            farkas,
            kind,
        );
        self.lemma_map.insert(key, id);
        Some(id)
    }

    /// Take ownership of the accumulated proof
    pub(crate) fn take_proof(&mut self) -> Proof {
        std::mem::take(&mut self.proof)
    }

    /// Get the number of proof steps
    #[must_use]
    pub(crate) fn num_steps(&self) -> usize {
        self.proof.len()
    }

    /// Reset proof content for a new solving session without clearing scope state.
    ///
    /// Used between check-sat calls in incremental mode. Unlike `reset()` (from
    /// `IncrementalSubsystem`), this preserves the scope_stack so that push/pop
    /// incremental scoping remains balanced.
    pub(crate) fn reset_session(&mut self) {
        self.proof = Proof::new();
        self.assumption_map.clear();
        self.lemma_map.clear();
        // Scope stack preserved — push/pop balance maintained across check-sat calls.
        // Update watermarks to point into the now-empty proof.
        for watermark in &mut self.scope_stack {
            *watermark = 0;
        }
        // Keep enabled state and theory name
    }
}

impl crate::incremental_state::IncrementalSubsystem for ProofTracker {
    /// Save a scope checkpoint. All proof steps added after this point
    /// will be removed by the matching `pop()`.
    fn push(&mut self) {
        self.scope_stack.push(self.proof.steps.len());
    }

    /// Restore to the last `push()` checkpoint: remove all proof steps,
    /// assumptions, and lemma dedup entries added since then.
    /// Returns false if no matching push exists.
    fn pop(&mut self) -> bool {
        if let Some(watermark) = self.scope_stack.pop() {
            self.proof.steps.truncate(watermark);
            // Remove map entries whose ProofId points beyond the watermark
            let cutoff = watermark as u32;
            self.assumption_map.retain(|_, id| id.0 < cutoff);
            self.lemma_map.retain(|_, id| id.0 < cutoff);
            self.proof.named_steps.retain(|_, id| id.0 < cutoff);
            true
        } else {
            false
        }
    }

    /// Reset the tracker for a new solving session
    fn reset(&mut self) {
        self.proof = Proof::new();
        self.assumption_map.clear();
        self.lemma_map.clear();
        self.scope_stack.clear();
        // Keep enabled state and theory name
    }
}
