// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mediator for SAT proof emission and validation.
//!
//! All DRAT/LRAT writes are routed through `ProofManager` so callsites do not
//! manipulate `ProofOutput` directly. In LRAT mode this centralizes hint-ID
//! validation. In debug builds it also wires the online forward checker and
//! the LRAT chain verifier.

#[cfg(debug_assertions)]
use crate::forward_checker::ForwardChecker;
use crate::kani_compat::{det_hash_set_new, det_hash_set_with_capacity, DetHashSet};
#[cfg(debug_assertions)]
use crate::lrat_checker::LratChecker;
use crate::proof::ProofOutput;
use crate::Literal;
use std::io;

#[cfg(test)]
mod tests;

/// Classification for emitted proof additions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProofAddKind {
    /// Derived clause that should be RUP-checkable under current state.
    Derived,
    /// Trusted axiom step (for example, a theory lemma) that bypasses RUP check.
    Axiom,
    /// Trusted inprocessing transform that bypasses the full RUP check but
    /// still runs the forward checker's consistency verification (#4609).
    ///
    /// Unlike `Axiom` (which adds to the checker as original with no validation),
    /// `TrustedTransform` verifies the clause is well-formed: non-empty,
    /// non-tautological, and not already falsified under the current assignment.
    /// This catches the most common inprocessing bugs (emitting a clause that
    /// is immediately falsified) without requiring full RUP derivability.
    TrustedTransform,
}

/// Single mediator for SAT proof emission.
pub(crate) struct ProofManager {
    output: ProofOutput,
    lrat_mode: bool,
    /// Fail-close guard: once theory lemmas are seen in SMT mode, do not emit
    /// LRAT additions/deletions because they are not SAT-resolution derivations.
    lrat_blocked_by_theory_lemmas: bool,
    /// LRAT IDs known to the mediator (original + emitted additions).
    /// Always-on in LRAT mode: enables structural chain integrity checks
    /// in all builds (#5005). Empty in DRAT mode.
    known_lrat_ids: DetHashSet<u64>,
    /// LRAT IDs for TrustedTransform clauses that are NOT written to the
    /// LRAT proof file (#6270). These IDs are reserved in the ID space
    /// (known to the solver) but invisible to external checkers. Downstream
    /// hint chains must filter out these IDs before writing to the LRAT file.
    trusted_lrat_ids: DetHashSet<u64>,
    /// Next LRAT ID expected from the writer.
    /// Always-on in LRAT mode for hint validation (#5005).
    next_lrat_id: u64,
    #[cfg(debug_assertions)]
    checker: ForwardChecker,
    /// Online LRAT chain verifier (debug-only, active only in LRAT mode).
    #[cfg(debug_assertions)]
    lrat_checker: Option<LratChecker>,
    /// Buffer for original clauses awaiting their LRAT clause ID.
    /// The solver calls `register_original_clause` before `register_clause_id`
    /// for original clauses. Learned clauses skip `register_original_clause`,
    /// so only original clauses produce pending entries.
    #[cfg(debug_assertions)]
    pending_originals: Vec<Vec<Literal>>,
    /// Last emitted addition — clause literals and ID for uncommit (#4561).
    last_add: Option<(Vec<Literal>, u64)>,
}

impl ProofManager {
    /// Build a new proof manager around an existing proof output.
    pub(crate) fn new(output: ProofOutput, num_vars: usize) -> Self {
        let lrat_mode = matches!(&output, ProofOutput::Lrat(_));
        let _ = &num_vars;
        let next_lrat_id = match &output {
            ProofOutput::Drat(_) => 1,
            ProofOutput::Lrat(writer) => writer.next_id(),
        };

        Self {
            output,
            lrat_mode,
            lrat_blocked_by_theory_lemmas: false,
            known_lrat_ids: det_hash_set_new(),
            trusted_lrat_ids: det_hash_set_new(),
            next_lrat_id,
            #[cfg(debug_assertions)]
            checker: ForwardChecker::new(num_vars),
            #[cfg(debug_assertions)]
            lrat_checker: if lrat_mode {
                Some(LratChecker::new(num_vars))
            } else {
                None
            },
            #[cfg(debug_assertions)]
            pending_originals: Vec::new(),
            last_add: None,
        }
    }

    #[inline]
    pub(crate) fn is_lrat(&self) -> bool {
        self.lrat_mode
    }

    #[inline]
    pub(crate) fn lrat_id_visible_in_file(&self, clause_id: u64) -> bool {
        !self.lrat_mode || (clause_id != 0 && !self.trusted_lrat_ids.contains(&clause_id))
    }

    #[inline]
    pub(crate) fn block_lrat_for_theory_lemmas(&mut self) {
        if self.lrat_mode {
            self.lrat_blocked_by_theory_lemmas = true;
        }
    }

    #[inline]
    pub(crate) fn lrat_blocked_by_theory_lemmas(&self) -> bool {
        self.lrat_mode && self.lrat_blocked_by_theory_lemmas
    }

    #[inline]
    pub(crate) fn register_clause_id(&mut self, clause_id: u64) {
        if !self.lrat_mode || clause_id == 0 {
            return;
        }
        self.known_lrat_ids.insert(clause_id);
        if clause_id >= self.next_lrat_id {
            self.next_lrat_id = clause_id + 1;
        }
        // Keep the writer's counter past all original clause IDs so derived
        // clauses emitted via output.add() don't collide (#7108).
        self.output.advance_past(self.next_lrat_id);
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            if let Some(clause) = self.pending_originals.pop() {
                lrat.add_original(clause_id, &clause);
            }
        }
    }

    #[inline]
    pub(crate) fn register_original_clause(&mut self, _clause: &[Literal]) {
        #[cfg(debug_assertions)]
        self.checker.add_original(_clause);
        #[cfg(debug_assertions)]
        if self.lrat_checker.is_some() {
            self.pending_originals.push(_clause.to_vec());
        }
    }

    pub(crate) fn emit_add(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        debug_assert!(
            !clause.is_empty() || matches!(kind, ProofAddKind::Derived),
            "BUG: empty proof clause must be derived, got {kind:?}"
        );

        // Defense-in-depth: filter out sentinel ID 0 from hints before
        // validation and proof writing (#7957). Multiple hint-construction
        // paths can produce 0-valued entries when a clause has no assigned
        // LRAT ID (e.g., clause_id() returns 0 for unregistered clauses).
        // Some callers already filter (lrat_reverse_hints, BVE retain),
        // but not all do. Filtering here at the proof-manager boundary
        // prevents panics in release builds while preserving the
        // debug_assert in LratWriter::add for development visibility.
        debug_assert!(
            hints.iter().all(|&h| h != 0),
            "BUG: LRAT hints contain ID 0 (caller should filter) — \
             filtering defensively at proof-manager boundary"
        );
        let filtered_hints_buf: Vec<u64>;
        let hints = if self.lrat_mode && hints.contains(&0) {
            filtered_hints_buf = hints.iter().copied().filter(|&h| h != 0).collect();
            &filtered_hints_buf
        } else {
            hints
        };

        let mut suppress_lrat_write = false;
        #[cfg(debug_assertions)]
        match kind {
            ProofAddKind::Axiom => self.checker.add_original(clause),
            ProofAddKind::TrustedTransform => self.checker.add_trusted_transform(clause),
            ProofAddKind::Derived => {
                if !hints.is_empty() && self.lrat_mode {
                    self.checker.add_original(clause);
                } else {
                    self.checker.add_derived(clause);
                }
            }
        }
        if self.lrat_mode
            && matches!(kind, ProofAddKind::Axiom)
            && hints.is_empty()
            && !clause.is_empty()
        {
            self.lrat_blocked_by_theory_lemmas = true;
            suppress_lrat_write = true;
        }
        if self.lrat_mode && hints.is_empty() && matches!(kind, ProofAddKind::Axiom) {
            // Suppress Axiom clauses with empty hints — these are theory
            // lemmas that the LRAT checker cannot verify (no resolution chain).
            suppress_lrat_write = true;
        }
        // Suppress TrustedTransform UNIT clauses from LRAT output (#6270).
        // External LRAT checkers (lrat-check, z4-lrat-check) treat every
        // proof line as a derived clause requiring RUP verification.
        // TrustedTransform unit clauses with empty hints are typically NOT
        // RUP-derivable (they depend on semantic inprocessing reasoning like
        // failed literal detection). Writing them to the LRAT file causes
        // "NOT VERIFIED" failures.
        //
        // Non-unit TrustedTransform clauses (binary, ternary from BVE,
        // congruence, factorize) are usually RUP-derivable and are written
        // normally — downstream clauses reference them in hint chains.
        //
        // For suppressed units: reserve an ID (so the solver's internal
        // tracking works), register it in trusted_lrat_ids (so downstream
        // hint chains can filter it out), and add it to the online checker
        // as an original (for debug-build verification).
        if self.lrat_mode
            && matches!(kind, ProofAddKind::TrustedTransform)
            && clause.len() == 1
            && hints.is_empty()
        {
            let reserved_id = self.output.reserve_id();
            if reserved_id != 0 {
                self.known_lrat_ids.insert(reserved_id);
                self.trusted_lrat_ids.insert(reserved_id);
                self.next_lrat_id = reserved_id + 1;
                #[cfg(debug_assertions)]
                if let Some(ref mut lrat) = self.lrat_checker {
                    lrat.add_original(reserved_id, clause);
                }
            }
            self.last_add = Some((clause.to_vec(), reserved_id));
            return Ok(reserved_id);
        }
        if self.lrat_blocked_by_theory_lemmas() && !clause.is_empty() {
            suppress_lrat_write = true;
        }
        if suppress_lrat_write {
            if self.lrat_mode && !clause.is_empty() {
                self.output.reserve_id();
            }
            return Ok(0);
        }

        self.validate_lrat_hints(clause, hints, kind);

        // Deduplicate hint IDs for output (#5248) and filter out trusted
        // (suppressed) IDs for the LRAT file (#6270).
        //
        // Two hint sets are maintained:
        // - `file_hints`: for the LRAT file — deduped AND trusted IDs removed
        // - `checker_hints`: for the online checker — deduped but trusted IDs kept
        //
        // The online checker has TrustedTransform clauses as originals and needs
        // hint references to them for chain verification. The external checker
        // (lrat-check) never sees TrustedTransform clauses, so those hints must
        // be removed from the file output.
        let deduped_file_hints: Vec<u64>;
        let deduped_checker_hints: Vec<u64>;
        let (file_hints, _checker_hints): (&[u64], &[u64]) = if self.lrat_mode && !hints.is_empty()
        {
            let mut seen = det_hash_set_with_capacity(hints.len());
            // Checker hints: deduped only (keep trusted IDs).
            deduped_checker_hints = hints.iter().copied().filter(|h| seen.insert(*h)).collect();
            // File hints: deduped + trusted IDs removed.
            deduped_file_hints = deduped_checker_hints
                .iter()
                .copied()
                .filter(|h| !self.trusted_lrat_ids.contains(h))
                .collect();
            (&deduped_file_hints, &deduped_checker_hints)
        } else {
            (hints, hints)
        };

        let clause_id = self.output.add(clause, file_hints)?;
        if self.lrat_mode && clause_id != 0 {
            self.known_lrat_ids.insert(clause_id);
            self.next_lrat_id = clause_id + 1;

            // Feed LRAT chain verifier with the emitted clause and checker_hints
            // (which keep trusted IDs — the online checker has those clauses).
            #[cfg(debug_assertions)]
            if let Some(ref mut lrat) = self.lrat_checker {
                match kind {
                    ProofAddKind::Derived => {
                        // All derived clauses are added as originals in the
                        // online checker (#7108, #6270). The online checker
                        // cannot reliably verify hint chains because:
                        // - Learned clauses are opaque originals in the checker
                        // - TrustedTransform clauses lack RUP derivation chains
                        // - Empty clause hints may reference clauses not in the
                        //   checker's DB (e.g., deleted during inprocessing)
                        //
                        // Full proof validation is done by the external LRAT
                        // checker (lrat-check) which sees the complete proof
                        // file. The online checker provides structural
                        // defense-in-depth (clause DB consistency) only.
                        lrat.add_original(clause_id, clause);
                    }
                    ProofAddKind::Axiom => lrat.add_original(clause_id, clause),
                    ProofAddKind::TrustedTransform => {
                        // Should not be reached — TrustedTransform returns early above.
                        lrat.add_original(clause_id, clause);
                    }
                }
            }
        }
        self.last_add = Some((clause.to_vec(), clause_id));
        Ok(clause_id)
    }

    pub(crate) fn emit_delete(&mut self, clause: &[Literal], clause_id: u64) -> io::Result<()> {
        if self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        if self.lrat_mode && clause_id == 0 {
            #[cfg(debug_assertions)]
            self.checker.delete_clause(clause);
            return Ok(());
        }

        if self.lrat_mode && clause_id != 0 {
            assert!(
                self.known_lrat_ids.contains(&clause_id),
                "BUG: deleting unknown LRAT clause ID {clause_id}"
            );
        }
        #[cfg(debug_assertions)]
        if !clause.is_empty() {
            self.checker.delete_clause(clause);
        }
        // Trusted IDs were never written to the LRAT file (#6270).
        // Suppress the deletion line (external checker doesn't know about them)
        // but still update the online checker and internal tracking.
        if self.lrat_mode && self.trusted_lrat_ids.contains(&clause_id) {
            #[cfg(debug_assertions)]
            if let Some(ref mut lrat) = self.lrat_checker {
                lrat.delete(clause_id);
            }
            self.known_lrat_ids.remove(&clause_id);
            self.trusted_lrat_ids.remove(&clause_id);
            return Ok(());
        }
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            if self.lrat_mode && clause_id != 0 {
                lrat.delete(clause_id);
            }
        }
        self.output.delete(clause, clause_id)?;
        if self.lrat_mode && clause_id != 0 {
            self.known_lrat_ids.remove(&clause_id);
        }
        Ok(())
    }

    /// Reserve an LRAT ID for backward reconstruction without writing to the
    /// proof file (#8105).
    ///
    /// During solving with backward LRAT reconstruction as the primary path,
    /// learned clauses need an ID for solver-internal tracking (clause_ids,
    /// deletion, etc.) but should NOT be written to the LRAT proof file yet.
    /// The backward reconstruction will write them post-UNSAT with proper hints.
    ///
    /// The reserved ID is registered in `known_lrat_ids` so that:
    /// - Deletion steps can reference it (emit_delete checks known_lrat_ids)
    /// - The ID counter stays monotonic
    pub(crate) fn reserve_lrat_id_for_backward(&mut self) -> u64 {
        if !self.lrat_mode {
            return 0;
        }
        let id = self.output.reserve_id();
        if id != 0 {
            self.known_lrat_ids.insert(id);
            if id >= self.next_lrat_id {
                self.next_lrat_id = id + 1;
            }
        }
        id
    }

    /// Write a backward-reconstructed LRAT step to the proof file (#8105).
    ///
    /// Called during UNSAT finalization for each learned clause that is
    /// reachable from the empty clause. The step includes the clause's
    /// literals and LRAT hints (antecedent clause IDs).
    ///
    /// Unlike `emit_add`, this does NOT allocate a new ID -- the ID was
    /// already reserved during solving via `reserve_lrat_id_for_backward`.
    /// Instead, it writes the addition line using the pre-assigned ID.
    pub(crate) fn emit_backward_step(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<()> {
        if !self.lrat_mode || clause_id == 0 {
            return Ok(());
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        // Filter out trusted IDs and zero-valued hints.
        let filtered: Vec<u64> = if !self.trusted_lrat_ids.is_empty() {
            hints
                .iter()
                .copied()
                .filter(|h| *h != 0 && !self.trusted_lrat_ids.contains(h))
                .collect()
        } else {
            hints.iter().copied().filter(|h| *h != 0).collect()
        };
        // Write directly to the output using the pre-assigned clause_id.
        self.output.add_with_id(clause_id, clause, &filtered)?;
        Ok(())
    }

    #[inline]
    pub(crate) fn flush(&mut self) -> io::Result<()> {
        self.output.flush()
    }

    #[inline]
    pub(crate) fn added_count(&self) -> u64 {
        self.output.added_count()
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn deleted_count(&self) -> u64 {
        self.output.deleted_count()
    }

    #[inline]
    pub(crate) fn has_io_error(&self) -> bool {
        self.output.has_io_error()
    }

    #[inline]
    pub(crate) fn lrat_failures(&self) -> u64 {
        #[cfg(debug_assertions)]
        if let Some(ref lrat) = self.lrat_checker {
            return lrat.failures();
        }
        0
    }

    /// Register a clause as an LRAT axiom in the checker (debug-only).
    ///
    /// Allocates an ID from `next_lrat_id` (the unified counter that tracks
    /// the maximum across original clause IDs and proof writer IDs) to avoid
    /// collisions with IDs assigned by `register_clause_id`. Then advances the
    /// writer's counter past this ID so subsequent `emit_add` calls produce
    /// non-conflicting IDs.
    ///
    /// Returns the allocated ID so callers can advance solver-side counters
    /// (next_original_clause_id, next_clause_id) to prevent collisions with
    /// subsequent original clause additions.
    ///
    /// Used by `push()` to register ¬selector as an LRAT axiom (#7108).
    #[cfg(debug_assertions)]
    pub(crate) fn register_lrat_axiom(&mut self, clause: &[Literal]) -> u64 {
        if !self.lrat_mode {
            return 0;
        }
        let id = self.next_lrat_id;
        self.next_lrat_id += 1;
        self.known_lrat_ids.insert(id);
        // Keep the writer's counter synchronized so subsequent proof steps
        // (via output.add()) don't reuse this ID.
        self.output.advance_past(self.next_lrat_id);
        if let Some(ref mut lrat) = self.lrat_checker {
            lrat.add_original(id, clause);
        }
        id
    }

    #[cfg(debug_assertions)]
    pub(crate) fn checker_live_clause_count(&self) -> usize {
        self.checker.live_clause_count()
    }

    #[inline]
    pub(crate) fn output(&self) -> &ProofOutput {
        &self.output
    }

    #[inline]
    pub(crate) fn into_output(self) -> ProofOutput {
        self.output
    }

    /// Clear the last-add record so that `verify_unsat_chain` only validates
    /// the current finalization's empty clause, not a stale entry from a
    /// previous solve cycle or from `pop()`'s selector-clause emission (#7175).
    pub(crate) fn clear_last_add(&mut self) {
        self.last_add = None;
    }

    /// Structural LRAT chain integrity check: verify all hints reference
    /// known, live clause IDs. Always-on in all builds (#5005).
    fn validate_lrat_hints(&self, clause: &[Literal], hints: &[u64], kind: ProofAddKind) {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return;
        }
        if matches!(kind, ProofAddKind::Derived) {
            assert!(
                !hints.is_empty() || clause.len() <= 1,
                "BUG: LRAT derived clause requires hints unless unit/empty (clause len={})",
                clause.len()
            );
        }
        for &hint in hints {
            // Hint ID 0 is filtered at the emit_add boundary (#7957).
            // Keep as debug_assert for development visibility.
            debug_assert!(hint != 0, "BUG: LRAT hint contains clause ID 0");
            if hint == 0 {
                continue;
            }
            assert!(
                hint < self.next_lrat_id,
                "BUG: LRAT hint {hint} references future ID (next={})",
                self.next_lrat_id
            );
            assert!(
                self.known_lrat_ids.contains(&hint),
                "BUG: LRAT hint {hint} references unknown/deleted clause"
            );
        }
    }

    /// Post-UNSAT structural chain integrity check (#5005).
    ///
    /// Verifies the LRAT proof structure is consistent after finalization.
    /// This is an O(1) defense-in-depth check that runs in all builds.
    ///
    /// The per-emit `validate_lrat_hints` (always-on) checks each hint at
    /// emit time against `known_lrat_ids`, ensuring all hints reference
    /// known, live clause IDs. Combined with the monotonic ID invariant
    /// (`hint < next_lrat_id`), this guarantees every derivation chain
    /// terminates at original clauses (axioms). This method catches
    /// systemic issues at the proof boundary:
    ///
    /// 1. Empty ID tracking set (broken registration)
    /// 2. ID counter never advanced (no clauses emitted)
    /// 3. Last emitted clause was not the empty clause (incomplete proof)
    pub(crate) fn verify_unsat_chain(&self) {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return;
        }
        // The known_lrat_ids set must contain at least the original clauses
        // that were not deleted during solving. An empty set means tracking
        // was broken or all clauses were deleted (which is invalid — the
        // empty clause derivation requires at least some axioms).
        assert!(
            !self.known_lrat_ids.is_empty(),
            "BUG: LRAT ID tracking empty after UNSAT — no known clause IDs"
        );
        // next_lrat_id must have advanced past the initial value.
        assert!(
            self.next_lrat_id > 1,
            "BUG: LRAT next_id never advanced (next={})",
            self.next_lrat_id
        );
        // The last emitted addition must be the empty clause. An UNSAT proof
        // that doesn't end with an empty clause derivation is structurally
        // invalid — the proof manager may have been corrupted or the
        // finalization sequence was incomplete.
        if let Some((ref last_clause, last_id)) = self.last_add {
            assert!(
                last_clause.is_empty(),
                "BUG: LRAT proof did not end with empty clause (last add: {} lits, id={})",
                last_clause.len(),
                last_id
            );
        }
    }
}
