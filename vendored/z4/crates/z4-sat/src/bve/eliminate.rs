// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE elimination: resolution, gate-aware elimination, and candidate filtering.

use super::{
    EliminationResult, ResolveAcc, ResolveClauseProfile, ResolveOutcome, WitnessEntry, BVE,
    ELIM_CLAUSE_SIZE_LIMIT,
};
use crate::clause::{
    clause_signature_bit, clause_signature_may_subsume,
    clause_signatures_may_resolve_tautologically,
};
use crate::clause_arena::ClauseArena;
#[cfg(test)]
use crate::elim_heap::ElimHeap;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

impl BVE {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_resolve_pair(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        pos: ResolveClauseProfile,
        neg: ResolveClauseProfile,
        marks: &mut LitMarks,
        vals: &[i8],
        acc: &mut ResolveAcc<'_>,
    ) -> bool {
        let pos_idx = pos.clause_idx;
        let neg_idx = neg.clause_idx;
        // CaDiCaL elim.cpp: variable must not already be eliminated
        debug_assert!(
            !self.eliminated[var.index()],
            "BUG: try_resolve_pair on eliminated variable {var:?}",
        );
        // Skip self-resolution: a tautological clause like (x ∨ ¬x) appears
        // in both positive and negative occurrence lists, so resolving it with
        // itself would remove the pivot pair and produce a spurious empty
        // resolvent, falsely signaling UNSAT.
        if pos_idx == neg_idx {
            return true;
        }
        if pos_idx >= clauses.len() || clauses.is_dead(pos_idx) {
            return true;
        }
        if neg_idx >= clauses.len() || clauses.is_dead(neg_idx) {
            return true;
        }

        let pos_lits = clauses.literals(pos_idx);
        let neg_lits = clauses.literals(neg_idx);
        let pos_pivot = Literal::positive(var);
        let neg_pivot = Literal::negative(var);

        debug_assert!(
            pos_lits.contains(&pos_pivot),
            "BUG: clause {pos_idx} from positive occurrence list for {var:?} is missing {pos_pivot:?}"
        );
        debug_assert!(
            neg_lits.contains(&neg_pivot),
            "BUG: clause {neg_idx} from negative occurrence list for {var:?} is missing {neg_pivot:?}"
        );

        if pos.tautological || neg.tautological {
            self.stats.tautologies_skipped += 1;
            return true;
        }

        // Signature-based resolvent size pre-filter (#7922): the union of two
        // clause signatures (pivot excluded during profile computation) gives a
        // lower bound on distinct resolvent variables. If this lower bound
        // exceeds ELIM_CLAUSE_SIZE_LIMIT, the resolvent is guaranteed too large.
        let combined_sig = pos.signature | neg.signature;
        if combined_sig.count_ones() as usize > ELIM_CLAUSE_SIZE_LIMIT {
            return true;
        }

        let outcome = if clause_signatures_may_resolve_tautologically(pos.signature, neg.signature)
        {
            self.resolve_with_marks(pos_lits, neg_lits, var, marks, vals)
        } else {
            self.stats.sig_fast_path += 1;
            self.resolve_without_tautology_checks(pos_lits, neg_lits, var, marks, vals)
        };

        match outcome {
            ResolveOutcome::Tautology => {
                return true;
            }
            ResolveOutcome::ParentSatisfied(first_parent) => {
                // CaDiCaL elim.cpp:316-325: mark satisfied parent as garbage.
                let satisfied_idx = if first_parent { pos_idx } else { neg_idx };
                acc.satisfied_parents.push(satisfied_idx);
                return true;
            }
            ResolveOutcome::Resolvent(resolvent, pruned_vars) => {
                if resolvent.is_empty() {
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                    *acc.found_empty_resolvent = true;
                    return true;
                }

                // NOTE: CaDiCaL does NOT forward-subsume resolvents during
                // BVE resolution (elim.cpp:264-460). A subsuming clause D
                // may be deleted in a later variable elimination within the
                // same BVE round, making the dropped resolvent needed. The
                // resolvent must be kept unconditionally. Forward subsumption
                // is a separate inprocessing pass that runs between BVE rounds,
                // where it is safe because no concurrent deletions occur.

                // CaDiCaL elim.cpp:396-403: unit resolvents are assigned
                // immediately and not counted toward the elimination bound.
                // The solver propagates them after the elimination round,
                // allowing subsequent variables to see a cleaner formula.
                if resolvent.len() == 1 {
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                    return true;
                }

                // CaDiCaL elim.cpp:509: reject if any resolvent exceeds elimclslim.
                if resolvent.len() > ELIM_CLAUSE_SIZE_LIMIT {
                    return false;
                }

                // CaDiCaL elim.cpp:409-447: self-subsuming resolution.
                // Check if the resolvent subsumes either (or both) parent clauses.
                // Use the 64-bit signature as a sound negative filter before the
                // O(r+p) mark scan to avoid work on obviously impossible cases.
                // Marks still replace the old O(r×p) Vec::contains path (#5075).
                let mut resolvent_signature = 0;
                for &lit in &resolvent {
                    marks.mark(lit);
                    resolvent_signature |= clause_signature_bit(lit);
                }
                let subsumes_pos = resolvent.len() < pos_lits.len()
                    && clause_signature_may_subsume(resolvent_signature, pos.signature)
                    && pos_lits
                        .iter()
                        .all(|lit| lit.variable() == var || marks.get(lit.variable()) != 0);
                let subsumes_neg = resolvent.len() < neg_lits.len()
                    && clause_signature_may_subsume(resolvent_signature, neg.signature)
                    && neg_lits
                        .iter()
                        .all(|lit| lit.variable() == var || marks.get(lit.variable()) != 0);
                marks.clear_clause(&resolvent);

                if subsumes_pos && subsumes_neg {
                    // CaDiCaL elim.cpp:413-424: Double self-subsuming resolution.
                    // The two antecedents are identical except for the pivot polarity.
                    // Strengthen one parent (remove pivot + root-level-false lits),
                    // garbage-collect the other. The resolvent is NOT added.
                    // CaDiCaL elim.cpp:215-223: also prune root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(pos_lits, var, vals);
                    // Merge root-level-false vars from both antecedents (resolution)
                    // with those from the parent itself for complete LRAT hints.
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, pos_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.double_otfs += 1;
                    // neg_idx is NOT strengthened — it stays in to_delete and the
                    // driver garbage-collects it. This removes one redundant clause.
                } else if subsumes_pos {
                    // CaDiCaL elim.cpp:431-437: Single self-subsuming resolution
                    // on the positive parent. Remove pivot + root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(pos_lits, var, vals);
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, pos_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.single_otfs += 1;
                    // Resolvent NOT added.
                } else if subsumes_neg {
                    // CaDiCaL elim.cpp:441-447: Single self-subsuming resolution
                    // on the negative parent. Remove pivot + root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(neg_lits, var, vals);
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, neg_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.single_otfs += 1;
                    // Resolvent NOT added.
                } else {
                    // No self-subsumption: add resolvent normally.
                    let rlen = resolvent.len() as u64;
                    self.stats.total_resolvent_literals += rlen;
                    self.stats.non_unit_resolvents += 1;
                    if rlen > self.stats.max_resolvent_len {
                        self.stats.max_resolvent_len = rlen;
                    }
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                }

                // CaDiCaL fastelim product shortcut: skip clause-count check when
                // the product of occurrence counts guarantees we're within budget.
                if !acc.clause_count_guaranteed
                    && acc.resolvents.len() > self.resolvent_budget(acc.clauses_removed)
                {
                    return false;
                }
            }
        }

        true
    }

    /// Find the best variable to eliminate (linear scan).
    ///
    /// Returns None if no suitable variable is found.
    /// The `frozen` slice contains reference counts - a variable is frozen if its count > 0.
    ///
    /// Note: production uses `next_candidate()` (priority queue) for better
    /// ordering. This linear scan is used by unit tests for simpler setup.
    #[cfg(test)]
    pub(super) fn find_elimination_candidate(
        &self,
        vals: &[i8],
        frozen: &[u32],
    ) -> Option<Variable> {
        let mut best_var: Option<Variable> = None;
        let mut best_score = u64::MAX;

        for var_idx in 0..self.num_vars {
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, frozen) else {
                continue;
            };

            // Gate-defined variables receive a credit that approximates the
            // gate×gate pairs skipped by restricted resolution.
            let score = ElimHeap::elim_score(var, &self.occ, &self.schedule_gate_pair_credit);

            if score < best_score {
                best_score = score;
                best_var = Some(var);
            }
        }

        best_var
    }

    /// Try to eliminate a specific variable.
    ///
    /// Convenience wrapper around `try_eliminate_with_gate_with_marks` that
    /// allocates fresh temporaries. Production code reuses marks/vals buffers
    /// via `try_eliminate_with_gate_with_marks` directly.
    #[cfg(test)]
    pub(crate) fn try_eliminate(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
    ) -> EliminationResult {
        self.try_eliminate_with_gate(var, clauses, None, false)
    }

    /// Try to eliminate a specific variable, optionally using restricted
    /// resolution if `gate_defining_clauses` is provided.
    ///
    /// Convenience wrapper that allocates fresh `LitMarks` and empty `vals`.
    /// Production code reuses shared buffers via `try_eliminate_with_gate_with_marks`.
    #[cfg(test)]
    pub(crate) fn try_eliminate_with_gate(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        gate_defining_clauses: Option<&[usize]>,
        resolve_gate_pairs: bool,
    ) -> EliminationResult {
        let mut marks = LitMarks::new(self.num_vars);
        let empty_vals: Vec<i8> = vec![0; self.num_vars * 2];
        self.try_eliminate_with_gate_with_marks(
            var,
            clauses,
            gate_defining_clauses,
            resolve_gate_pairs,
            &mut marks,
            &empty_vals,
        )
    }

    /// Try to eliminate a specific variable using shared marks, optionally with
    /// restricted resolution if `gate_defining_clauses` is provided.
    ///
    /// `vals` is the literal-indexed value array from the solver. At level 0,
    /// `vals[lit.index()] > 0` means the literal is root-level-true.
    pub(crate) fn try_eliminate_with_gate_with_marks(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        gate_defining_clauses: Option<&[usize]>,
        resolve_gate_pairs: bool,
        marks: &mut LitMarks,
        vals: &[i8],
    ) -> EliminationResult {
        let var_idx = var.index();

        // CaDiCaL elim.cpp:698: variable index must be within bounds
        debug_assert!(
            var_idx < self.num_vars,
            "BUG: try_eliminate_with_gate var {var:?} index {var_idx} >= num_vars {}",
            self.num_vars,
        );
        // CaDiCaL elim.cpp:700: gate defining clauses must reference valid indices
        debug_assert!(
            gate_defining_clauses
                .map(|g| g.iter().all(|&idx| idx < clauses.len()))
                .unwrap_or(true),
            "BUG: gate_defining_clauses contains index >= clauses.len() {}",
            clauses.len(),
        );
        debug_assert!(
            gate_defining_clauses.is_some() || !resolve_gate_pairs,
            "BUG: resolve_gate_pairs requires gate_defining_clauses"
        );

        // Check if already eliminated
        if var_idx < self.eliminated.len() && self.eliminated[var_idx] {
            return EliminationResult::not_eliminated(var);
        }

        // Check if elimination is bounded
        let (can_eliminate, resolvents, strengthened, satisfied_parents, resolution_attempts) =
            self.check_bounded_elimination_with_marks(
                var,
                clauses,
                gate_defining_clauses,
                resolve_gate_pairs,
                marks,
                vals,
            );

        if !can_eliminate {
            let mut result = EliminationResult::not_eliminated(var);
            result.resolution_attempts = resolution_attempts;
            return result;
        }

        // Collect clauses to delete
        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);

        let mut to_delete = Vec::new();
        let mut witness_entries = Vec::new();
        let mut seen = std::collections::HashSet::new();
        // CaDiCaL (elim.cpp:628): when a gate was detected, push ONLY gate
        // clauses to the reconstruction stack. Non-gate clauses are omitted
        // because the gate uniquely determines the eliminated variable's
        // value — the resolvents (gate × non-gate) encode the non-gate
        // constraints without the pivot. Pushing non-gate clauses causes
        // reconstruction oscillation: a non-gate clause can flip the pivot
        // to satisfy itself, breaking another non-gate clause that was
        // already satisfied before reconstruction.
        //
        // Without a gate, all clauses are pushed (no functional definition
        // exists, so reconstruction must check all clauses to find a
        // consistent assignment).
        for &(witness, occs) in &[
            (pos_lit, self.occ.get(pos_lit)),
            (neg_lit, self.occ.get(neg_lit)),
        ] {
            for &c_idx in occs {
                if c_idx >= clauses.len() || clauses.is_dead(c_idx) || !seen.insert(c_idx) {
                    continue;
                }
                to_delete.push(c_idx);
                // Push ALL clauses as witness entries regardless of gate.
                // CaDiCaL-style gate-only filtering was previously implemented
                // here but caused reconstruction failures when the gate didn't
                // fully capture the variable's semantic dependency.
                witness_entries.push(WitnessEntry {
                    clause_idx: c_idx,
                    witness,
                });
            }
        }

        let active_before = clauses.active_clause_count();
        // Only apply the 10% backstop on formulas large enough for the
        // percentage to be meaningful. On tiny formulas, additive
        // growth_bound is the intended sole budget control.
        if active_before >= 100 && resolvents.len() > to_delete.len() {
            let growth = resolvents.len() - to_delete.len();
            if growth.saturating_mul(10) > active_before {
                let mut result = EliminationResult::not_eliminated(var);
                result.resolution_attempts = resolution_attempts;
                return result;
            }
        }

        debug_assert!(
            to_delete.iter().all(|&idx| {
                idx < clauses.len()
                    && !clauses.is_dead(idx)
                    && clauses
                        .literals(idx)
                        .iter()
                        .any(|lit| lit.variable() == var)
            }),
            "BUG: deleted clause missing eliminated variable {var:?}"
        );
        debug_assert!(
            witness_entries.iter().all(|entry| {
                entry.clause_idx < clauses.len()
                    && !clauses.is_dead(entry.clause_idx)
                    && entry.witness.variable() == var
                    && clauses.literals(entry.clause_idx).contains(&entry.witness)
            }),
            "BUG: invalid witness entries for eliminated variable {var:?}"
        );
        #[cfg(debug_assertions)]
        {
            let to_delete_set: std::collections::HashSet<usize> =
                to_delete.iter().copied().collect();
            assert!(
                self.occ
                    .get(pos_lit)
                    .iter()
                    .chain(self.occ.get(neg_lit).iter())
                    .all(|&idx| {
                        if idx >= clauses.len() || clauses.is_dead(idx) {
                            return true;
                        }
                        if !clauses
                            .literals(idx)
                            .iter()
                            .any(|lit| lit.variable() == var)
                        {
                            return true;
                        }
                        to_delete_set.contains(&idx)
                    }),
                "BUG: active clause containing {var:?} is missing from deletion/witness set"
            );
        }
        // With gate-only witness entries, witness_entries <= to_delete.
        // Without a gate, they are equal (all clauses pushed).
        debug_assert!(
            witness_entries.len() <= to_delete.len(),
            "BUG: BVE: {} witness entries > {} deleted clauses for var {var:?}",
            witness_entries.len(),
            to_delete.len()
        );
        debug_assert!(
            gate_defining_clauses.is_some() || to_delete.len() == witness_entries.len(),
            "BUG: BVE non-gated: {} clauses deleted but {} witness entries for var {var:?}",
            to_delete.len(),
            witness_entries.len()
        );
        // Invariant: no resolvent should contain the eliminated variable.
        debug_assert!(
            resolvents
                .iter()
                .all(|(r, _, _, _)| r.iter().all(|l| l.variable() != var)),
            "BUG: resolvent contains eliminated variable {var:?}"
        );

        // Mark variable as eliminated
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = true;
        }

        // Update statistics
        self.stats.vars_eliminated += 1;
        self.stats.clauses_removed += to_delete.len() as u64;
        self.stats.resolvents_added += resolvents.len() as u64;
        for (r, _, _, _) in &resolvents {
            let rlen = r.len() as u64;
            self.stats.total_resolvent_literals += rlen;
            self.stats.non_unit_resolvents += 1;
            if rlen > self.stats.max_resolvent_len {
                self.stats.max_resolvent_len = rlen;
            }
        }

        EliminationResult {
            variable: var,
            to_delete,
            witness_entries,
            resolvents,
            strengthened,
            satisfied_parents,
            eliminated: true,
            resolution_attempts,
        }
    }
}
