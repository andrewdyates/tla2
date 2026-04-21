// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! On-the-fly self-subsumption (OTFS).
//!
//! During 1UIP conflict analysis, when the intermediate resolvent subsumes
//! the current reason clause, the reason clause is strengthened in-place by
//! removing the pivot literal (and any level-0 literals).
//!
//! Reference: CaDiCaL analyze.cpp:770-865 (`on_the_fly_strengthen`).

use crate::literal::Literal;
use crate::proof_manager::ProofAddKind;
use crate::solver::WatchOrderPolicy;
use crate::watched::ClauseRef;

impl super::Solver {
    /// Strengthen a reason clause via on-the-fly self-subsumption.
    ///
    /// Removes the pivot variable and any level-0 literals from the clause,
    /// updates watched literals, and emits proof obligations.
    ///
    /// Returns `true` if the clause was strengthened.
    pub(super) fn otfs_strengthen(&mut self, reason_ref: ClauseRef, pivot: Literal) -> bool {
        let clause_idx = reason_ref.0 as usize;
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
        let old_size = old_lits.len();
        // NOTE: proof-mode stability (solve_proof_mode) is asserted centrally
        // in proof_emit.rs — no per-caller check needed here.

        // Precondition: pivot must appear in the clause
        debug_assert!(
            old_lits.iter().any(|l| l.variable() == pivot.variable()),
            "BUG: OTFS pivot {pivot:?} not found in clause {clause_idx}",
        );
        // Precondition: one of the watched literals must be true (propagated)
        debug_assert!(
            old_size < 2 || self.lit_val(old_lits[0]) > 0 || self.lit_val(old_lits[1]) > 0,
            "BUG: OTFS clause {clause_idx} has no true watched literal",
        );

        // Cannot strengthen binary or unit clauses (CaDiCaL analyze.cpp:772)
        if old_size <= 2 {
            return false;
        }

        // LRAT mode requires a full resolution hint chain for each strengthening
        // step. OTFS currently lacks that chain construction, so keep the clause
        // unchanged rather than emit an invalid proof transition.
        if self.cold.lrat_enabled {
            return false;
        }

        // Build new literal list: remove pivot variable and level-0 literals
        let mut new_lits: Vec<Literal> = Vec::with_capacity(old_size);
        for &lit in &old_lits {
            let var_idx = lit.variable().index();
            if lit.variable() == pivot.variable() {
                continue;
            }
            if self.var_data[var_idx].level == 0 {
                continue;
            }
            new_lits.push(lit);
        }

        let new_size = new_lits.len();

        // CaDiCaL analyze.cpp:903: strengthened clause must be strictly shorter
        debug_assert!(
            new_size < old_size,
            "BUG: OTFS strengthened clause not shorter ({new_size} >= {old_size})"
        );
        // No duplicate literals after removing pivot/level-0 lits
        debug_assert!(
            {
                let mut sorted: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                sorted.sort_unstable();
                sorted.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: OTFS strengthened clause has duplicate variables"
        );

        // Must have at least 2 literals remaining and must actually shrink.
        // CaDiCaL analyze.cpp:844-851: new_size==1 bails, new_size==2 allowed.
        if new_size < 2 || new_size >= old_size {
            return false;
        }

        // 2WL maintenance after OTFS: the pivot (propagated literal) was removed,
        // so ALL remaining literals are false under the current assignment.
        // Arrange the two highest-level false literals at watch positions 0 and 1
        // so BCP fires correctly on backtrack.
        // CaDiCaL reference: analyze.cpp:826-841.
        let old_watch0 = old_lits[0];
        let old_watch1 = old_lits[1];

        // All remaining literals must be falsified (pivot was the only true one)
        debug_assert!(
            new_lits.iter().all(|&lit| self.lit_val(lit) < 0),
            "BUG: OTFS strengthened clause has non-false literal in clause {clause_idx}",
        );

        // Put highest-level literal at position 0
        let mut best0 = 0;
        let mut best0_level = self.var_data[new_lits[0].variable().index()].level;
        for (i, &lit) in new_lits.iter().enumerate().skip(1) {
            let lv = self.var_data[lit.variable().index()].level;
            if lv > best0_level {
                best0 = i;
                best0_level = lv;
            }
        }
        if best0 != 0 {
            new_lits.swap(0, best0);
        }

        // Put second-highest-level literal at position 1
        let mut best1 = 1;
        let mut best1_level = self.var_data[new_lits[1].variable().index()].level;
        for (i, &lit) in new_lits.iter().enumerate().skip(2) {
            let lv = self.var_data[lit.variable().index()].level;
            if lv > best1_level {
                best1 = i;
                best1_level = lv;
            }
        }
        if best1 != 1 {
            new_lits.swap(1, best1);
        }

        // Post-sort: position 0 at highest level, position 1 at second-highest
        debug_assert!(
            new_lits[2..].iter().all(|&lit| {
                self.var_data[lit.variable().index()].level
                    <= self.var_data[new_lits[1].variable().index()].level
            }),
            "BUG: OTFS new_lits[1] not at second-highest level in clause {clause_idx}",
        );
        // Watched literals must be distinct (CaDiCaL implicit invariant)
        debug_assert_ne!(
            new_lits[0], new_lits[1],
            "BUG: OTFS watched literals are identical: {:?}",
            new_lits[0],
        );

        // Remove old watches
        self.remove_watch(old_watch0, reason_ref);
        self.remove_watch(old_watch1, reason_ref);

        // DRAT/LRAT proof obligations: add strengthened, delete original.
        // CaDiCaL reference: analyze.cpp:807-822 (LRAT mini_chain handling).
        let old_id = self.clause_id(reason_ref);
        // OTFS strengthening: for LRAT, pass the old clause ID as a hint.
        let hints: Vec<u64> = if self.cold.lrat_enabled && old_id != 0 {
            vec![old_id]
        } else {
            Vec::new()
        };
        // OTFS strengthening is a self-subsumption resolution step (CaDiCaL
        // analyze.cpp:807-822). The strengthened clause is semantically derived
        // but is NOT RUP-derivable from the forward checker's clause set (the
        // checker doesn't mirror the solver's search assignment — see proof_manager
        // comment at the Derived/LRAT branch). Use TrustedTransform so the
        // forward checker verifies well-formedness (non-empty, non-tautological,
        // not fully-falsified) without requiring a full RUP derivation.
        if let Ok(new_id) = self.proof_emit_add(&new_lits, &hints, ProofAddKind::TrustedTransform) {
            // Update clause ID mapping: the clause at this index now has a new
            // LRAT ID (the old ID was deleted). Without this update,
            // clause_id(reason_ref) returns the stale deleted ID.
            let idx = reason_ref.0 as usize;
            if new_id != 0 && idx < self.cold.clause_ids.len() {
                self.cold.clause_ids[idx] = new_id;
            }
            // Sync next_clause_id so subsequent learned clauses don't
            // collide with IDs allocated by the proof manager.
            if new_id != 0 && new_id >= self.cold.next_clause_id {
                self.cold.next_clause_id = new_id;
            }
        }
        let _ = self.proof_emit_delete(&old_lits, old_id);
        self.clear_level0_reasons_removed_by_replacement(clause_idx, &old_lits, &new_lits, old_id);

        // Replace clause in-place (old literals become garbage)
        self.drain_pending_garbage_mark(clause_idx);
        self.arena.replace(clause_idx, &new_lits);
        self.arena.set_saved_pos(clause_idx, 2);
        self.arena
            .set_used(clause_idx, crate::clause_arena::MAX_USED);
        // CaDiCaL analyze.cpp:850: post-replace size must match new_lits
        debug_assert_eq!(
            self.arena.len_of(clause_idx),
            new_lits.len(),
            "BUG: OTFS clause_db header len {} != new_lits.len() {} after replace",
            self.arena.len_of(clause_idx),
            new_lits.len(),
        );

        // Add new watches. Binary clauses use implicit binary watch encoding.
        let is_binary = new_size == 2;
        let watched = self
            .prepare_watched_literals(&mut new_lits, WatchOrderPolicy::Preserve)
            .expect("OTFS strengthened clauses have >= 2 literals");
        self.attach_clause_watches(reason_ref, watched, is_binary);

        self.stats.otfs_strengthened += 1;
        true
    }
}
