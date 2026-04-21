// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT learned clause management, resolution chain collection, and
//! eager subsumption for conflict analysis.
//!
//! Proof ID queries and level-0 unit chain BFS are in
//! `conflict_analysis_lrat_unit_chain.rs`.

use super::*;
use crate::kani_compat::DetHashSet;
use crate::solver_log::solver_log;

impl Solver {
    #[allow(clippy::ptr_arg)]
    fn add_learned_clause_inner(
        &mut self,
        lits: &mut Vec<Literal>,
        lbd: u32,
        resolution_chain: &[u64],
    ) -> ClauseRef {
        // CaDiCaL analyze.cpp:521: learned clause must be non-empty
        debug_assert!(
            !lits.is_empty(),
            "BUG: add_learned_clause called with empty clause"
        );
        // No duplicate literals in learned clause
        debug_assert!(
            {
                let mut sorted = lits.iter().map(|l| l.0).collect::<Vec<_>>();
                sorted.sort_unstable();
                sorted.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: learned clause contains duplicate literals"
        );

        // Reorder so lits[1] is the highest-level non-UIP literal (#3785).
        // Matches CaDiCaL analyze.cpp:826-841.
        let watched = self.prepare_watched_literals(lits, WatchOrderPolicy::LearnedBacktrack);

        // Log the learned clause to proof if enabled.
        // #8105: With backward LRAT reconstruction as the primary proof path,
        // learned clauses in LRAT mode are reserved (ID allocated without writing
        // to the proof file) during solving. The backward reconstruction writes
        // them post-UNSAT with proper hints. DRAT mode continues to emit as
        // before (no hints needed).
        let emitted_id = if self.cold.lrat_enabled && resolution_chain.is_empty() {
            // LRAT backward path: reserve an ID without writing to the proof file.
            // The backward reconstruction will produce proper LRAT additions with
            // hints after UNSAT is determined.
            if let Some(ref mut manager) = self.proof_manager {
                let reserved = manager.reserve_lrat_id_for_backward();
                Some(reserved)
            } else {
                Some(0)
            }
        } else {
            // DRAT mode or forward LRAT fallback (non-empty resolution chain).
            let reversed_chain: Vec<u64>;
            let emit_hints = if self.cold.lrat_enabled && !resolution_chain.is_empty() {
                reversed_chain = Self::lrat_reverse_hints(resolution_chain);
                &reversed_chain[..]
            } else {
                resolution_chain
            };
            self.proof_emit_add_prechecked(lits, emit_hints, ProofAddKind::Derived)
                .ok()
        };
        // Sync next_clause_id with LRAT writer: deletion steps consume IDs
        // from the shared monotonic space, so the writer's returned ID may
        // be ahead of the solver's counter.
        if let Some(id) = emitted_id {
            if id != 0 && id >= self.cold.next_clause_id {
                self.cold.next_clause_id = id;
            }
        }

        // Atomic clause+hints insertion (#4435): hints are attached in a single
        // add_clause_db_checked call, eliminating the two-step add/set_resolution_hints
        // pattern that was the root cause of hint-loss regressions.
        // Learned clauses are always derived (forward_check_derived=true).
        // The LRAT-mode forward DRUP skip is handled inside add_clause_db_checked
        // (#7108) to avoid conflating the forward check flag with LRAT ID
        // assignment and ProofManager registration.
        let clause_idx = self.add_clause_db_checked(lits, true, true, resolution_chain);
        let clause_ref = ClauseRef(clause_idx as u32);
        self.arena.set_lbd(clause_idx, lbd);
        // CaDiCaL clause.cpp:140: mark_added only for likely_to_be_kept (#7393).
        // Deferred from add_clause_db_checked because LBD wasn't set yet.
        self.mark_subsume_dirty_if_kept(clause_idx);
        // CaDiCaL analyze.cpp:535: new learned clauses start with max_used protection
        self.arena
            .set_used(clause_idx, crate::clause_arena::MAX_USED);
        let clause_id = self.clause_id(clause_ref);
        let trace_clause_id = if clause_id == 0 {
            (clause_idx as u64) + 1
        } else {
            clause_id
        };
        self.trace_learn(trace_clause_id);
        solver_log!(
            self,
            "learn clause #{} lbd={} size={}",
            clause_idx,
            lbd,
            lits.len()
        );

        if let Some(watched) = watched {
            // Watch literals[0] (UIP) and literals[1] (highest level non-UIP).
            self.attach_clause_watches(clause_ref, watched, lits.len() == 2);
        }

        // Track for eager subsumption (CaDiCaL analyze.cpp:728-766).
        // Bound the trail: only the last EAGER_SUBSUME_LIMIT entries are
        // ever read (see eager_subsume). Without truncation the trail grows
        // to O(num_conflicts), wasting ~80 MB on 10M-conflict solves (#6278/F3).
        self.cold.learned_clause_trail.push(clause_idx);
        const TRAIL_CAPACITY: usize = 1024;
        if self.cold.learned_clause_trail.len() > TRAIL_CAPACITY {
            let keep = TRAIL_CAPACITY / 2;
            let drain = self.cold.learned_clause_trail.len() - keep;
            self.cold.learned_clause_trail.drain(..drain);
        }

        clause_ref
    }

    /// `rup_satisfied`: literals satisfied by the RUP assumption for the derived
    /// clause. Reason clauses containing any of these literals are trivially
    /// satisfied and must be omitted from the hint chain — strict checkers
    /// (lrat-check) reject hints with non-falsified literals (#5026).
    /// Pass an empty set when no filtering is needed.
    pub(crate) fn collect_resolution_chain(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Vec<u64> {
        let mut chain = Vec::new();
        // Reuse solver-owned LRAT bits in minimize_flags with sparse cleanup to avoid
        // O(num_vars) allocation/zeroing on every chain collection.
        // This function only needs one mark bit, so LRAT_A in minimize_flags is reused.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();

        let seed_id = self.clause_id(seed_clause);
        let seed_lits = self.arena.literals(seed_clause.0 as usize);
        // Filter the seed (conflict) clause if it contains a literal
        // satisfied by the RUP assumption. Under RUP, the checker assumes
        // the negation of the derived clause — a hint clause containing one
        // of those negated literals has a non-falsified (true) literal and
        // can never produce a conflict. Only its transitive dependencies
        // are still collected below. (#7108)
        let seed_is_satisfied =
            !rup_satisfied.is_empty() && seed_lits.iter().any(|l| rup_satisfied.contains(l));
        if seed_id != 0 && !seed_is_satisfied {
            chain.push(seed_id);
        }
        for &lit in seed_lits {
            let vi = lit.variable().index();
            if vi < self.num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        for &trail_lit in self.trail.iter().rev() {
            let vi = trail_lit.variable().index();
            if vi >= self.num_vars
                || self.min.minimize_flags[vi] & LRAT_A == 0
                || skip_var == Some(vi)
            {
                continue;
            }
            let reason_raw = self.var_data[vi].reason;
            if is_clause_reason(reason_raw) {
                let reason_ref = ClauseRef(reason_raw);
                // Check if the reason clause is satisfied by the RUP assumption.
                // If so, skip adding it as a hint but still traverse its literals
                // for transitive dependencies (#5026).
                let reason_lits = self.arena.literals(reason_ref.0 as usize);
                let reason_is_satisfied = !rup_satisfied.is_empty()
                    && reason_lits.iter().any(|l| rup_satisfied.contains(l));
                let reason_id = self.clause_id(reason_ref);
                if !reason_is_satisfied && reason_id != 0 {
                    chain.push(reason_id);
                }
                for &reason_lit in reason_lits {
                    let rvi = reason_lit.variable().index();
                    if rvi < self.num_vars && self.min.minimize_flags[rvi] & LRAT_A == 0 {
                        self.min.minimize_flags[rvi] |= LRAT_A;
                        self.min.lrat_to_clear.push(rvi);
                    }
                }
                continue;
            }
            // For unit_proof_id / level0_proof_id fallback: the original reason
            // clause was deleted; we can't inspect its literals. Check if the
            // variable itself has its trail literal in rup_satisfied, meaning
            // its original reason clause (which contained that trail literal)
            // would be satisfied. (#5026)
            if !rup_satisfied.is_empty() && rup_satisfied.contains(&trail_lit) {
                continue;
            }
            if let Some(unit_id) = self.visible_unit_proof_id_of_var_index(vi) {
                chain.push(unit_id);
            } else if let Some(id) = self.level0_var_proof_id(vi) {
                // Fallback: ClearLevel0 cleared reason[vi] but level0_proof_id
                // preserves the clause ID for LRAT derivation chains (#4617).
                chain.push(id);
            }
        }

        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();

        chain
    }

    /// Add a learned clause and return its reference (test-only convenience).
    ///
    /// Production code uses `add_conflict_learned_clause` for buffer recycling.
    /// This simpler API takes a borrowed chain and is used only in tests.
    #[cfg(test)]
    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_learned_clause(
        &mut self,
        lits: Vec<Literal>,
        lbd: u32,
        resolution_chain: &[u64],
    ) -> ClauseRef {
        let mut lits = lits;
        let clause_ref = self.add_learned_clause_inner(&mut lits, lbd, resolution_chain);
        self.conflict.return_learned_buf(lits);
        clause_ref
    }

    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_conflict_learned_clause(
        &mut self,
        lits: Vec<Literal>,
        lbd: u32,
        resolution_chain: Vec<u64>,
    ) -> ClauseRef {
        let mut lits = lits;
        let clause_ref = self.add_learned_clause_inner(&mut lits, lbd, &resolution_chain);
        self.conflict.return_learned_buf(lits);
        self.conflict.return_chain_buf(resolution_chain);
        clause_ref
    }

    /// Eagerly subsume recently learned clauses using the new clause.
    ///
    /// CaDiCaL `analyze.cpp:728-766`: after learning clause `c`, walk backward
    /// through the last `EAGER_SUBSUME_LIMIT` learned clauses. If `c` subsumes
    /// a candidate `d` (all literals of `c` appear in `d`), mark `d` as garbage.
    ///
    /// Uses `lit_marks` to mark the new clause's literals, then checks each
    /// candidate. Marks garbage with `mark_garbage_keep_data` so the clause data
    /// remains intact (the clause might still serve as a reason for an assigned
    /// variable). Cleanup happens during the next `reduce_db`.
    pub(super) fn eager_subsume(&mut self, new_clause_off: usize) {
        const EAGER_SUBSUME_LIMIT: usize = 20;

        let new_len = self.arena.len_of(new_clause_off);
        if new_len == 0 {
            return;
        }

        // Mark all literals in the new clause.
        for i in 0..new_len {
            self.lit_marks.mark(self.arena.literal(new_clause_off, i));
        }

        // Walk backward through recently learned clauses (skip the last entry
        // which is the new clause itself).
        let trail_len = self.cold.learned_clause_trail.len();
        let end = trail_len.saturating_sub(1);
        let start = end.saturating_sub(EAGER_SUBSUME_LIMIT);

        for i in (start..end).rev() {
            let cand_off = self.cold.learned_clause_trail[i];

            // Skip deleted or irredundant clauses.
            if !self.arena.is_active(cand_off) || !self.arena.is_learned(cand_off) {
                continue;
            }
            if self.arena.is_garbage(cand_off) {
                continue;
            }

            // Check if the new clause subsumes this candidate:
            // all literals of new_clause must appear in candidate.
            let cand_len = self.arena.len_of(cand_off);
            let mut needed = new_len as i32;
            for j in 0..cand_len {
                let lit = self.arena.literal(cand_off, j);
                if self.lit_marks.get(lit.variable()) == lit.sign_i8() {
                    needed -= 1;
                    if needed == 0 {
                        break;
                    }
                }
            }

            if needed == 0 {
                // New clause subsumes candidate — mark as garbage.
                // Keep data intact so it can still serve as a reason clause.
                self.arena.mark_garbage_keep_data(cand_off);
                self.cold.num_eager_subsumptions += 1;
            }
        }

        // Unmark.
        for i in 0..new_len {
            self.lit_marks.clear(self.arena.literal(new_clause_off, i));
        }
    }
}
