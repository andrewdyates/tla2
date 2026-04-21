// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `EufSolver`.
//!
//! Implements the DPLL(T) theory interface: assert, check, propagate, push/pop.
//! Conflict detection helpers are in `theory_check.rs`, propagation helpers
//! in `theory_propagate.rs`.

use z4_core::term::TermId;
use z4_core::{
    unwrap_not, DiscoveredEquality, EqualityPropagationResult, TheoryLit, TheoryPropagation,
    TheoryResult, TheorySolver,
};

use crate::solver::EufSolver;
use crate::types::{CongruenceTable, EqualityReason, MergeReason, UndoRecord};

impl TheorySolver for EufSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let debug = self.debug_euf;

        assert!(
            (literal.0 as usize) < self.terms.len(),
            "BUG: EUF assert_literal: term {} out of range (term store len={})",
            literal.0,
            self.terms.len()
        );

        let (term, val) = unwrap_not(self.terms, literal, value);
        if debug && term != literal {
            safe_eprintln!(
                "[EUF ASSERT] NOT term {} unwrapped to inner {} with value {}",
                literal.0,
                term.0,
                val
            );
        }

        if debug {
            // Check if it's an equality
            if let Some((lhs, rhs)) = self.decode_eq(term) {
                safe_eprintln!(
                    "[EUF ASSERT] eq term {} (terms {} == {}) = {}",
                    term.0,
                    lhs.0,
                    rhs.0,
                    val
                );
            }
        }
        self.record_assignment(term, val);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        let debug = self.debug_euf;
        tracing::debug!(
            assigns = self.assigns.len(),
            dirty = self.dirty,
            incremental = true,
            "EUF check"
        );

        if debug {
            safe_eprintln!(
                "[EUF] check() called: dirty={}, assigns={}, incremental={}",
                self.dirty,
                self.assigns.len(),
                true
            );
        }

        // 0) Direct conflict: term assigned both true and false
        if let Some(conflict_term) = self.pending_conflict.take() {
            if debug {
                safe_eprintln!("[EUF CHECK] Direct conflict on term {}", conflict_term.0);
            }
            debug_assert!(
                (conflict_term.0 as usize) < self.terms.len(),
                "BUG: EUF direct conflict: term {} out of range (term store len={})",
                conflict_term.0,
                self.terms.len()
            );
            // Return conflict clause: {term=true, term=false} -> both are in conflict
            self.conflict_count += 1;
            return TheoryResult::Unsat(vec![
                TheoryLit::new(conflict_term, true),
                TheoryLit::new(conflict_term, false),
            ]);
        }

        self.rebuild_closure();

        if debug {
            let eq_count = self
                .assigns
                .iter()
                .filter(|(t, &v)| v && self.decode_eq(**t).is_some())
                .count();
            safe_eprintln!("[EUF CHECK] {} equalities asserted true", eq_count);
        }

        // 1-4) Check for conflicts in priority order (see theory_check.rs)
        if let Some(result) = self.check_disequality_conflicts() {
            return result;
        }
        if let Some(result) = self.check_distinct_conflicts() {
            return result;
        }
        if let Some(result) = self.check_constant_conflicts() {
            return result;
        }
        if let Some(result) = self.check_bool_congruence_conflicts() {
            return result;
        }

        if debug {
            safe_eprintln!("[EUF CHECK] Returning SAT");
        }

        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // Rebuild closure if needed
        if self.dirty {
            self.rebuild_closure();
        }

        // Ensure eq_terms index is built (lazy, one-time O(|terms|) scan)
        self.init_eq_terms();

        let mut propagations = Vec::new();

        // Positive equality propagation (see theory_propagate.rs)
        self.propagate_positive_equalities(&mut propagations);
        // Disequality propagation (#5575, see theory_propagate.rs)
        self.propagate_disequalities(&mut propagations);

        self.propagation_count += propagations.len() as u64;
        propagations
    }

    fn push(&mut self) {
        self.scopes.push(self.trail.len());
        // For incremental mode: save undo trail position
        self.undo_scopes.push(self.undo_trail.len());
    }

    fn pop(&mut self) {
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        debug_assert!(
            mark <= self.trail.len(),
            "BUG: EUF pop: scope mark {} exceeds trail length {}",
            mark,
            self.trail.len()
        );
        while self.trail.len() > mark {
            let Some((term, prev)) = self.trail.pop() else {
                debug_assert!(false, "BUG: trail underflow in pop()");
                break;
            };
            match prev {
                Some(v) => {
                    self.assigns.insert(term, v);
                }
                None => {
                    self.assigns.remove(&term);
                }
            }
        }

        // Replay undo records to restore E-graph state
        // This must always happen when undo_scopes is non-empty, regardless of
        // incremental/legacy EUF mode. The undo_scopes track E-graph merges
        // that need to be undone on backtrack.
        if !self.undo_scopes.is_empty() {
            let undo_mark = self.undo_scopes.pop().unwrap_or(0);
            debug_assert!(
                undo_mark <= self.undo_trail.len(),
                "BUG: EUF pop: undo scope mark {} exceeds undo trail length {}",
                undo_mark,
                self.undo_trail.len()
            );
            while self.undo_trail.len() > undo_mark {
                let Some(record) = self.undo_trail.pop() else {
                    debug_assert!(false, "BUG: undo trail underflow in pop()");
                    break;
                };
                match record {
                    UndoRecord::SetRoot {
                        node,
                        old_root,
                        old_next,
                    } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].root = old_root;
                            self.enodes[node as usize].next = old_next;
                        }
                    }
                    UndoRecord::SetClassSize { node, old_size } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].class_size = old_size;
                        }
                    }
                    UndoRecord::RemoveParent { node } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].parents.pop();
                        }
                    }
                    UndoRecord::RemoveEqualityEdge(a, b) => {
                        self.equality_edges.remove(&(a, b));
                    }
                    UndoRecord::UnmergeProofForest { node, old_root } => {
                        self.unmerge_proof_forest(node, old_root);
                    }
                    UndoRecord::RemoveSharedEqualityReason(a, b) => {
                        self.shared_equality_reasons.remove(&(a, b));
                    }
                }
            }
            self.to_merge.clear();
            // Rebuild congruence table from current enode state.
            // After undo replay, roots are restored correctly but the cong_table
            // is stale. Rebuilding from scratch is O(func_apps) — much cheaper than
            // storing and replaying Signature Vecs in undo records (#5575).
            if self.enodes_init && self.func_apps_init {
                self.cong_table.clear();
                for meta in &self.func_apps {
                    let sig =
                        CongruenceTable::make_signature(meta.func_hash, &meta.args, &self.enodes);
                    self.cong_table.insert(meta.term_id, sig);
                }
            }
        }

        // Clear N-O state on pop (#318, pattern from [P]90)
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        // shared_equality_reasons is now scope-aware via RemoveSharedEqualityReason
        // undo records (#4840). No blanket clear needed.
        self.func_app_values.clear(); // #385: derived from assignments

        // In incremental mode with active undo records, equality_edges are maintained
        // incrementally via RemoveEqualityEdge undo records (#5575). The blanket clear
        // is only needed for legacy mode where rebuild_closure() recreates all edges.
        // Clearing in incremental mode destroys lower-scope edges that explain() needs,
        // forcing unnecessary full rebuilds and degrading performance.
        if !self.enodes_init {
            // Enodes not yet initialized — blanket clear is safe.
            self.equality_edges.clear();
            self.dirty = true;
        } else {
            // Incremental mode: E-graph state is maintained by undo records above.
            // equality_edges are already cleaned by RemoveEqualityEdge records.
            // Refresh the UF mirror before returning so direct uf.find() readers
            // and extract_model() see the restored outer-scope partition.
            self.sync_egraph_to_uf();
            self.resync_func_app_values_from_assigns();
        }
        self.pending_conflict = None;
    }

    fn reset(&mut self) {
        let debug = self.debug_euf;
        if debug {
            safe_eprintln!(
                "[EUF] reset() called, clearing {} assigns",
                self.assigns.len()
            );
        }
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.uf.ensure_size(self.terms.len());
        self.uf.reset();
        self.equality_edges.clear();
        self.dirty = true;
        self.pending_conflict = None;

        // Reset incremental E-graph state
        self.enodes_init = false;
        self.enodes.clear();
        self.cong_table.clear();
        self.to_merge.clear();
        self.undo_trail.clear();
        self.undo_scopes.clear();
        // Clear Nelson-Oppen state
        self.shared_equality_reasons.clear();
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        // Clear function application values (#385)
        self.func_app_values.clear();
    }

    fn soft_reset(&mut self) {
        let debug = self.debug_euf;
        if debug {
            safe_eprintln!(
                "[EUF] soft_reset() called, clearing {} assigns",
                self.assigns.len()
            );
        }
        // Clear assignments but preserve closure state
        // The closure will be validated/rebuilt lazily in rebuild_closure
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.dirty = true;
        self.pending_conflict = None;

        // Reset e-graph state since equivalence classes are invalid after clear.
        self.enodes_init = false;
        self.enodes.clear();
        self.cong_table.clear();
        self.to_merge.clear();
        self.undo_trail.clear();
        self.undo_scopes.clear();
        self.equality_edges.clear();
        // Clear Nelson-Oppen state (equalities may change across soft resets)
        self.shared_equality_reasons.clear();
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        // Clear function application values (#385) - derived from assignments
        self.func_app_values.clear();
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        let debug = self.debug_euf;

        debug_assert!(
            (lhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_equality: lhs term {} out of range (term store len={})",
            lhs.0,
            self.terms.len()
        );
        debug_assert!(
            (rhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_equality: rhs term {} out of range (term store len={})",
            rhs.0,
            self.terms.len()
        );

        if debug {
            safe_eprintln!(
                "[EUF] assert_shared_equality: {} = {} (reason: {} literals)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Store the reason for later explanation (#320)
        // Use scoped undo records so pop() only removes this scope's entries (#4840).
        let key = Self::edge_key(lhs.0, rhs.0);
        let is_new_entry = !self.shared_equality_reasons.contains_key(&key);
        match self.shared_equality_reasons.get_mut(&key) {
            Some(existing) => {
                if reason.len() < existing.len() {
                    *existing = reason.to_vec();
                }
            }
            None => {
                self.shared_equality_reasons.insert(key, reason.to_vec());
            }
        }
        if is_new_entry {
            self.undo_trail
                .push(UndoRecord::RemoveSharedEqualityReason(key.0, key.1));
        }
        self.dirty = true;

        // Fix for #321: In incremental mode, enqueue the merge directly
        // Previously only stored the reason without queueing, so incremental_rebuild()
        // never processed shared equalities from Nelson-Oppen.
        {
            // Ensure enodes are initialized
            if !self.enodes_init {
                self.init_enodes();
            }
            // Ensure enodes array covers these terms
            self.ensure_enodes_size(lhs.0);
            self.ensure_enodes_size(rhs.0);

            // Only queue if not already in the same class
            let lhs_root = self.enode_find_const(lhs.0);
            let rhs_root = self.enode_find_const(rhs.0);
            if lhs_root != rhs_root {
                self.to_merge.push_back(MergeReason {
                    a: lhs.0,
                    b: rhs.0,
                    reason: EqualityReason::Shared,
                });

                if debug {
                    safe_eprintln!(
                        "[EUF] assert_shared_equality: {} = {} queued for incremental merge",
                        lhs.0,
                        rhs.0
                    );
                }
            }
        }
    }

    fn supports_euf_semantic_check(&self) -> bool {
        true
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        // EUF discovers equalities via asserted equality literals and congruence closure.
        // Drain pending propagations and return them to the Nelson-Oppen loop.
        let equalities: Vec<DiscoveredEquality> = self
            .pending_propagations
            .drain(..)
            .map(|(lhs, rhs, reason)| DiscoveredEquality::new(lhs, rhs, reason))
            .collect();

        let debug = self.debug_nelson_oppen;
        if debug && !equalities.is_empty() {
            safe_eprintln!(
                "[EUF N-O] Propagating {} equalities to other theories",
                equalities.len()
            );
        }

        EqualityPropagationResult {
            equalities,
            conflict: None,
        }
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("euf_checks", self.check_count),
            ("euf_conflicts", self.conflict_count),
            ("euf_propagations", self.propagation_count),
        ]
    }

    fn supports_theory_aware_branching(&self) -> bool {
        true
    }

    fn suggest_phase(&self, _atom: TermId) -> Option<bool> {
        // Force all theory atoms to be decided. For equality atoms, prefer
        // true (merge) — this gives congruence closure more equalities to
        // work with, increasing the chance of detecting conflicts early.
        // For non-equality atoms, prefer true as a default.
        Some(true)
    }
}
