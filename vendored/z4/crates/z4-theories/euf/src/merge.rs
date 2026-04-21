// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF incremental merge operations.

use crate::solver::EufSolver;
use crate::types::{EqualityReason, MergeReason, UndoRecord};
use tracing::{debug, trace};
use z4_core::term::TermId;

impl EufSolver<'_> {
    /// Incrementally merge two equivalence classes.
    ///
    /// This is the core of the incremental E-graph. When two terms are asserted
    /// equal, we:
    /// 1. Find their representatives
    /// 2. Remove affected parent applications from the congruence table
    /// 3. Union the classes (smaller into larger for efficiency)
    /// 4. Reinsert parent applications - discovering new congruences
    /// 5. Record undo information for backtracking
    ///
    /// Complexity: O(parents(smaller_class)) per merge
    pub(crate) fn incremental_merge(&mut self, a: u32, b: u32, reason: EqualityReason) {
        let debug = self.debug_euf;
        self.debug_assert_enode_index(a, "incremental_merge lhs");
        self.debug_assert_enode_index(b, "incremental_merge rhs");

        let mut r1 = self.enode_find(a);
        let mut r2 = self.enode_find(b);
        self.debug_assert_enode_root_fixed_point(r1, "incremental_merge lhs representative");
        self.debug_assert_enode_root_fixed_point(r2, "incremental_merge rhs representative");

        debug!(
            target: "z4::euf",
            lhs = a,
            rhs = b,
            reason = ?&reason,
            lhs_rep = r1,
            rhs_rep = r2,
            "EUF incremental merge request"
        );

        if r1 == r2 {
            trace!(
                target: "z4::euf",
                lhs = a,
                rhs = b,
                representative = r1,
                "EUF incremental merge skipped; terms already equivalent"
            );
            return;
        }
        let proof_reason = reason.clone();
        let edge_key = Self::edge_key(a, b);
        #[cfg(not(kani))]
        if let hashbrown::hash_map::Entry::Vacant(e) = self.equality_edges.entry(edge_key) {
            e.insert(reason);
            self.undo_trail
                .push(UndoRecord::RemoveEqualityEdge(edge_key.0, edge_key.1));
        }
        #[cfg(kani)]
        if let std::collections::btree_map::Entry::Vacant(e) = self.equality_edges.entry(edge_key) {
            e.insert(reason);
            self.undo_trail
                .push(UndoRecord::RemoveEqualityEdge(edge_key.0, edge_key.1));
        }
        self.merge_proof_forest(a, b, proof_reason);

        if self.enodes[r1 as usize].class_size > self.enodes[r2 as usize].class_size {
            std::mem::swap(&mut r1, &mut r2);
        }
        self.debug_assert_enode_root_fixed_point(r1, "incremental_merge source class");
        self.debug_assert_enode_root_fixed_point(r2, "incremental_merge destination class");

        if debug {
            safe_eprintln!(
                "[EUF] incremental_merge: {} -> {} (merging class {} into {})",
                a,
                b,
                r1,
                r2
            );
        }

        let parents_to_reinsert: Vec<u32> = self.enodes[r1 as usize].parents.clone();
        for &parent in &parents_to_reinsert {
            if let Some(sig) = self.get_func_app_sig(parent) {
                self.cong_table.remove(&sig);
            }
        }

        let old_r1_next = self.enodes[r1 as usize].next;
        let old_r2_next = self.enodes[r2 as usize].next;
        let source_class_size = self.enodes[r1 as usize].class_size;
        let target_class_size_before = self.enodes[r2 as usize].class_size;
        #[allow(clippy::needless_collect)]
        let class_nodes: Vec<_> = self.enode_class_iter(r1).collect();
        for node in class_nodes {
            debug_assert_eq!(self.enodes[node as usize].root, r1);
            self.undo_trail.push(UndoRecord::SetRoot {
                node,
                old_root: r1,
                old_next: self.enodes[node as usize].next,
            });
            self.enodes[node as usize].root = r2;
        }

        self.undo_trail.push(UndoRecord::SetRoot {
            node: r2,
            old_root: r2,
            old_next: self.enodes[r2 as usize].next,
        });
        self.enodes[r1 as usize].next = old_r2_next;
        self.enodes[r2 as usize].next = old_r1_next;
        let old_r2_size = self.enodes[r2 as usize].class_size;
        self.undo_trail.push(UndoRecord::SetClassSize {
            node: r2,
            old_size: old_r2_size,
        });
        self.enodes[r2 as usize].class_size += source_class_size;
        debug_assert_eq!(
            self.enodes[r2 as usize].class_size,
            target_class_size_before + source_class_size,
            "BUG: incremental_merge class_size update mismatch"
        );
        for &parent in &parents_to_reinsert {
            if let Some(new_sig) = self.get_func_app_sig(parent) {
                if let Some(congruent) = self.cong_table.insert(parent, new_sig) {
                    if congruent != parent {
                        if let Some((parent_fh, parent_args)) = self.get_func_app_info(parent) {
                            if let Some((cong_fh, cong_args)) = self.get_func_app_info(congruent) {
                                let is_true_congruence = parent_fh == cong_fh
                                    && parent_args.len() == cong_args.len()
                                    && parent_args.iter().zip(cong_args.iter()).all(|(&a, &b)| {
                                        self.enode_find_const(a) == self.enode_find_const(b)
                                    });
                                if is_true_congruence {
                                    let arg_pairs: Vec<(TermId, TermId)> = parent_args
                                        .iter()
                                        .zip(cong_args.iter())
                                        .map(|(&a, &b)| (TermId(a), TermId(b)))
                                        .collect();

                                    let cong_reason = EqualityReason::Congruence {
                                        _term1: TermId(parent),
                                        _term2: TermId(congruent),
                                        arg_pairs,
                                    };

                                    if debug {
                                        safe_eprintln!(
                                            "[EUF] Found congruence: {} ~ {} (adding to worklist)",
                                            parent,
                                            congruent
                                        );
                                    }
                                    debug!(
                                        target: "z4::euf",
                                        parent_term = parent,
                                        congruent_term = congruent,
                                        "EUF congruence discovered during incremental merge"
                                    );

                                    self.to_merge.push_back(MergeReason {
                                        a: parent,
                                        b: congruent,
                                        reason: cong_reason,
                                    });

                                    let lhs = TermId(parent);
                                    let rhs = TermId(congruent);
                                    let pair = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
                                    if !self.propagated_eq_pairs.contains(&pair) {
                                        self.propagated_eq_pairs.insert(pair);
                                        let mut reasons = Vec::new();
                                        for (&a, &b) in parent_args.iter().zip(cong_args.iter()) {
                                            if a != b {
                                                let sub_reasons =
                                                    self.explain(TermId(a), TermId(b));
                                                reasons.extend(sub_reasons);
                                            }
                                        }
                                        reasons.sort_by_key(|l| (l.term.0, l.value));
                                        reasons.dedup_by_key(|l| (l.term.0, l.value));
                                        self.queue_pending_propagation(
                                            lhs,
                                            rhs,
                                            reasons,
                                            "incremental congruence",
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }

            self.enodes[r2 as usize].parents.push(parent);
            self.undo_trail.push(UndoRecord::RemoveParent { node: r2 });
        }

        trace!(
            target: "z4::euf",
            lhs = a,
            rhs = b,
            merged_into = r2,
            new_class_size = self.enodes[r2 as usize].class_size,
            reinserted_parents = parents_to_reinsert.len(),
            pending_merges = self.to_merge.len(),
            "EUF incremental merge completed"
        );

        #[cfg(debug_assertions)]
        self.debug_assert_enode_class_integrity(r2, "incremental_merge destination");
    }

    /// Rebuild the incremental merge queue from the current asserted state.
    /// Needed when queued merges were discarded on pop() before they were ever
    /// processed, but the surviving outer-scope assignments still need to be
    /// reflected in the E-graph.
    pub(crate) fn refill_incremental_merge_queue_from_state(&mut self) {
        self.scratch_equalities.clear();
        for (&lit_term, &value) in &self.assigns {
            if value {
                if let Some((lhs, rhs)) = self.decode_eq(lit_term) {
                    if lhs != rhs && self.terms.sort(lhs) == self.terms.sort(rhs) {
                        self.scratch_equalities.push((lit_term, lhs, rhs));
                    }
                }
            }
        }
        self.scratch_equalities
            .sort_by_key(|(lit_term, _, _)| *lit_term);
        for idx in 0..self.scratch_equalities.len() {
            let (lit_term, lhs, rhs) = self.scratch_equalities[idx];
            self.ensure_enodes_size(lhs.0);
            self.ensure_enodes_size(rhs.0);
            if self.enode_find_const(lhs.0) != self.enode_find_const(rhs.0) {
                self.to_merge.push_back(MergeReason {
                    a: lhs.0,
                    b: rhs.0,
                    reason: EqualityReason::Direct(lit_term),
                });
            }
        }

        self.scratch_shared_eq_keys.clear();
        self.scratch_shared_eq_keys
            .extend(self.shared_equality_reasons.keys().copied());
        self.scratch_shared_eq_keys.sort_unstable();
        for idx in 0..self.scratch_shared_eq_keys.len() {
            let (lhs, rhs) = self.scratch_shared_eq_keys[idx];
            self.ensure_enodes_size(lhs);
            self.ensure_enodes_size(rhs);
            if self.enode_find_const(lhs) != self.enode_find_const(rhs) {
                self.to_merge.push_back(MergeReason {
                    a: lhs,
                    b: rhs,
                    reason: EqualityReason::Shared,
                });
            }
        }
    }
}
