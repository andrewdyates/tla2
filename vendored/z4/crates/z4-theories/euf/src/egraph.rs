// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental E-graph operations for `EufSolver`.
//!
//! Contains the worklist-based incremental merge infrastructure:
//! E-node initialization, find/union operations, class iteration,
//! congruence table management, and incremental rebuild.

use tracing::info;
use z4_core::term::{TermData, TermId};
use z4_core::TheoryLit;

use crate::solver::EufSolver;
use crate::types::{CongruenceTable, ENode, EqualityReason, MergeReason};

impl EufSolver<'_> {
    // ========================================================================
    // Incremental E-graph methods (Phase 1)
    // ========================================================================

    /// Initialize the E-node array and populate parent pointers.
    ///
    /// This is called lazily on first use. It:
    /// 1. Creates an ENode for each term
    /// 2. Registers function applications with their arguments' parent lists
    /// 3. Populates the congruence table with initial signatures
    pub(crate) fn init_enodes(&mut self) {
        if self.enodes_init {
            return;
        }

        // Ensure func_apps is initialized first
        self.init_func_apps();

        // Create ENodes for all terms
        self.enodes.clear();
        for term_id in self.terms.term_ids() {
            self.enodes.push(ENode::new(term_id.0));
        }

        // Register parent pointers for function applications
        for meta in &self.func_apps {
            for &arg in &meta.args {
                self.enodes[arg as usize].parents.push(meta.term_id);
            }
        }

        // Populate initial congruence table
        self.cong_table.clear();
        for meta in &self.func_apps {
            let sig = CongruenceTable::make_signature(meta.func_hash, &meta.args, &self.enodes);
            self.cong_table.insert(meta.term_id, sig);
        }

        self.enodes_init = true;
    }

    /// Ensure enodes array is sized for term_id.
    /// This handles terms added dynamically during CHC solving (lemma learning).
    pub(crate) fn ensure_enodes_size(&mut self, term_id: u32) {
        let needed = (term_id + 1) as usize;
        while self.enodes.len() < needed {
            let new_id = self.enodes.len() as u32;
            self.enodes.push(ENode::new(new_id));
        }
    }

    /// Find the representative of a term in the incremental E-graph.
    /// Uses path compression for efficiency.
    #[inline]
    pub(crate) fn enode_find(&mut self, x: u32) -> u32 {
        self.debug_assert_enode_index(x, "enode_find input");
        let root = self.enodes[x as usize].root;
        if root == x {
            return x;
        }
        // Path compression
        let final_root = self.enode_find(root);
        self.debug_assert_enode_root_fixed_point(final_root, "enode_find result");
        self.enodes[x as usize].root = final_root;
        final_root
    }

    /// Find representative without mutation (for use in const contexts)
    /// Returns x unchanged if term_id is beyond enodes array (dynamically added term).
    #[inline]
    /// Returns the equivalence class representative for term `x` (immutable).
    pub fn enode_find_const(&self, x: u32) -> u32 {
        if (x as usize) >= self.enodes.len() {
            return x; // Treat uninitialized terms as singletons
        }
        let mut curr = x;
        while self.enodes[curr as usize].root != curr {
            curr = self.enodes[curr as usize].root;
            if (curr as usize) >= self.enodes.len() {
                return x; // Corrupted state fallback
            }
        }
        curr
    }

    /// Check if two terms are in the same equivalence class.
    pub fn are_equal(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        self.enode_find_const(a.0) == self.enode_find_const(b.0)
    }

    /// Sync E-graph representatives to legacy UF structure.
    /// O(n log n) pass — sets UF parent of each term to its E-graph root.
    /// Uses enode_find_const (no path compression), so each find is O(depth)
    /// where depth is O(log n) due to merge-by-size. Total: O(n log n).
    /// This ensures callers using uf.find() see consistent results after
    /// incremental_rebuild(). (#5575)
    pub(crate) fn sync_egraph_to_uf(&mut self) {
        if !self.enodes_init {
            return;
        }
        self.uf.ensure_size(self.enodes.len());
        for i in 0..self.enodes.len() {
            let root = self.enode_find_const(i as u32);
            self.uf.parent[i] = root;
        }
    }

    /// Iterate over all members of an equivalence class.
    /// Uses the circular linked list.
    pub(crate) fn enode_class_iter(&self, root: u32) -> impl Iterator<Item = u32> + '_ {
        let start = root;
        let mut curr = root;
        let mut done = false;
        std::iter::from_fn(move || {
            if done {
                return None;
            }
            let result = curr;
            curr = self.enodes[curr as usize].next;
            if curr == start {
                done = true;
            }
            Some(result)
        })
    }

    // ========================================================================
    // Proof-forest methods (Z3-style explain)
    // Port of Z3's euf_egraph.cpp / euf_enode.cpp proof justification system.
    // The proof-forest is a tree embedded in ENode::proof_target/proof_justification
    // that records merge history for O(depth) explain without HashMap allocation.
    // ========================================================================

    /// Get function application info for a term (func_hash and argument ids).
    /// Clones the args Vec. Use get_func_app_sig() to avoid the clone when
    /// only the signature is needed.
    pub(crate) fn get_func_app_info(&self, term: u32) -> Option<(u64, Vec<u32>)> {
        let idx = self.func_app_index.get(&term)?;
        let meta = &self.func_apps[*idx];
        Some((meta.func_hash, meta.args.clone()))
    }

    /// Compute the congruence table signature for a function application term
    /// without cloning args — uses func_apps index directly (#5575).
    pub(crate) fn get_func_app_sig(&self, term: u32) -> Option<crate::types::Signature> {
        let idx = self.func_app_index.get(&term)?;
        let meta = &self.func_apps[*idx];
        Some(CongruenceTable::make_signature(
            meta.func_hash,
            &meta.args,
            &self.enodes,
        ))
    }

    /// Process the merge worklist until fixed point.
    ///
    /// Each merge can discover new congruences, which are added to the worklist.
    /// We process until no more merges are pending.
    pub(crate) fn incremental_propagate(&mut self) -> usize {
        let debug = self.debug_euf;
        let mut iterations = 0;
        let initial_pending = self.to_merge.len();

        while let Some(merge) = self.to_merge.pop_front() {
            iterations += 1;
            self.incremental_merge(merge.a, merge.b, merge.reason);
        }

        if debug && iterations > 0 {
            safe_eprintln!(
                "[EUF] incremental_propagate: {} merges processed",
                iterations
            );
        }

        if iterations > 0 {
            info!(
                target: "z4::euf",
                initial_pending,
                merges_processed = iterations,
                pending_after = self.to_merge.len(),
                "EUF incremental propagation summary"
            );
        }

        iterations
    }

    /// Process pending merges in the incremental E-graph.
    ///
    /// In true incremental mode, equalities are queued in record_assignment(),
    /// and we just process the worklist here. No full rebuild needed.
    pub(crate) fn incremental_rebuild(&mut self) {
        let debug = self.debug_euf;
        let initial_pending = self.to_merge.len();
        let mut merge_steps = 0usize;

        // If dirty but no pending merges, enodes might not be initialized
        // This happens on first call or after reset
        if !self.enodes_init {
            self.init_enodes();
        }

        if self.dirty && self.to_merge.is_empty() {
            self.refill_incremental_merge_queue_from_state();
        }

        // Process all pending merges from record_assignment()
        if !self.to_merge.is_empty() {
            if debug {
                safe_eprintln!(
                    "[EUF] incremental_rebuild: processing {} pending merges",
                    self.to_merge.len()
                );
            }
            merge_steps += self.incremental_propagate();
        }

        // Merge Bool-valued theory atoms sharing the same truth value.
        // Same logic as merge_bool_valued_atoms() but uses the incremental
        // merge path (to_merge queue) instead of uf.union(). (#4610)
        let bool_merge_candidates = self.incremental_merge_bool_valued_atoms();
        if !self.to_merge.is_empty() {
            merge_steps += self.incremental_propagate();
        }

        // ITE axiom: when the condition of ite(c, t, e) is assigned, merge the
        // ITE term with the selected branch (incremental path). (#5081)
        // Uses pre-indexed ITE term list to avoid O(|terms|) scan (#5575).
        self.init_ite_terms();
        let mut ite_merge_count = 0usize;
        // Iterate by index to avoid cloning ite_terms (#5575).
        let n_ite = self.ite_terms.len();
        for ite_i in 0..n_ite {
            let idx = self.ite_terms[ite_i];
            let term_id = TermId(idx);
            if let TermData::Ite(cond, then_t, else_t) = self.terms.get(term_id).clone() {
                let cond_val = match self.terms.get(cond) {
                    TermData::Not(inner) => self.assigns.get(inner).map(|&v| !v),
                    _ => self.assigns.get(&cond).copied(),
                };
                if let Some(val) = cond_val {
                    let branch = if val { then_t } else { else_t };
                    self.ensure_enodes_size(term_id.0);
                    self.ensure_enodes_size(branch.0);
                    let r1 = self.enode_find_const(term_id.0);
                    let r2 = self.enode_find_const(branch.0);
                    if r1 != r2 {
                        self.to_merge.push_back(MergeReason {
                            a: term_id.0,
                            b: branch.0,
                            reason: EqualityReason::Ite {
                                condition: cond,
                                value: val,
                            },
                        });
                        // Propagate ITE-derived equality to other theories via
                        // Nelson-Oppen (incremental path). (#5081)
                        let reason = vec![TheoryLit::new(cond, val)];
                        self.queue_pending_propagation(
                            term_id,
                            branch,
                            reason,
                            "incremental ITE branch equality",
                        );
                        ite_merge_count += 1;
                    }
                }
            }
        }
        if !self.to_merge.is_empty() {
            merge_steps += self.incremental_propagate();
        }

        // Sync E-graph representatives to legacy UF so all callers
        // (model extraction, explain, tests) see consistent state. O(n) pass.
        self.sync_egraph_to_uf();

        self.dirty = false;

        if merge_steps > 0
            || bool_merge_candidates > 0
            || ite_merge_count > 0
            || initial_pending > 0
        {
            info!(
                target: "z4::euf",
                assignments = self.assigns.len(),
                initial_pending,
                bool_merge_candidates,
                merge_steps,
                equality_edges = self.equality_edges.len(),
                "EUF incremental rebuild summary"
            );
        }
    }
}
