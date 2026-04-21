// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF explanation and proof-forest traversal.
//!
//! Congruence closure rebuilding lives in sibling `closure.rs`.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use std::collections::VecDeque;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::TermId;
use z4_core::{TheoryLit, TheoryResult};

use crate::solver::EufSolver;
use crate::types::{EqualityReason, UndoRecord};

impl EufSolver<'_> {
    /// Find the root of a node's proof-forest tree.
    /// Follows proof_target pointers until None (tree root).
    pub(crate) fn find_proof_root(&self, x: u32) -> u32 {
        let mut curr = x;
        while let Some(target) = self.enodes.get(curr as usize).and_then(|e| e.proof_target) {
            curr = target;
        }
        curr
    }

    /// Reverse the singly-linked proof-forest path from `node` to its root,
    /// making `node` the new root of its proof subtree.
    /// Port of Z3's euf_enode.cpp:133-148 reverse_justification().
    pub(crate) fn reverse_justification(&mut self, node: u32) {
        let mut curr = node;
        let mut prev_target: Option<u32> = None;
        let mut prev_just: Option<EqualityReason> = None;
        while let Some(target) = self.enodes[curr as usize].proof_target {
            let curr_just = self.enodes[curr as usize].proof_justification.take();
            self.enodes[curr as usize].proof_target = prev_target;
            self.enodes[curr as usize].proof_justification = prev_just;
            prev_target = Some(curr);
            prev_just = curr_just;
            curr = target;
        }
        self.enodes[curr as usize].proof_target = prev_target;
        self.enodes[curr as usize].proof_justification = prev_just;
    }

    /// Set a proof-forest edge from a to b with the given reason.
    /// Records an UnmergeProofForest undo record for incremental pop().
    /// Port of Z3's merge_justification().
    pub(crate) fn merge_proof_forest(&mut self, a: u32, b: u32, reason: EqualityReason) {
        let old_root = self.find_proof_root(a);
        if old_root == self.find_proof_root(b) {
            return;
        }
        self.reverse_justification(a);
        self.enodes[a as usize].proof_target = Some(b);
        self.enodes[a as usize].proof_justification = Some(reason);
        self.undo_trail
            .push(UndoRecord::UnmergeProofForest { node: a, old_root });
    }

    /// Undo a proof-forest merge. Called during pop() for UnmergeProofForest records.
    /// Port of Z3's unmerge_justification().
    pub(crate) fn unmerge_proof_forest(&mut self, node: u32, old_root: u32) {
        if (node as usize) < self.enodes.len() {
            self.enodes[node as usize].proof_target = None;
            self.enodes[node as usize].proof_justification = None;
        }
        if (old_root as usize) < self.enodes.len() {
            self.reverse_justification(old_root);
        }
    }

    /// Find the lowest common ancestor (LCA) of two nodes in the proof forest.
    /// Port of Z3's euf_egraph.cpp find_lca.
    pub(crate) fn find_lca(&self, a: u32, b: u32) -> u32 {
        let mut marks: HashSet<u32> = HashSet::new();
        let mut curr = a;
        marks.insert(curr);
        while let Some(target) = self.enodes.get(curr as usize).and_then(|e| e.proof_target) {
            marks.insert(target);
            curr = target;
        }
        curr = b;
        if marks.contains(&curr) {
            return curr;
        }
        while let Some(target) = self.enodes.get(curr as usize).and_then(|e| e.proof_target) {
            if marks.contains(&target) {
                return target;
            }
            curr = target;
        }
        curr
    }

    /// Collect reason literals along the proof-forest path from `from` to `to` (LCA).
    /// Handles Direct, Congruence (recursive explain for arg pairs), and Shared reasons.
    /// Returns `true` on success, `false` if the proof forest is broken.
    pub(crate) fn collect_path_reasons_proof_forest(
        &mut self,
        from: u32,
        to: u32,
        reasons: &mut Vec<TheoryLit>,
    ) -> bool {
        let mut curr = from;
        while curr != to {
            let just = self.enodes[curr as usize].proof_justification.clone();
            let target = self.enodes[curr as usize].proof_target;
            if let Some(just) = just {
                match just {
                    EqualityReason::Direct(eq_term) => {
                        reasons.push(TheoryLit::new(eq_term, true));
                    }
                    EqualityReason::Congruence { arg_pairs, .. } => {
                        for (arg_a, arg_b) in arg_pairs {
                            if arg_a != arg_b {
                                let sub = self.explain(arg_a, arg_b);
                                reasons.extend(sub);
                            }
                        }
                    }
                    EqualityReason::Shared => {
                        let target_node = target.unwrap_or(curr);
                        let key = Self::edge_key(curr, target_node);
                        if let Some(lits) = self.shared_equality_reasons.get(&key) {
                            reasons.extend(lits.iter().copied());
                        } else {
                            debug_assert!(
                                false,
                                "BUG: proof-forest Shared edge ({curr}, {target_node}) has no entry in shared_equality_reasons — scope-aware cleanup may be incomplete"
                            );
                            reasons.clear();
                            return false;
                        }
                    }
                    EqualityReason::BoolValue { term, value } => {
                        reasons.push(TheoryLit::new(term, value));
                        let other = target.unwrap_or(curr);
                        reasons.push(TheoryLit::new(TermId(other), value));
                    }
                    EqualityReason::Ite { condition, value } => {
                        reasons.push(TheoryLit::new(condition, value));
                    }
                }
            }
            match target {
                Some(next) => curr = next,
                None => {
                    debug_assert!(
                        false,
                        "BUG: proof-forest path broken at node {curr} before reaching LCA {to}"
                    );
                    reasons.clear();
                    return false;
                }
            }
        }
        true
    }

    pub(crate) fn all_true_equalities(&self) -> Vec<TheoryLit> {
        let mut keys: Vec<TermId> = self.assigns.keys().copied().collect();
        keys.sort_unstable(); // Deterministic iteration order (#3724)
        let mut out = Vec::new();
        for t in keys {
            if self.assigns[&t] && self.decode_eq(t).is_some() {
                out.push(TheoryLit::new(t, true));
            }
        }
        out
    }

    /// Explain why two terms are equal.
    ///
    /// In incremental mode: uses proof-forest LCA traversal (O(depth), no allocation).
    /// In legacy mode: falls back to BFS over equality_edges HashMap.
    ///
    /// The proof-forest approach fixes #3934: pop() no longer destroys pre-push
    /// equality information because proof edges are undone per-scope via
    /// UnmergeProofForest undo records, rather than cleared wholesale.
    pub fn explain(&mut self, a: TermId, b: TermId) -> Vec<TheoryLit> {
        let debug = self.debug_euf;
        self.debug_assert_solver_term_index(a, "explain lhs");
        self.debug_assert_solver_term_index(b, "explain rhs");
        if a == b {
            return Vec::new();
        }

        // Use proof-forest when available (incremental mode with initialized enodes)
        if self.enodes_init
            && (a.0 as usize) < self.enodes.len()
            && (b.0 as usize) < self.enodes.len()
        {
            let root_a = self.find_proof_root(a.0);
            let root_b = self.find_proof_root(b.0);
            if root_a == root_b {
                let lca = self.find_lca(a.0, b.0);
                self.debug_assert_explain_lca(lca, root_a);
                let mut reasons = Vec::new();
                let ok_a = self.collect_path_reasons_proof_forest(a.0, lca, &mut reasons);
                let ok_b = ok_a && self.collect_path_reasons_proof_forest(b.0, lca, &mut reasons);

                if ok_a && ok_b {
                    if debug {
                        safe_eprintln!(
                            "[EUF EXPLAIN] Proof-forest: {} to {} via LCA {}, {} reasons",
                            a.0,
                            b.0,
                            lca,
                            reasons.len()
                        );
                    }

                    reasons.sort_by_key(|l| (l.term.0, l.value));
                    reasons.dedup_by_key(|l| (l.term.0, l.value));
                    return reasons;
                }
                // Proof-forest walk failed (broken path or missing shared reason).
                // Fall through to BFS. (#6849, #3710)
                if debug {
                    safe_eprintln!(
                        "[EUF EXPLAIN] Proof-forest walk failed for {} to {}, BFS fallback",
                        a.0,
                        b.0
                    );
                }
            }
            // Not in same proof tree — fall through to BFS
            if debug {
                safe_eprintln!(
                    "[EUF EXPLAIN] Proof-forest: {} and {} not in same tree, BFS fallback",
                    a.0,
                    b.0
                );
            }
        }
        // Legacy BFS fallback (non-incremental mode or proof-forest unavailable)
        // We need to find paths through the actual term graph, not just representatives
        let mut visited: HashSet<u32> = HashSet::new();
        let mut queue: VecDeque<u32> = VecDeque::new();
        let mut parent: HashMap<u32, (u32, EqualityReason)> = HashMap::new();

        queue.push_back(a.0);
        visited.insert(a.0);

        // Build adjacency from equality_edges.
        // Sort neighbor lists by node ID for deterministic BFS paths (#3041).
        let mut adj: HashMap<u32, Vec<(u32, EqualityReason)>> = HashMap::new();
        for (&(x, y), reason) in &self.equality_edges {
            adj.entry(x).or_default().push((y, reason.clone()));
            adj.entry(y).or_default().push((x, reason.clone()));
        }
        for neighbors in adj.values_mut() {
            neighbors.sort_by_key(|(node, _)| *node);
        }

        while let Some(curr) = queue.pop_front() {
            if curr == b.0 {
                break;
            }
            if let Some(neighbors) = adj.get(&curr) {
                for (next, reason) in neighbors {
                    if !visited.contains(next) {
                        visited.insert(*next);
                        parent.insert(*next, (curr, reason.clone()));
                        queue.push_back(*next);
                    }
                }
            }
        }

        let mut reasons = Vec::new();
        let mut curr = b.0;

        if !parent.contains_key(&curr) && curr != a.0 {
            if debug {
                safe_eprintln!(
                    "[EUF EXPLAIN] No path from {} to {}, falling back",
                    a.0,
                    b.0
                );
            }
            return self.all_true_equalities();
        }

        while curr != a.0 {
            if let Some((prev, reason)) = parent.get(&curr) {
                self.collect_reason_literals(*prev, curr, reason, &mut reasons);
                curr = *prev;
            } else {
                break;
            }
        }

        if debug {
            safe_eprintln!(
                "[EUF EXPLAIN] Path from {} to {} needs {} reasons",
                a.0,
                b.0,
                reasons.len()
            );
        }

        reasons.sort_by_key(|l| (l.term.0, l.value));
        reasons.dedup_by_key(|l| (l.term.0, l.value));

        reasons
    }

    /// Recursively collect the direct equality literals for a reason
    pub(crate) fn collect_reason_literals(
        &mut self,
        a: u32,
        b: u32,
        reason: &EqualityReason,
        out: &mut Vec<TheoryLit>,
    ) {
        match reason {
            EqualityReason::Direct(eq_term) => {
                out.push(TheoryLit::new(*eq_term, true));
            }
            EqualityReason::Congruence { arg_pairs, .. } => {
                // For each argument pair that are in the same equivalence class,
                // we need to explain why they're equal
                for &(arg_a, arg_b) in arg_pairs {
                    // Use incremental enode structure if available, otherwise use uf
                    let (rep_a, rep_b) = (
                        self.enode_find_const(arg_a.0),
                        self.enode_find_const(arg_b.0),
                    );
                    if rep_a == rep_b && arg_a != arg_b {
                        // Recursively explain why arg_a = arg_b
                        let sub_reasons = self.explain(arg_a, arg_b);
                        out.extend(sub_reasons);
                    }
                }
            }
            EqualityReason::Shared => {
                // Shared equalities come from Nelson-Oppen with their own reasons
                // which are already tracked separately. For conflict explanation,
                // we look up the shared equality's reason literals.
                let key = Self::edge_key(a, b);
                if let Some(lits) = self.shared_equality_reasons.get(&key) {
                    out.extend(lits.iter().copied());
                }
            }
            EqualityReason::BoolValue { term, value } => {
                // Both endpoints share the same Bool truth value.
                // The reason is the truth-value assignment of both terms. (#4610)
                out.push(TheoryLit::new(*term, *value));
                // The other endpoint (the canonical representative) was merged
                // first and is found via the edge endpoints (a, b).
                let other = if *term == TermId(a) {
                    TermId(b)
                } else {
                    TermId(a)
                };
                out.push(TheoryLit::new(other, *value));
            }
            EqualityReason::Ite { condition, value } => {
                // ITE axiom: ite(c,t,e) = t when c=true, or ite(c,t,e) = e when c=false.
                // The reason is the truth-value assignment of the condition. (#5081)
                out.push(TheoryLit::new(*condition, *value));
            }
        }
    }

    #[allow(clippy::unused_self)] // method for consistency; may use self in future
    pub(crate) fn conflict_with_reasons(
        &self,
        mut reasons: Vec<TheoryLit>,
        lit: TheoryLit,
    ) -> TheoryResult {
        reasons.push(lit);
        // Keep the clause reasonably small by removing duplicates.
        reasons.sort_by_key(|l| (l.term, l.value));
        reasons.dedup_by_key(|l| (l.term, l.value));
        TheoryResult::Unsat(reasons)
    }
}
