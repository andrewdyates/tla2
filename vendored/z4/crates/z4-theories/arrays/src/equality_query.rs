// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality query and explanation methods for the array theory solver.
//!
//! Provides:
//! - known_equal / known_distinct queries
//! - Equivalence class retrieval and representative computation
//! - Select conflict candidate pair generation
//! - Equality/disequality explanation for conflict clause generation
//! - BFS equality path search

use super::*;

impl ArraySolver<'_> {
    /// Check if two terms are known to be equal (direct equality asserted). O(1) via pair index.
    pub(crate) fn known_equal(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return true;
        }
        let key = Self::ordered_pair(t1, t2);
        if let Some(&eq_term) = self.eq_pair_index.get(&key) {
            if self.assigns.get(&eq_term) == Some(&true) {
                return true;
            }
        }
        self.equal_by_affine_form(t1, t2)
    }

    /// Check if two terms are known to be distinct.
    ///
    /// Uses O(1) constant check, O(1) diseq_set lookup, and O(|C1|×|C2|)
    /// equivalence class cross-product. Does NOT perform equality-substituted
    /// affine BFS (#6820): that reasoning belongs in the arithmetic theory,
    /// not the array theory. Z3 parity: `are_distinct()` is O(1) unique-value
    /// check only; index disequalities from `i = j + k` are propagated by
    /// the LRA/LIA solver into the EUF diseq_set.
    pub(crate) fn known_distinct(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return false;
        }

        // O(1): both are distinct constants (Z3 parity: is_unique_value).
        if self.known_distinct_direct(t1, t2) {
            return true;
        }

        // O(|C1|×|C2|): check equiv class members against diseq_set.
        self.known_distinct_via_equiv_classes(t1, t2)
    }

    /// Check equivalence class cross-product for known disequalities.
    fn known_distinct_via_equiv_classes(&self, t1: TermId, t2: TermId) -> bool {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            let c1 = self
                .equiv_class_map
                .get(&t1)
                .map(|&i| self.equiv_classes[i].as_slice());
            let c2 = self
                .equiv_class_map
                .get(&t2)
                .map(|&i| self.equiv_classes[i].as_slice());
            let t1_singleton = [t1];
            let t2_singleton = [t2];
            let c1 = c1.unwrap_or(&t1_singleton);
            let c2 = c2.unwrap_or(&t2_singleton);
            for &t1_equiv in c1 {
                for &t2_equiv in c2 {
                    if self.known_distinct_direct(t1_equiv, t2_equiv) {
                        return true;
                    }
                }
            }
        } else {
            // Fallback: BFS (used when cache hasn't been built yet, e.g. during propagate)
            let t1_class = self.get_equiv_class_bfs(t1);
            let t2_class = self.get_equiv_class_bfs(t2);
            for &t1_equiv in &t1_class {
                for &t2_equiv in &t2_class {
                    if self.known_distinct_direct(t1_equiv, t2_equiv) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Get the equivalence class of a term. Uses cached equiv classes when
    /// available (O(1) lookup), falls back to BFS when the cache is stale or unavailable.
    pub(crate) fn get_equiv_class(&self, term: TermId) -> Vec<TermId> {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            if let Some(&class_idx) = self.equiv_class_map.get(&term) {
                return self.equiv_classes[class_idx].clone();
            }
            // Term not in eq_adj — singleton class
            return vec![term];
        }

        self.get_equiv_class_bfs(term)
    }

    fn equiv_class_representative(&self, term: TermId) -> TermId {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            if let Some(&class_idx) = self.equiv_class_map.get(&term) {
                return self.equiv_classes[class_idx]
                    .iter()
                    .copied()
                    .min()
                    .unwrap_or(term);
            }
            return term;
        }

        self.get_equiv_class_bfs(term)
            .into_iter()
            .min()
            .unwrap_or(term)
    }

    /// Return select-term pairs that already have concrete distinctness evidence.
    ///
    /// `check_row2_extended()` and `check_nested_select_conflicts()` only need
    /// to inspect pairs whose values are already known distinct. Restricting the
    /// candidate set to those pairs avoids re-scanning every select combination
    /// in `final_check()` on large storeinv formulas.
    pub(crate) fn select_conflict_candidate_pairs(&self) -> Vec<(TermId, TermId)> {
        let mut selects_by_class: HashMap<TermId, Vec<TermId>> = HashMap::new();
        for &select_term in self.select_cache.keys() {
            selects_by_class
                .entry(self.equiv_class_representative(select_term))
                .or_default()
                .push(select_term);
        }
        for select_terms in selects_by_class.values_mut() {
            select_terms.sort_unstable_by_key(|term| term.0);
            select_terms.dedup();
        }

        let mut candidate_pairs = HashSet::new();
        for &(lhs, rhs) in &self.diseq_set {
            let lhs_class = self.equiv_class_representative(lhs);
            let rhs_class = self.equiv_class_representative(rhs);
            let Some(lhs_selects) = selects_by_class.get(&lhs_class) else {
                continue;
            };
            let Some(rhs_selects) = selects_by_class.get(&rhs_class) else {
                continue;
            };
            for &sel1 in lhs_selects {
                for &sel2 in rhs_selects {
                    if sel1 != sel2 {
                        candidate_pairs.insert(Self::ordered_pair(sel1, sel2));
                    }
                }
            }
        }

        let mut class_constants = Vec::new();
        for (&class_key, select_terms) in &selects_by_class {
            let constant = self
                .get_equiv_class(select_terms[0])
                .into_iter()
                .find_map(|term| match self.terms.get(term) {
                    TermData::Const(constant) => Some(constant.clone()),
                    _ => None,
                });
            if let Some(constant) = constant {
                class_constants.push((class_key, constant));
            }
        }
        class_constants.sort_unstable_by_key(|(class_key, _)| class_key.0);
        for i in 0..class_constants.len() {
            for j in (i + 1)..class_constants.len() {
                if class_constants[i].1 == class_constants[j].1 {
                    continue;
                }
                let lhs_selects = &selects_by_class[&class_constants[i].0];
                let rhs_selects = &selects_by_class[&class_constants[j].0];
                for &sel1 in lhs_selects {
                    for &sel2 in rhs_selects {
                        candidate_pairs.insert(Self::ordered_pair(sel1, sel2));
                    }
                }
            }
        }

        let mut candidate_pairs: Vec<_> = candidate_pairs.into_iter().collect();
        candidate_pairs.sort_unstable_by_key(|&(lhs, rhs)| (lhs.0, rhs.0));
        candidate_pairs
    }

    /// BFS fallback for equivalence class when cache is stale.
    fn get_equiv_class_bfs(&self, term: TermId) -> Vec<TermId> {
        let mut class = vec![term];
        let mut to_process = vec![term];
        let mut seen = HashSet::new();
        seen.insert(term);

        while let Some(t) = to_process.pop() {
            if let Some(neighbors) = self.eq_adj.get(&t) {
                for &(other, _eq_term) in neighbors {
                    if seen.insert(other) {
                        class.push(other);
                        to_process.push(other);
                    }
                }
            }
        }

        class
    }

    /// Build equality paths (as eq-term chains) from `start` to all reachable terms.
    pub(crate) fn equality_paths_from(&self, start: TermId) -> HashMap<TermId, Vec<TermId>> {
        let mut paths = HashMap::new();
        let mut queue = std::collections::VecDeque::new();
        paths.insert(start, Vec::new());
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            let current_path = paths.get(&current).cloned().unwrap_or_default();
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    if paths.contains_key(&other) {
                        continue;
                    }
                    let mut next_path = current_path.clone();
                    if !eq_term.is_sentinel() {
                        next_path.push(eq_term);
                    }
                    paths.insert(other, next_path);
                    queue.push_back(other);
                }
            }
        }

        paths
    }

    /// Build an asserted-equality path between two terms.
    ///
    /// Unlike `equality_paths_from`, this skips sentinel edges so the result
    /// contains only SAT-visible equality atoms that can be used as reasons.
    fn asserted_equality_path(&self, start: TermId, goal: TermId) -> Option<Vec<TermId>> {
        if start == goal {
            return Some(Vec::new());
        }

        let mut queue = std::collections::VecDeque::new();
        let mut seen = HashSet::new();
        let mut prev: HashMap<TermId, (TermId, TermId)> = HashMap::new();
        queue.push_back(start);
        seen.insert(start);

        while let Some(current) = queue.pop_front() {
            let Some(neighbors) = self.eq_adj.get(&current) else {
                continue;
            };
            for &(other, eq_term) in neighbors {
                if eq_term.is_sentinel() || !seen.insert(other) {
                    continue;
                }
                prev.insert(other, (current, eq_term));
                if other == goal {
                    let mut path = Vec::new();
                    let mut cursor = goal;
                    while cursor != start {
                        let &(parent, via_eq) = prev.get(&cursor)?;
                        path.push(via_eq);
                        cursor = parent;
                    }
                    path.reverse();
                    return Some(path);
                }
                queue.push_back(other);
            }
        }

        None
    }

    /// Explain why two terms are provably equal using only SAT-visible reasons.
    ///
    /// Returns:
    /// - `Some(vec![])` for tautological equalities (syntactic identity or
    ///   direct affine normalization)
    /// - `Some(non_empty)` when asserted equality atoms prove the equality
    /// - `None` when the equality is not provable without external/model-based
    ///   assumptions
    pub(crate) fn explain_equal_if_provable(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if t1 == t2 || self.equal_by_affine_form(t1, t2) {
            return Some(Vec::new());
        }

        if let Some(eq_term) = self.get_eq_term(t1, t2) {
            if self.assigns.get(&eq_term) == Some(&true) {
                return Some(vec![TheoryLit::new(eq_term, true)]);
            }
        }

        let mut reasons: Vec<_> = self
            .asserted_equality_path(t1, t2)?
            .into_iter()
            .map(|eq_term| TheoryLit::new(eq_term, true))
            .collect();
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
        Some(reasons)
    }

    /// Reconstruct a non-empty explanation for `t1 ≠ t2` when possible.
    fn explain_distinct(&self, t1: TermId, t2: TermId) -> Vec<TheoryLit> {
        if let Some(eq_term) = self.get_eq_term(t1, t2) {
            if self.assigns.get(&eq_term) == Some(&false) {
                return vec![TheoryLit::new(eq_term, false)];
            }
        }

        let lhs_paths = self.equality_paths_from(t1);
        let rhs_paths = self.equality_paths_from(t2);

        for (lhs_rep, lhs_path) in &lhs_paths {
            for (rhs_rep, rhs_path) in &rhs_paths {
                if let (TermData::Const(lhs_const), TermData::Const(rhs_const)) =
                    (self.terms.get(*lhs_rep), self.terms.get(*rhs_rep))
                {
                    if lhs_const != rhs_const {
                        let mut reasons = Vec::new();
                        for &path_eq in lhs_path {
                            if !path_eq.is_sentinel() {
                                reasons.push(TheoryLit::new(path_eq, true));
                            }
                        }
                        for &path_eq in rhs_path {
                            if !path_eq.is_sentinel() {
                                reasons.push(TheoryLit::new(path_eq, true));
                            }
                        }
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));
                        if !reasons.is_empty() {
                            return reasons;
                        }
                    }
                }

                let Some(eq_term) = self.get_eq_term(*lhs_rep, *rhs_rep) else {
                    continue;
                };
                if self.assigns.get(&eq_term) != Some(&false) {
                    continue;
                }

                let mut reasons = Vec::new();
                for &path_eq in lhs_path {
                    if !path_eq.is_sentinel() {
                        reasons.push(TheoryLit::new(path_eq, true));
                    }
                }
                for &path_eq in rhs_path {
                    if !path_eq.is_sentinel() {
                        reasons.push(TheoryLit::new(path_eq, true));
                    }
                }
                reasons.push(TheoryLit::new(eq_term, false));
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                return reasons;
            }
        }

        Vec::new()
    }

    /// Check if two terms are provably distinct WITH explanation reasons (#5086).
    ///
    /// Returns `Some(reasons)` if the disequality is known AND can be explained
    /// (safe for conflict clause generation). Returns `None` if the disequality
    /// is not known or cannot be explained (external disequalities from model
    /// evaluation that lack SAT-level reason terms).
    ///
    /// This is the safe alternative to `known_distinct()` + `explain_distinct()`
    /// for all code paths that generate conflict clauses. Using `known_distinct()`
    /// alone is unsafe because external disequalities have no reason terms.
    pub(crate) fn explain_distinct_if_provable(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if t1 == t2 {
            return None;
        }

        // O(1): distinct constants need no reasons (Z3 parity: is_unique_value).
        let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
        let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
        if t1_is_const && t2_is_const {
            return Some(Vec::new());
        }

        // O(1) tautological affine offset (i vs i+1) — no reasons needed.
        if self.distinct_by_affine_offset(t1, t2) {
            return Some(Vec::new());
        }

        if !self.known_distinct(t1, t2) {
            return None;
        }

        let reasons = self.explain_distinct(t1, t2);
        if reasons.is_empty() {
            // known_distinct returned true but explain_distinct returned empty.
            // Check if this is a reason-carrying external disequality (#6546).
            let key = Self::ordered_pair(t1, t2);
            self.external_diseq_reasons.get(&key).cloned()
        } else {
            Some(reasons)
        }
    }

    /// Direct distinctness check without transitivity. O(1) via diseq_set + constant check.
    fn known_distinct_direct(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return false;
        }

        // Check syntactic distinctness of constants
        let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
        let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
        if t1_is_const && t2_is_const {
            return true;
        }

        // O(1) lookup in disequality set
        let key = Self::ordered_pair(t1, t2);
        self.diseq_set.contains(&key)
    }

    /// Get the equality term for two terms if it exists. O(1) via pair index.
    pub(crate) fn get_eq_term(&self, t1: TermId, t2: TermId) -> Option<TermId> {
        let key = Self::ordered_pair(t1, t2);
        self.eq_pair_index.get(&key).copied()
    }

    pub(crate) fn get_exact_select_term(&self, array: TermId, index: TermId) -> Option<TermId> {
        self.select_pair_index.get(&(array, index)).copied()
    }
}
