// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Store chain navigation and resolution for the array theory solver.
//!
//! Implements store chain walking for ROW1/ROW2 reasoning:
//! - Following stores through equality chains
//! - Resolving selects through store chains
//! - Collecting effective store maps for extensionality

use super::*;

impl ArraySolver<'_> {
    /// Follow a term through equalities to find a store term.
    ///
    /// Performs BFS through the equality adjacency list up to a bounded depth,
    /// handling transitive equality chains like c = b = store(a, i, v) (#4304).
    fn find_store_through_eq(&self, term: TermId) -> Option<(TermId, TermId, TermId, Vec<TermId>)> {
        // First check if term is directly a store
        if let Some(&(base, idx, val)) = self.store_cache.get(&term) {
            return Some((base, idx, val, vec![]));
        }

        // BFS through equality adjacency list to find a store term
        const MAX_DEPTH: usize = 10;
        let mut queue: Vec<(TermId, Vec<TermId>)> = vec![(term, vec![])];
        let mut visited = std::collections::HashSet::new();
        visited.insert(term);

        while let Some((current, eq_path)) = queue.pop() {
            if eq_path.len() >= MAX_DEPTH {
                continue;
            }
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    if !visited.insert(other) {
                        continue;
                    }
                    let mut path = eq_path.clone();
                    path.push(eq_term);
                    if let Some(&(base, idx, val)) = self.store_cache.get(&other) {
                        return Some((base, idx, val, path));
                    }
                    queue.push((other, path));
                }
            }
        }
        None
    }

    /// Follow a term through equalities to find a const-array representative.
    ///
    /// Returns the const default term and equality terms used to reach it.
    fn find_const_array_through_eq(&self, term: TermId) -> Option<(TermId, Vec<TermId>)> {
        if let Some(&default) = self.const_array_cache.get(&term) {
            return Some((default, vec![]));
        }

        const MAX_DEPTH: usize = 10;
        let mut queue: Vec<(TermId, Vec<TermId>)> = vec![(term, vec![])];
        let mut visited = std::collections::HashSet::new();
        visited.insert(term);

        while let Some((current, eq_path)) = queue.pop() {
            if eq_path.len() >= MAX_DEPTH {
                continue;
            }
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    if !visited.insert(other) {
                        continue;
                    }
                    let mut path = eq_path.clone();
                    if !eq_term.is_sentinel() {
                        path.push(eq_term);
                    }
                    if let Some(&default) = self.const_array_cache.get(&other) {
                        return Some((default, path));
                    }
                    queue.push((other, path));
                }
            }
        }

        None
    }

    /// Follow store chain from `array`, skipping stores at indices known-distinct from `index`.
    /// Returns the final base array and any equality terms used.
    pub(crate) fn follow_stores_skip_distinct(
        &self,
        array: TermId,
        index: TermId,
    ) -> (TermId, Vec<TermId>, Vec<TheoryLit>) {
        let mut current = array;
        let mut eq_terms = Vec::new();
        let mut diseq_reasons = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 20;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                break;
            }

            if let Some((base, store_idx, _store_val, used_eqs)) =
                self.find_store_through_eq(current)
            {
                // Only skip stores where the disequality is provable (#5086).
                // External disequalities (from model evaluation) cannot be
                // explained and must not be assumed in conflict reasoning.
                if let Some(reasons) = self.explain_distinct_if_provable(index, store_idx) {
                    eq_terms.extend(used_eqs);
                    diseq_reasons.extend(reasons);
                    current = base;
                    continue;
                }
                // Store might affect this index, or disequality not provable
                break;
            }
            break;
        }

        (current, eq_terms, diseq_reasons)
    }

    /// Recursively simplify nested selects through stores.
    ///
    /// For select(select(select(Heap_post, 0), obj), f2):
    /// 1. Simplify select(Heap_post, 0) using ROW1 → gets middle value
    /// 2. If middle value is a store, continue simplifying
    /// 3. Eventually reaches a value or base array
    ///
    /// Returns (normalized_base_array, normalized_index, eq_terms_used, diseq_reasons)
    /// The normalized form is a (base_array, index) pair that can be compared for equality.
    /// `diseq_reasons` contains disequality explanations from store chain ROW2 skipping (#5086).
    pub(crate) fn normalize_select(
        &self,
        select_term: TermId,
    ) -> (Option<(TermId, TermId)>, Vec<TermId>, Vec<TheoryLit>) {
        let Some(&(array, index)) = self.select_cache.get(&select_term) else {
            return (None, vec![], vec![]);
        };

        // Track equality terms used
        let mut eq_terms = Vec::new();
        let mut diseq_reasons = Vec::new();

        // First, get the effective array (follow through nested selects and stores)
        let effective_array = self.get_effective_array(array, &mut eq_terms);

        // Now walk through stores at the effective array level
        let base =
            self.follow_stores_to_base(effective_array, index, &mut eq_terms, &mut diseq_reasons);

        (Some((base, index)), eq_terms, diseq_reasons)
    }

    /// Get the effective array by following nested selects.
    /// If array is select(A, i) and A=store(B, i, V), return V.
    fn get_effective_array(&self, array: TermId, eq_terms: &mut Vec<TermId>) -> TermId {
        // If array is a select term, try to simplify it
        if let Some(&(inner_array, inner_index)) = self.select_cache.get(&array) {
            // Recursively get the effective inner array
            let effective_inner = self.get_effective_array(inner_array, eq_terms);

            // Try to apply ROW1: if effective_inner is a store at inner_index
            if let Some((_base, store_idx, store_val, used_eqs)) =
                self.find_store_through_eq(effective_inner)
            {
                if self.known_equal(inner_index, store_idx) {
                    // ROW1: select(store(a, i, v), i) = v
                    eq_terms.extend(used_eqs);
                    // v might itself be a store, so return it for further processing
                    return store_val;
                }
            }

            // Can't simplify further at this level
            return array;
        }

        // Not a select, return as-is
        array
    }

    /// Follow stores via ROW2 to find the base array.
    ///
    /// Uses `explain_distinct_if_provable` to ensure only provable index
    /// disequalities are used. Collects disequality reasons alongside
    /// equality terms so callers can build complete conflict clauses (#5086).
    fn follow_stores_to_base(
        &self,
        array: TermId,
        index: TermId,
        eq_terms: &mut Vec<TermId>,
        diseq_reasons: &mut Vec<TheoryLit>,
    ) -> TermId {
        let mut current = array;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 20;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                break;
            }

            if let Some((base, store_idx, _store_val, used_eqs)) =
                self.find_store_through_eq(current)
            {
                // Only skip stores where the disequality is provable (#5086).
                if let Some(reasons) = self.explain_distinct_if_provable(index, store_idx) {
                    eq_terms.extend(used_eqs);
                    diseq_reasons.extend(reasons);
                    current = base;
                    continue;
                }
                // Can't skip - index might match or disequality not provable
                break;
            }

            // Not a store
            break;
        }

        current
    }

    /// Resolve select(array, index) through a chain of stores using ROW1+ROW2.
    ///
    /// Walks the store chain from `array`:
    /// - ROW2: if store index is known-distinct from `index`, skip to base
    /// - ROW1: if store index is known-equal to `index`, return the stored value
    ///
    /// Returns `Some((value, reasons))` if ROW1/ROW2 resolves the select to a
    /// concrete value, or `None` if the chain cannot be fully resolved.
    pub(crate) fn resolve_select_through_stores(
        &self,
        array: TermId,
        index: TermId,
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        let mut current = array;
        let mut reasons = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return None;
            }

            if let Some((base, store_idx, store_val, used_eqs)) =
                self.find_store_through_eq(current)
            {
                for eq_term in used_eqs {
                    if !eq_term.is_sentinel() {
                        reasons.push(TheoryLit::new(eq_term, true));
                    }
                }
                if self.known_equal(index, store_idx) {
                    // ROW1: select(store(a, i, v), i) = v
                    if index != store_idx {
                        if let Some(eq_term) = self.get_eq_term(index, store_idx) {
                            reasons.push(TheoryLit::new(eq_term, true));
                        }
                    }
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));
                    return Some((store_val, reasons));
                }
                if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, store_idx) {
                    // ROW2: skip to base array when the disequality is
                    // provable and explainable with SAT-level reasons.
                    reasons.extend(diseq_reasons);
                    current = base;
                    continue;
                }
                // Index relationship unknown — can't resolve further
                return None;
            }

            if let Some((default_value, const_eqs)) = self.find_const_array_through_eq(current) {
                for eq_term in const_eqs {
                    reasons.push(TheoryLit::new(eq_term, true));
                }
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                return Some((default_value, reasons));
            }

            // Not a store term — can't resolve further
            return None;
        }
    }

    /// Store chain resolution for equality propagation with explicit reasons.
    ///
    /// Like `resolve_select_through_stores`, but returns the SAT-visible
    /// equality/disequality antecedents used while walking the store chain.
    /// Unlike the older relaxed propagation path, this rejects sentinel-only
    /// (external/model-based) equalities and only skips stores when the index
    /// relationship is provable with a real explanation.
    ///
    /// Returns the resolved base array after walking through all explainable
    /// stores. If ROW1 matches (index equals store index), returns
    /// `ResolvedValue`. Otherwise returns `ResolvedBase` with the ultimate base
    /// array that couldn't be resolved further.
    pub(crate) fn resolve_select_base_for_propagation_with_reasons(
        &self,
        array: TermId,
        index: TermId,
    ) -> (SelectResolution, Vec<TheoryLit>) {
        let mut current = array;
        let mut reasons = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return (SelectResolution::Unresolved, reasons);
            }

            if let Some((base, store_idx, store_val, used_eqs)) =
                self.find_store_through_eq(current)
            {
                for eq_term in used_eqs {
                    reasons.push(TheoryLit::new(eq_term, true));
                }
                if self.known_equal(index, store_idx) {
                    // ROW1: select(store(a, i, v), i) = v
                    if let Some(eq_reasons) = self.explain_equal_if_provable(index, store_idx) {
                        reasons.extend(eq_reasons);
                    } else {
                        return (SelectResolution::Unresolved, reasons);
                    }
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));
                    return (SelectResolution::Value(store_val), reasons);
                }
                if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, store_idx) {
                    // ROW2: skip to base only when the disequality is
                    // provable with SAT-visible reasons. Sentinel-only
                    // model equalities/disequalities must not reach
                    // equality propagation (#5179, #6608).
                    reasons.extend(diseq_reasons);
                    current = base;
                    continue;
                }
                // Index relationship unknown — can't resolve further
                return (SelectResolution::Unresolved, reasons);
            }

            if let Some((default_value, const_eqs)) = self.find_const_array_through_eq(current) {
                for eq_term in const_eqs {
                    reasons.push(TheoryLit::new(eq_term, true));
                }
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                return (SelectResolution::Value(default_value), reasons);
            }

            // Reached a base array that is not a store — return it.
            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            return (SelectResolution::Base(current), reasons);
        }
    }

    /// Collect the effective store map of a store chain (#5086).
    ///
    /// Walks a store chain top-down (outermost store first) and collects
    /// (index, value) pairs. Later stores (closer to the base) at the same
    /// index are shadowed by earlier ones (closer to the top).
    ///
    /// Returns `Some((base_array, effective_map))` where `effective_map`
    /// contains the first (index, value) pair seen for each equivalence class
    /// of index terms. Returns `None` if the chain is too long or not a
    /// pure store chain.
    pub(crate) fn collect_effective_stores(
        &self,
        array: TermId,
    ) -> Option<(TermId, Vec<(TermId, TermId)>)> {
        let mut current = array;
        let mut effective: Vec<(TermId, TermId)> = Vec::new();
        let mut seen_indices: Vec<TermId> = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return None;
            }

            if let Some(&(base, store_idx, store_val)) = self.store_cache.get(&current) {
                // #7654: An inner store is only "effective" if its index is
                // PROVABLY DISTINCT from all outer store indices. If we merely
                // check `known_equal` (the old code), an inner store at index
                // `i` is included even when an outer store at index `j` might
                // equal `i` — the model can set i=j, making the outer store
                // overwrite the inner one. The effective map then claims the
                // inner value is visible, leading to false equality propagation
                // (e.g., store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
                // falsely derives v=w).
                //
                // Fix: skip the inner store unless ALL outer indices are
                // provably distinct from it.
                let possibly_covered = seen_indices
                    .iter()
                    .any(|&si| si == store_idx || !self.known_distinct(si, store_idx));
                if !possibly_covered {
                    effective.push((store_idx, store_val));
                    seen_indices.push(store_idx);
                }
                current = base;
                continue;
            }

            // Also follow equalities to find store terms
            if let Some((base, store_idx, store_val, _used_eqs)) =
                self.find_store_through_eq(current)
            {
                // #7654: Same fix as above — require provable distinctness.
                let possibly_covered = seen_indices
                    .iter()
                    .any(|&si| si == store_idx || !self.known_distinct(si, store_idx));
                if !possibly_covered {
                    effective.push((store_idx, store_val));
                    seen_indices.push(store_idx);
                }
                current = base;
                continue;
            }

            // Reached a non-store base — return it with the collected map
            return Some((current, effective));
        }
    }

    /// Check if two effective store maps are identical up to equivalence classes.
    ///
    /// Two maps match if for every (index, value) in one map, there exists a
    /// corresponding (index', value') in the other where index ≡ index' and
    /// value ≡ value'. Both maps must have the same number of entries.
    pub(crate) fn effective_stores_match_with_reasons(
        &self,
        map1: &[(TermId, TermId)],
        map2: &[(TermId, TermId)],
    ) -> Option<Vec<TheoryLit>> {
        if map1.len() != map2.len() {
            return None;
        }

        // #6546: Greedy O(N^2) matcher replaces O(N!) backtracking matcher.
        let mut used = vec![false; map2.len()];
        let mut all_reasons = Vec::new();

        for &(idx1, val1) in map1 {
            let mut matched = false;
            for (candidate, &(idx2, val2)) in map2.iter().enumerate() {
                if used[candidate] {
                    continue;
                }

                let Some(idx_reasons) = self.explain_equal_if_provable(idx1, idx2) else {
                    continue;
                };
                let Some(val_reasons) = self.explain_equal_if_provable(val1, val2) else {
                    continue;
                };

                used[candidate] = true;
                all_reasons.extend(idx_reasons);
                all_reasons.extend(val_reasons);
                matched = true;
                break;
            }
            if !matched {
                return None;
            }
        }

        all_reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        all_reasons.dedup_by_key(|lit| (lit.term, lit.value));
        Some(all_reasons)
    }

    pub(crate) fn conflict_reasons_to_lemma(mut reasons: Vec<TheoryLit>) -> Option<TheoryResult> {
        if reasons.is_empty() {
            return None;
        }

        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));

        let mut clause: Vec<TheoryLit> = reasons
            .into_iter()
            .map(|lit| TheoryLit::new(lit.term, !lit.value))
            .collect();
        clause.sort_by_key(|lit| (lit.term.0, lit.value));
        clause.dedup_by_key(|lit| (lit.term, lit.value));

        if clause.is_empty() {
            return None;
        }

        Some(TheoryResult::NeedLemmas(vec![TheoryLemma::new(clause)]))
    }
}
