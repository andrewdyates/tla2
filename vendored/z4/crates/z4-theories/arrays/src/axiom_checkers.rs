// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ROW1 and ROW2 axiom conflict checkers for the array theory solver.
//!
//! Implements detection of array axiom violations:
//! - ROW1 (read-over-write same index)
//! - ROW2 (read-over-write different index) — downward, upward, extended
//!
//! Store chain resolution, const-array reads, self-store, array equality,
//! and extensionality checks are in `axiom_store_checks`.

use super::*;

impl ArraySolver<'_> {
    /// Check read-over-write axiom 1 (same index):
    /// If we have select(store(a, i, v), i), it must equal v.
    /// Returns conflict if select(store(a, i, v), i) ≠ v is asserted.
    ///
    /// Event-driven (#6546 revised design): instead of scanning ALL selects
    /// and doing BFS per select (O(S × D) per check), drains only
    /// `pending_row1` pairs queued by `register_select`, `register_store`,
    /// and `notify_equality`. Most `check()` calls have 0-1 new pairs.
    ///
    /// Drain semantics: pairs where indices match but no conflict is detected
    /// yet are RETAINED for future re-checking (the disequality on values
    /// may be propagated later). Pairs with non-matching indices are
    /// discarded (handled by ROW2).
    pub(crate) fn check_row1(&mut self) -> Option<TheoryResult> {
        let mut pairs = std::mem::take(&mut self.pending_row1);
        // Sort/dedup for deterministic conflict detection and bounded replay.
        pairs.sort_unstable_by_key(|&(sel, st)| (sel.0, st.0));
        pairs.dedup();

        let mut retained = Vec::new();
        let mut iter = pairs.into_iter();
        while let Some((select_term, store_term)) = iter.next() {
            // Validate that both terms are still in caches (backtrack may
            // have removed them via a dirty rebuild).
            let Some(&(select_array, select_idx)) = self.select_cache.get(&select_term) else {
                continue;
            };
            let Some(&(_base, store_idx, store_val)) = self.store_cache.get(&store_term) else {
                continue;
            };

            // ROW1: select(store(a, i, v), j) where i = j → result = v.
            if !self.known_equal(select_idx, store_idx) {
                // Indices not equal — not a ROW1 candidate. Discard.
                // (ROW2 handles the i ≠ j case separately.)
                continue;
            }

            // Check if select_term ≠ store_val is provably asserted (conflict).
            let Some(val_diseq_reasons) = self.explain_distinct_if_provable(select_term, store_val)
            else {
                // Indices match but no conflict yet — RETAIN for re-checking.
                // The disequality may be propagated on a future check() call.
                retained.push((select_term, store_term));
                continue;
            };

            // Conflict! select(store(a, i, v), i) ≠ v contradicts ROW1.
            let mut reasons = val_diseq_reasons;

            // Justify select_array = store_term via equality path.
            if select_array != store_term {
                if let Some(eq_path) = self.find_eq_path(select_array, store_term) {
                    for eq_term in eq_path {
                        reasons.push(TheoryLit::new(eq_term, true));
                    }
                }
            }

            // Add the equality i = store_idx if it's not syntactic.
            if select_idx != store_idx {
                if let Some(eq_term) = self.get_eq_term(select_idx, store_idx) {
                    reasons.push(TheoryLit::new(eq_term, true));
                }
            }

            // Preserve the unprocessed tail before returning so one emitted
            // lemma does not silently drop later queued ROW1 work.
            retained.extend(iter);
            self.pending_row1 = retained;
            return Self::conflict_reasons_to_lemma(reasons);
        }

        self.pending_row1 = retained;
        None
    }

    /// Find equality path from `from` to `to` through `eq_adj`.
    /// Returns the sequence of equality terms justifying `from = to`.
    fn find_eq_path(&self, from: TermId, to: TermId) -> Option<Vec<TermId>> {
        if from == to {
            return Some(vec![]);
        }
        // Check direct equality first (O(1)).
        if let Some(&eq_term) = self.eq_pair_index.get(&Self::ordered_pair(from, to)) {
            if self.assigns.get(&eq_term) == Some(&true) {
                return Some(vec![eq_term]);
            }
        }
        // BFS through eq_adj with known target.
        let mut queue: std::collections::VecDeque<(TermId, Vec<TermId>)> =
            std::collections::VecDeque::new();
        queue.push_back((from, vec![]));
        let mut visited = std::collections::HashSet::new();
        visited.insert(from);
        while let Some((current, path)) = queue.pop_front() {
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    if !visited.insert(other) {
                        continue;
                    }
                    let mut new_path = path.clone();
                    new_path.push(eq_term);
                    if other == to {
                        return Some(new_path);
                    }
                    if new_path.len() < 10 {
                        queue.push_back((other, new_path));
                    }
                }
            }
        }
        None
    }

    pub(crate) fn row2_down_clause_terms(
        &self,
        store_term: TermId,
        select_term: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let &(array, select_idx) = self.select_cache.get(&select_term)?;
        if array != store_term {
            return None;
        }

        let &(base_array, store_idx, _) = self.store_cache.get(&store_term)?;
        let base_select = self.get_exact_select_term(base_array, select_idx)?;
        if base_select == select_term {
            return None;
        }
        Some((store_idx, select_idx, base_select))
    }

    /// Check read-over-write axiom 2 (different index):
    /// If i ≠ j, then select(store(a, i, v), j) = select(a, j).
    ///
    /// The array solver cannot create fresh equality terms directly, so this
    /// pass has two stages:
    /// 1. if both equality atoms already exist, emit the permanent ROW2 clause
    /// 2. otherwise, request the missing equality atoms via NeedModelEqualities
    ///
    /// Applied ROW2 clauses are remembered so later check() calls do not
    /// regenerate them after split-loop rebuilds (#6546 Packet 3).
    pub(crate) fn check_row2(&mut self) -> Option<TheoryResult> {
        let mut lemmas = Vec::new();
        let mut seen_lemmas = HashSet::new();
        let mut requests = Vec::new();
        let mut seen_requests = HashSet::new();

        // (#6820) Move blocked axioms back to pending only when new terms have
        // been created.
        if self.populated_terms > self.blocked_axiom_term_gen {
            self.pending_axioms.append(&mut self.blocked_axioms);
            self.blocked_axiom_term_gen = self.populated_terms;
        }

        // Drain completed axioms: swap out pending_axioms, process them, and
        // put back only those that still need work.
        let axioms = std::mem::take(&mut self.pending_axioms);
        let mut remaining = Vec::with_capacity(axioms.len());

        for axiom in axioms {
            match axiom {
                PendingAxiom::Row2Down { store, select } => {
                    let Some((store_idx, select_idx, base_select)) =
                        self.row2_down_clause_terms(store, select)
                    else {
                        // Terms not in cache yet — keep for later.
                        remaining.push(PendingAxiom::Row2Down { store, select });
                        continue;
                    };

                    let idx_eq = self.get_eq_term(store_idx, select_idx);
                    let select_eq = self.get_eq_term(select, base_select);
                    if let (Some(idx_eq), Some(select_eq)) = (idx_eq, select_eq) {
                        // If either disjunct is already true under the current
                        // assignment the clause is satisfied — skip emission.
                        let idx_sat = self.assigns.get(&idx_eq) == Some(&true);
                        let sel_sat = self.assigns.get(&select_eq) == Some(&true);
                        if idx_sat || sel_sat {
                            remaining.push(PendingAxiom::Row2Down { store, select });
                            continue;
                        }

                        // Both atoms exist — build and emit the clause, then
                        // drain this axiom (don't push to remaining).
                        let mut clause = vec![
                            TheoryLit::new(idx_eq, true),
                            TheoryLit::new(select_eq, true),
                        ];
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        if !clause.is_empty() && seen_lemmas.insert(clause.clone()) {
                            lemmas.push(TheoryLemma::new(clause));
                        }
                        // Axiom completed — drained (not pushed to remaining).
                        continue;
                    }

                    // At least one equality atom missing — request it and move
                    // to blocked_axioms.
                    for (lhs, rhs) in [(store_idx, select_idx), (select, base_select)] {
                        if self.get_eq_term(lhs, rhs).is_some() {
                            continue;
                        }
                        let request_key = Self::ordered_pair(lhs, rhs);
                        if seen_requests.insert(request_key)
                            && self.requested_model_eqs.insert(request_key)
                        {
                            requests.push(ModelEqualityRequest {
                                lhs,
                                rhs,
                                reason: Vec::new(),
                            });
                        }
                    }
                    self.blocked_axioms
                        .push(PendingAxiom::Row2Down { store, select });
                }
            }
        }

        self.pending_axioms = remaining;

        if !lemmas.is_empty() {
            return Some(TheoryResult::NeedLemmas(lemmas));
        }
        match requests.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                requests.pop().expect("invariant: len checked above"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(requests)),
        }
    }

    /// Axiom 2b: Upward ROW2 conflict detection through store chains.
    ///
    /// Standard ROW2 (check_row2) checks *downward*: given select(store(A,i,v), j),
    /// it derives select(store(A,i,v), j) = select(A, j) when i != j.
    ///
    /// Upward ROW2 checks the reverse direction: given select(A, j) where A is
    /// the *base* array of some store(A, i, v) = B, it derives:
    ///   i != j → select(A, j) = select(B, j)
    ///
    /// Reference: Z3 `instantiate_axiom2b`, `set_prop_upward`, `add_parent_store`.
    #[cfg(test)]
    pub(crate) fn check_row2_upward(&self) -> Option<TheoryResult> {
        let mut selects: Vec<_> = self.select_cache.iter().collect();
        selects.sort_by_key(|(&term, _)| term.0);

        for (&select_on_base, &(base_array, select_idx)) in &selects {
            let Some(data) = self.array_vars.get(&base_array) else {
                continue;
            };
            if !data.prop_upward || data.parent_stores.is_empty() {
                continue;
            }

            for &store_term in &data.parent_stores {
                let Some(&(_, store_idx, _)) = self.store_cache.get(&store_term) else {
                    continue;
                };
                let Some(idx_diseq_reasons) =
                    self.explain_distinct_if_provable(select_idx, store_idx)
                else {
                    continue;
                };

                if let Some(select_on_store) = self.get_exact_select_term(store_term, select_idx) {
                    if let Some(val_diseq_reasons) =
                        self.explain_distinct_if_provable(select_on_base, select_on_store)
                    {
                        let mut reasons = idx_diseq_reasons;
                        reasons.extend(val_diseq_reasons);
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));

                        if reasons.is_empty() {
                            return None;
                        }
                        return Some(TheoryResult::Unsat(reasons));
                    }
                }
            }
        }

        None
    }

    /// Check ROW2 upward and emit `NeedModelEquality` for undecided index pairs.
    pub(crate) fn check_row2_upward_with_guidance(&mut self) -> Option<TheoryResult> {
        let pairs = std::mem::take(&mut self.pending_row2_upward);
        let mut pending_requests = Vec::new();

        for (select_on_base, store_term) in pairs {
            let Some(&(_, select_idx)) = self.select_cache.get(&select_on_base) else {
                continue;
            };
            let Some(&(_, store_idx, _)) = self.store_cache.get(&store_term) else {
                continue;
            };
            if select_idx == store_idx {
                continue;
            }

            if self.known_equal(select_idx, store_idx) {
                continue; // ROW1 handles this
            }

            if let Some(idx_diseq_reasons) =
                self.explain_distinct_if_provable(select_idx, store_idx)
            {
                if let Some(select_on_store) = self.get_exact_select_term(store_term, select_idx) {
                    if let Some(val_diseq_reasons) =
                        self.explain_distinct_if_provable(select_on_base, select_on_store)
                    {
                        #[allow(clippy::redundant_clone)]
                        let mut reasons = idx_diseq_reasons.clone();
                        reasons.extend(val_diseq_reasons);
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));
                        if reasons.is_empty() {
                            return None;
                        }
                        return Self::conflict_reasons_to_lemma(reasons);
                    }
                }
            } else {
                let key = if store_idx.0 <= select_idx.0 {
                    (store_idx, select_idx)
                } else {
                    (select_idx, store_idx)
                };
                if !self.requested_model_eqs.insert(key) {
                    continue;
                }
                pending_requests.push(ModelEqualityRequest {
                    lhs: store_idx,
                    rhs: select_idx,
                    reason: Vec::new(),
                });
            }
        }

        match pending_requests.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                pending_requests
                    .pop()
                    .expect("invariant: len checked above"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(pending_requests)),
        }
    }

    /// Check ROW2 conflicts via store chain following.
    pub(crate) fn check_row2_extended(&self) -> Option<TheoryResult> {
        struct Row2ExtendedSelectState {
            select_term: TermId,
            index: TermId,
            base: TermId,
            eq_terms: Vec<TermId>,
            diseq_reasons: Vec<TheoryLit>,
        }

        let candidate_pairs = self.select_conflict_candidate_pairs();

        let mut needed: HashSet<TermId> = HashSet::with_capacity(candidate_pairs.len() * 2);
        for &(s1, s2) in &candidate_pairs {
            needed.insert(s1);
            needed.insert(s2);
        }
        let select_terms: HashMap<_, _> = needed
            .iter()
            .filter_map(|&select_term| {
                let &(array, index) = self.select_cache.get(&select_term)?;
                let (base, eq_terms, diseq_reasons) =
                    self.follow_stores_skip_distinct(array, index);
                Some((
                    select_term,
                    Row2ExtendedSelectState {
                        select_term,
                        index,
                        base,
                        eq_terms,
                        diseq_reasons,
                    },
                ))
            })
            .collect();

        for (sel1_term, sel2_term) in candidate_pairs {
            let Some(sel1) = select_terms.get(&sel1_term) else {
                continue;
            };
            let Some(sel2) = select_terms.get(&sel2_term) else {
                continue;
            };

            if !self.known_equal(sel1.index, sel2.index) {
                continue;
            }

            let Some(sel_diseq_reasons) =
                self.explain_distinct_if_provable(sel1.select_term, sel2.select_term)
            else {
                continue;
            };

            if sel1.base == sel2.base {
                let mut reasons = sel_diseq_reasons;

                reasons.extend(sel1.diseq_reasons.iter().copied());
                reasons.extend(sel2.diseq_reasons.iter().copied());

                for &eq_term in &sel1.eq_terms {
                    reasons.push(TheoryLit::new(eq_term, true));
                }
                for &eq_term in &sel2.eq_terms {
                    reasons.push(TheoryLit::new(eq_term, true));
                }

                if sel1.index != sel2.index {
                    if let Some(eq_term) = self.get_eq_term(sel1.index, sel2.index) {
                        reasons.push(TheoryLit::new(eq_term, true));
                    } else {
                        let paths = self.equality_paths_from(sel1.index);
                        if let Some(path) = paths.get(&sel2.index) {
                            for &eq in path {
                                if !eq.is_sentinel() {
                                    reasons.push(TheoryLit::new(eq, true));
                                }
                            }
                        }
                    }
                }

                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));

                if reasons.is_empty() {
                    return None;
                }
                return Self::conflict_reasons_to_lemma(reasons);
            }
        }
        None
    }
}
