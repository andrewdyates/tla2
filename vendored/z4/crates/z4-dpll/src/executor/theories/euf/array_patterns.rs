// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array extensionality and store-base decomposition axiom generation.
//!
//! Congruence axioms are in `array_congruence`. ROW/ROW2b axioms are in `array_row`.

use super::super::super::Executor;
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{Sort, TermData, TermId};

impl Executor {
    #[inline]
    fn ordered_term_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    /// Collect direct top-level disequalities asserted as `(assert (not (= a b)))`.
    pub(super) fn collect_top_level_disequalities(&self) -> HashSet<(TermId, TermId)> {
        let mut disequalities = HashSet::new();
        for &assertion in &self.ctx.assertions {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                disequalities.insert(Self::ordered_term_pair(args[0], args[1]));
            }
        }
        disequalities
    }

    fn are_terms_distinct_constants(&self, lhs: TermId, rhs: TermId) -> bool {
        if lhs == rhs || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return false;
        }
        match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
            (TermData::Const(lhs_const), TermData::Const(rhs_const)) => lhs_const != rhs_const,
            _ => false,
        }
    }

    pub(super) fn are_terms_provably_distinct_from_assertions(
        &self,
        lhs: TermId,
        rhs: TermId,
        disequalities: &HashSet<(TermId, TermId)>,
    ) -> bool {
        lhs != rhs
            && (self.are_terms_distinct_constants(lhs, rhs)
                || disequalities.contains(&Self::ordered_term_pair(lhs, rhs)))
    }

    fn has_explicit_select_disequality_witness(
        &self,
        lhs: TermId,
        rhs: TermId,
        selects_by_array: &HashMap<TermId, HashMap<TermId, TermId>>,
        disequalities: &HashSet<(TermId, TermId)>,
    ) -> bool {
        let Some(lhs_selects) = selects_by_array.get(&lhs) else {
            return false;
        };
        let Some(rhs_selects) = selects_by_array.get(&rhs) else {
            return false;
        };
        let (smaller, larger) = if lhs_selects.len() <= rhs_selects.len() {
            (lhs_selects, rhs_selects)
        } else {
            (rhs_selects, lhs_selects)
        };
        smaller.iter().any(|(&index, &lhs_select)| {
            larger.get(&index).is_some_and(|&rhs_select| {
                self.are_terms_provably_distinct_from_assertions(
                    lhs_select,
                    rhs_select,
                    disequalities,
                )
            })
        })
    }

    /// Ensure negation terms exist for array equalities appearing inside ITE
    /// conditions. This is necessary for the ABV path where `(ite (= a b) t e)`
    /// contains an array equality `(= a b)` that is never negated elsewhere.
    /// Without the negation in the term store, `add_array_extensionality_axioms`
    /// skips the pair, leaving the array equality unconstrained. The ITE then
    /// becomes a coin flip, causing wrong-SAT or spurious unknown results.
    ///
    /// This function walks the term store for ITE terms whose condition is an
    /// array equality, and creates `(not (= a b))` in the term store. Creating
    /// the negation is semantically harmless (it's just a term, not an assertion)
    /// but enables the extensionality axiom generator to fire.
    pub(in crate::executor) fn ensure_array_eq_ite_negations(&mut self) {
        let mut array_eq_terms: Vec<TermId> = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            let TermData::Ite(cond, _, _) = self.ctx.terms.get(term_id) else {
                continue;
            };
            let cond = *cond;
            // Check if the condition is an array equality
            let TermData::App(sym, args) = self.ctx.terms.get(cond) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            if !matches!(self.ctx.terms.sort(args[0]), Sort::Array(_)) {
                continue;
            }
            array_eq_terms.push(cond);
        }
        // Create negation terms (idempotent via hash-consing in mk_not)
        for eq_term in array_eq_terms {
            let _ = self.ctx.terms.mk_not(eq_term);
        }
    }

    /// Add eager extensionality axioms for array equality atoms.
    ///
    /// For every equality atom `(= a b)` in the term store where a, b have
    /// `Sort::Array(...)`, creates:
    ///   - A fresh Skolem variable `__ext_diff_N` with the array's index sort
    ///   - Select terms `(select a __ext_diff_N)` and `(select b __ext_diff_N)`
    ///   - The extensionality clause: `(= a b) ∨ ¬(= (select a k) (select b k))`
    ///
    /// This is a valid tautology in the theory of arrays. Adding it before
    /// Tseitin encoding ensures the SAT solver has the atoms needed to enforce
    /// the extensionality axiom: if `a ≠ b`, the diff witness must differ.
    pub(in crate::executor) fn add_array_extensionality_axioms(&mut self) {
        let top_level_disequalities = self.collect_top_level_disequalities();

        // Collect array equality atoms and their negations from the term store.
        // Optimization: only generate extensionality axioms for pairs where
        // ¬(= a b) exists in the term store. If the negation never appears,
        // the solver cannot assert a ≠ b, so extensionality is vacuously
        // satisfied and the Skolem witness is unnecessary. Skipping avoids
        // introducing free variables that cause LIA oscillation (#4304).
        let mut negated_terms: HashSet<TermId> = HashSet::new();
        let mut array_eq_pairs: Vec<(TermId, TermId, TermId, Sort)> = Vec::new();
        let mut selects_by_array: HashMap<TermId, HashMap<TermId, TermId>> = HashMap::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            match self.ctx.terms.get(term_id).clone() {
                TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];
                    if lhs == rhs {
                        continue;
                    }
                    if let Sort::Array(ref arr_sort) = self.ctx.terms.sort(lhs).clone() {
                        array_eq_pairs.push((term_id, lhs, rhs, arr_sort.index_sort.clone()));
                    }
                }
                TermData::App(ref sym, ref args) if sym.name() == "select" && args.len() == 2 => {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .entry(args[1])
                        .or_insert(term_id);
                }
                TermData::Not(inner) => {
                    negated_terms.insert(inner);
                }
                _ => {}
            }
        }

        // For each unique array pair with a negation, create extensionality axiom
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::new();
        for (eq_term, lhs, rhs, index_sort) in array_eq_pairs {
            if !negated_terms.contains(&eq_term) {
                continue;
            }
            let pair = if lhs.0 <= rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            if !seen_pairs.insert(pair) {
                continue; // Already added axiom for this pair
            }

            // Port of Z3's `already_diseq`: when an explicit top-level witness
            // `not (= (select lhs k) (select rhs k))` already exists, do not
            // create a redundant fresh extensionality Skolem for the same pair.
            if self.has_explicit_select_disequality_witness(
                lhs,
                rhs,
                &selects_by_array,
                &top_level_disequalities,
            ) {
                continue;
            }

            // Create fresh Skolem diff variable with the array's index sort
            let skolem_name = format!("__ext_diff_{}_{}", lhs.0, rhs.0);
            let diff_var = self.ctx.terms.mk_var(skolem_name, index_sort);

            // Create select(a, diff) and select(b, diff)
            let sel_a = self.ctx.terms.mk_select(lhs, diff_var);
            let sel_b = self.ctx.terms.mk_select(rhs, diff_var);

            // Create (= (select a diff) (select b diff))
            let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);

            // Create ¬(= (select a diff) (select b diff))
            let not_sel_eq = self.ctx.terms.mk_not(sel_eq);

            // Create extensionality clause: (= a b) ∨ ¬(= (select a diff) (select b diff))
            let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);

            // Add as an assertion (it's a tautology, so it preserves equivalence)
            self.push_array_axiom_assertion(ext_clause);
        }
    }

    /// Store base decomposition axioms (#6282).
    ///
    /// For every pair of array-sorted terms X, Y where X = store(A, i, v1)
    /// and Y = store(B, j, v2) (either directly or via asserted equalities),
    /// adds axioms that decompose a potential X = Y into base equality:
    ///
    ///   `¬(= X Y) ∨ (= i diff_AB) ∨ (= j diff_AB) ∨ (= A B)`
    ///   `(= A B) ∨ ¬(= select(A, diff_AB) select(B, diff_AB))`
    ///
    /// This covers both direct store-store equalities and the transitive case
    /// where X and Y are variables equal to stores (e.g., `v6 = store(v4, i4, ...)`
    /// and `v7 = store(v5, i4, ...)`). When X = Y is asserted or derived during
    /// search, the decomposition axiom forces A = B or the diff is at a stored index.
    ///
    /// This enables the storeinv proof chain: from top-level store equality,
    /// propagate down through nested store layers to reach `a1 = a2`, which
    /// contradicts the Skolem witness of difference.
    pub(in crate::executor) fn add_store_store_base_decomposition_axioms(&mut self) {
        // Phase 1: collect every (variable/term, store_base, store_index) triple
        // from equalities `(= X store(A, i, v))` in the term store.
        // Also collect direct store-store equalities.
        struct StoreInfo {
            /// The "named" side (X in X = store(A,i,v), or the store term itself)
            named: TermId,
            base: TermId,
            idx: TermId,
        }

        // Map from store index (as a TermId) to all StoreInfos with that index.
        // We group by store index because base decomposition only links stores
        // at the same index (or includes both index disjuncts).
        let mut store_infos: Vec<StoreInfo> = Vec::new();

        // Also track existing store-store equalities for direct decomposition.
        struct DirectStoreStoreEq {
            eq_term: TermId,
            base_a: TermId,
            idx_a: TermId,
            base_b: TermId,
            idx_b: TermId,
        }
        let mut direct_eqs: Vec<DirectStoreStoreEq> = Vec::new();

        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term_id).clone() {
                if sym.name() == "=" && args.len() == 2 {
                    let lhs = args[0];
                    let rhs = args[1];
                    if lhs == rhs {
                        continue;
                    }
                    let lhs_store = match self.ctx.terms.get(lhs).clone() {
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3 => {
                            Some((a[0], a[1]))
                        }
                        _ => None,
                    };
                    let rhs_store = match self.ctx.terms.get(rhs).clone() {
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3 => {
                            Some((a[0], a[1]))
                        }
                        _ => None,
                    };

                    match (lhs_store, rhs_store) {
                        (Some((base_a, idx_a)), Some((base_b, idx_b))) => {
                            if base_a != base_b {
                                direct_eqs.push(DirectStoreStoreEq {
                                    eq_term: term_id,
                                    base_a,
                                    idx_a,
                                    base_b,
                                    idx_b,
                                });
                            }
                            // Both sides are stores — record both with their
                            // "named" side as the store term itself.
                            store_infos.push(StoreInfo {
                                named: lhs,
                                base: base_a,
                                idx: idx_a,
                            });
                            store_infos.push(StoreInfo {
                                named: rhs,
                                base: base_b,
                                idx: idx_b,
                            });
                        }
                        (Some((base, store_idx)), None) => {
                            // (= store(A,i,v) X) — record X as named
                            store_infos.push(StoreInfo {
                                named: rhs,
                                base,
                                idx: store_idx,
                            });
                        }
                        (None, Some((base, store_idx))) => {
                            // (= X store(A,i,v)) — record X as named
                            store_infos.push(StoreInfo {
                                named: lhs,
                                base,
                                idx: store_idx,
                            });
                        }
                        (None, None) => {}
                    }
                }
            }
        }

        // Phase 2: for each pair of StoreInfos with the same store index,
        // where the named sides are different, create a conditional base
        // decomposition axiom:
        //   ¬(= named_X named_Y) ∨ (= idx diff_AB) ∨ (= A B)
        //
        // This fires when X = Y becomes true (asserted or propagated).
        let mut seen_base_pairs: HashSet<(TermId, TermId)> = HashSet::new();

        // Helper: creates extensionality + decomposition for a base pair.
        // Returns true if new axioms were added.
        let terms = &mut self.ctx.terms;
        let assertions = &mut self.ctx.assertions;

        let mut add_decomp = |named_x: TermId,
                              named_y: TermId,
                              idx_a: TermId,
                              idx_b: TermId,
                              base_a: TermId,
                              base_b: TermId,
                              eq_term: Option<TermId>,
                              seen: &mut HashSet<(TermId, TermId)>| {
            // Mixed array sorts can share the same store index term in one
            // formula (for example Array Int Bool and Array Int Int on the same
            // symbolic index). Store decomposition only applies to same-sorted
            // array pairs; otherwise mk_eq/select would fabricate cross-sort
            // terms and panic (#1753 / zani mixed-array benchmark).
            if terms.sort(base_a) != terms.sort(base_b) || terms.sort(idx_a) != terms.sort(idx_b) {
                return;
            }
            if eq_term.is_none() && terms.sort(named_x) != terms.sort(named_y) {
                return;
            }

            let base_pair = if base_a.0 <= base_b.0 {
                (base_a, base_b)
            } else {
                (base_b, base_a)
            };

            // Create or get the (= named_x named_y) equality term.
            let xy_eq = eq_term.unwrap_or_else(|| terms.mk_eq(named_x, named_y));
            let not_xy_eq = terms.mk_not(xy_eq);

            // Create extensionality Skolem for the base pair (once per pair).
            if let Sort::Array(ref arr_sort) = terms.sort(base_a).clone() {
                let index_sort = arr_sort.index_sort.clone();
                // Reuse the canonical extensionality witness name for the same
                // base-array pair instead of introducing a parallel store-base
                // decomposition witness. This keeps the array proof search on a
                // single distinguishing index for `(base_a, base_b)` (#6282).
                let skolem_name = format!("__ext_diff_{}_{}", base_pair.0 .0, base_pair.1 .0);
                let diff_var = terms.mk_var(skolem_name, index_sort);
                let base_eq = terms.mk_eq(base_a, base_b);

                if seen.insert(base_pair) {
                    // First time: add extensionality axiom for (A, B).
                    let sel_a = terms.mk_select(base_a, diff_var);
                    let sel_b = terms.mk_select(base_b, diff_var);
                    let sel_eq = terms.mk_eq(sel_a, sel_b);
                    let not_sel_eq = terms.mk_not(sel_eq);
                    let ext_axiom = terms.mk_or(vec![base_eq, not_sel_eq]);
                    assertions.push(ext_axiom);
                }

                // Decomposition: ¬(= X Y) ∨ (= idx_a diff) ∨ [opt: (= idx_b diff)] ∨ (= A B)
                let mut decomp_lits = vec![not_xy_eq];
                let idx_a_eq_diff = terms.mk_eq(idx_a, diff_var);
                decomp_lits.push(idx_a_eq_diff);
                if idx_a != idx_b {
                    let idx_b_eq_diff = terms.mk_eq(idx_b, diff_var);
                    decomp_lits.push(idx_b_eq_diff);
                }
                decomp_lits.push(base_eq);
                let decomp_axiom = terms.mk_or(decomp_lits);
                assertions.push(decomp_axiom);
            }
        };

        // Phase 2a: handle direct store-store equalities.
        for dse in &direct_eqs {
            add_decomp(
                dse.eq_term, // not used as named, but we pass eq_term directly
                dse.eq_term, // dummy
                dse.idx_a,
                dse.idx_b,
                dse.base_a,
                dse.base_b,
                Some(dse.eq_term),
                &mut seen_base_pairs,
            );
        }

        // Phase 2b: handle transitive pairs — variables equal to stores at the
        // same index. For each pair (si, sj) where si.idx == sj.idx and
        // si.named != sj.named, add decomposition.
        // Group by index for efficiency.
        let mut by_index: HashMap<TermId, Vec<usize>> = HashMap::new();
        for (i, si) in store_infos.iter().enumerate() {
            by_index.entry(si.idx).or_default().push(i);
        }
        for (_idx, group) in &by_index {
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    let si = &store_infos[group[i]];
                    let sj = &store_infos[group[j]];
                    // Skip if same named side or same base
                    if si.named == sj.named || si.base == sj.base {
                        continue;
                    }
                    add_decomp(
                        si.named,
                        sj.named,
                        si.idx,
                        sj.idx,
                        si.base,
                        sj.base,
                        None,
                        &mut seen_base_pairs,
                    );
                }
            }
        }
    }
}
