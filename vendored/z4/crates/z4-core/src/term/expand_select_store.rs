// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expand `select(store(...))` into ITE chains at preprocessing time.
//!
//! Z3 ref: `array_rewriter.cpp:354-381` (`expand_select_store`).
//!
//! Converts `select(store(a, I, v), J)` → `ite(I = J, v, select(a, J))`,
//! eliminating store chains at preprocessing time. Critical for storeinv-family
//! benchmarks where deep swap chains cause the lazy array theory to cycle
//! through exponentially many models.

use super::*;
use std::collections::HashMap;

impl TermStore {
    /// Expand `select(store(a, I, v), J)` into `ite(I = J, v, select(a, J))`.
    ///
    /// The expansion chains recursively: if `a` is itself `store(a', I', v')`,
    /// the new `select(a', J)` term is also expanded. Bounded at 50 levels
    /// to prevent runaway expansion on pathological inputs.
    pub fn expand_select_store(&mut self, term: TermId) -> TermId {
        self.expand_select_store_inner(term, &mut HashMap::new())
    }

    fn expand_select_store_inner(
        &mut self,
        term: TermId,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::App(Symbol::Named(ref name), ref args)
                if name == "select" && args.len() == 2 =>
            {
                let array = args[0];
                let index = args[1];

                // Recursively expand children first
                let expanded_array = self.expand_select_store_inner(array, cache);
                let expanded_index = self.expand_select_store_inner(index, cache);

                // Now try to expand select-over-store on the result
                self.expand_select_over_store(expanded_array, expanded_index, 50)
            }
            TermData::App(ref sym, ref args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.expand_select_store_inner(a, cache))
                    .collect();
                if new_args == *args {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::App(sym.clone(), new_args), sort)
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.expand_select_store_inner(inner, cache);
                if new_inner == inner {
                    term
                } else {
                    self.mk_not(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let new_c = self.expand_select_store_inner(c, cache);
                let new_t = self.expand_select_store_inner(t, cache);
                let new_e = self.expand_select_store_inner(e, cache);
                if new_c == c && new_t == t && new_e == e {
                    term
                } else {
                    self.mk_ite(new_c, new_t, new_e)
                }
            }
            _ => term,
        };

        cache.insert(term, result);
        result
    }

    /// Expand `select(store_term, index)` into ITE chain.
    ///
    /// If `store_term` is `store(a, I, v)`, produces:
    ///   `ite(I = index, v, select(a, index))`
    /// and recursively expands the else-branch if `a` is also a store.
    ///
    /// Two depth limits apply:
    /// - `depth`: overall recursion bound (concrete skip-throughs + symbolic ITEs)
    /// - `symbolic_ite_budget`: number of symbolic ITE branches allowed before
    ///   stopping expansion. Each symbolic (non-concrete-distinct) store level
    ///   consumes one unit. Bounded to prevent O(2^N) ITE explosion on deep
    ///   store chains with symbolic indices (storeinv-family, #6367).
    ///
    /// Concrete-distinct indices never generate ITEs (they skip through), so
    /// they only consume from `depth`, not from `symbolic_ite_budget`.
    fn expand_select_over_store(&mut self, array: TermId, index: TermId, depth: usize) -> TermId {
        self.expand_select_over_store_inner(array, index, depth, Self::SYMBOLIC_ITE_BUDGET)
    }

    /// Maximum number of symbolic ITE branches generated per select-over-store
    /// expansion. Benchmarks with short chains (add4, dlx, pipeline) typically
    /// have 1-3 symbolic store levels and converge with ITE expansion. Deep
    /// storeinv chains (5-20 levels) produce O(2^N) ITEs and must be stopped.
    pub(crate) const SYMBOLIC_ITE_BUDGET: usize = 4;

    fn expand_select_over_store_inner(
        &mut self,
        array: TermId,
        index: TermId,
        depth: usize,
        symbolic_ite_budget: usize,
    ) -> TermId {
        if depth == 0 {
            return self.mk_select(array, index);
        }

        match self.get(array).clone() {
            TermData::App(Symbol::Named(ref name), ref args)
                if name == "store" && args.len() == 3 =>
            {
                let inner_array = args[0];
                let store_index = args[1];
                let store_value = args[2];

                // If indices are syntactically identical, just return the value
                if store_index == index {
                    return store_value;
                }

                // If both are provably distinct indices, skip this store level
                // without generating an ITE (no symbolic budget consumed).
                // Handles: concrete constants, and structural patterns like
                // bvadd(base, k1) vs bvadd(base, k2) where k1 != k2 (byte-level
                // memory access patterns common in QF_ABV benchmarks).
                let concrete_distinct = self.are_provably_distinct_indices(index, store_index);
                if concrete_distinct {
                    return self.expand_select_over_store_inner(
                        inner_array,
                        index,
                        depth - 1,
                        symbolic_ite_budget,
                    );
                }

                // Symbolic indices: generate ITE if budget remains, otherwise stop.
                // Stopping at deep chains prevents O(2^N) ITE explosion on
                // storeinv-family benchmarks (#6367). The runtime array theory
                // solver handles the remaining store levels via ROW1/ROW2 lemmas.
                if symbolic_ite_budget == 0 {
                    return self.mk_select(array, index);
                }

                let eq = self.mk_eq(store_index, index);
                let else_branch = self.expand_select_over_store_inner(
                    inner_array,
                    index,
                    depth - 1,
                    symbolic_ite_budget - 1,
                );
                self.mk_ite(eq, store_value, else_branch)
            }
            _ => {
                // Not a store — create select normally
                self.mk_select(array, index)
            }
        }
    }

    /// Apply expand_select_store to all assertions.
    pub fn expand_select_store_all(&mut self, terms: &[TermId]) -> Vec<TermId> {
        let mut cache = HashMap::new();
        terms
            .iter()
            .map(|&t| self.expand_select_store_inner(t, &mut cache))
            .collect()
    }
}
