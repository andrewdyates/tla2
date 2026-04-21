// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array operations for TermStore.

use super::*;

enum StoreIndexRewrite {
    Keep,
    SwapDistinct,
}

impl TermStore {
    // ==================== Array Operations ====================

    /// Create array select with read-over-write simplification: (select a i)
    pub fn mk_select(&mut self, array: TermId, index: TermId) -> TermId {
        // Get the element sort from the array sort
        let elem_sort = match self.sort(array) {
            Sort::Array(arr) => {
                debug_assert!(
                    self.sort(index) == &arr.index_sort,
                    "BUG: mk_select index sort mismatch: expected {:?}, got {:?}",
                    arr.index_sort,
                    self.sort(index)
                );
                arr.element_sort.clone()
            }
            _ => {
                // Sort mismatch: caller passed a non-Array term.
                // CHC solver paths (algebraic invariant validation, portfolio
                // query-only verification) can hit this when back-translated
                // model variables have degraded sorts. Return a dummy select
                // term so catch_z4_panics / SMT Unknown handles it gracefully.
                return self.intern(
                    TermData::App(Symbol::named("select"), vec![array, index]),
                    Sort::Bool,
                );
            }
        };

        // Read-over-const-array simplification: select(const-array(v), i) → v
        if let Some(default_value) = self.get_const_array(array) {
            return default_value;
        }

        // Read-over-write simplification: select(store(a, i, v), i) → v
        if let TermData::App(Symbol::Named(name), args) = self.get(array) {
            if name == "store" && args.len() == 3 {
                let store_index = args[1];
                let store_value = args[2];
                let inner_array = args[0];

                // If indices are identical, return the stored value
                if store_index == index {
                    return store_value;
                }

                // If both indices are constants and different, look through
                if let (Some(idx1), Some(idx2)) = (self.get_int(index), self.get_int(store_index)) {
                    if idx1 != idx2 {
                        return self.mk_select(inner_array, index);
                    }
                }
                if let (Some((val1, _)), Some((val2, _))) =
                    (self.get_bitvec(index), self.get_bitvec(store_index))
                {
                    if val1 != val2 {
                        return self.mk_select(inner_array, index);
                    }
                }
            }
        }

        self.intern(
            TermData::App(Symbol::named("select"), vec![array, index]),
            elem_sort,
        )
    }

    /// Create an array store (write) operation: (store a i v)
    ///
    /// Returns a new array identical to `a` except at index `i` where it has value `v`.
    ///
    /// Simplifications:
    /// - Store-over-store at same index: store(store(a, i, v1), i, v2) → store(a, i, v2)
    /// - Sort-store normalization: store(store(a, j, w), i, v) → store(store(a, i, v), j, w)
    ///   when `i` and `j` are provably distinct interpreted constants and `i < j`
    /// - Squash-store: collapse store chains where the same index appears deeper than 1 level
    ///   (Z3 ref: array_rewriter.cpp:206-239, up to 10 levels deep)
    /// - Constant-array no-op: store(const-array(v), i, v) → const-array(v)
    pub fn mk_store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        if !matches!(self.sort(array), Sort::Array(_)) {
            // Sort mismatch: caller passed a non-Array term. See mk_select
            // comment for the CHC paths that can trigger this.
            let array_sort = self.sort(array).clone();
            return self.intern(
                TermData::App(Symbol::named("store"), vec![array, index, value]),
                array_sort,
            );
        }
        if let Sort::Array(arr) = self.sort(array) {
            debug_assert!(
                self.sort(index) == &arr.index_sort,
                "BUG: mk_store index sort mismatch: expected {:?}, got {:?}",
                arr.index_sort,
                self.sort(index)
            );
            debug_assert!(
                self.sort(value) == &arr.element_sort,
                "BUG: mk_store value sort mismatch: expected {:?}, got {:?}",
                arr.element_sort,
                self.sort(value)
            );
        }
        let array_sort = self.sort(array).clone();

        // store(const-array(v), i, v) -> const-array(v)
        // Z3 ref: array_rewriter.cpp:184-189
        if self.get_const_array(array) == Some(value) {
            return array;
        }

        // Identity store elimination: store(a, i, select(a, i)) → a (#6282)
        if let TermData::App(Symbol::Named(n), a) = self.get(value) {
            if n == "select" && a.len() == 2 && a[0] == array && a[1] == index {
                return array;
            }
        }

        // Store-over-store and sort/squash rewrites require inner store
        if let TermData::App(Symbol::Named(name), args) = self.get(array) {
            if name == "store" && args.len() == 3 {
                let inner_index = args[1];
                let inner_array = args[0];
                let inner_value = args[2];

                if inner_index == index {
                    return self.mk_store(inner_array, index, value);
                }

                match self.store_index_rewrite(index, inner_index) {
                    StoreIndexRewrite::Keep => {}
                    StoreIndexRewrite::SwapDistinct => {
                        let new_inner = self.mk_store(inner_array, index, value);
                        return self.mk_store(new_inner, inner_index, inner_value);
                    }
                }

                if let Some(squashed) =
                    self.squash_store(index, value, inner_array, inner_index, inner_value)
                {
                    return squashed;
                }
            }
        }

        self.intern(
            TermData::App(Symbol::named("store"), vec![array, index, value]),
            array_sort,
        )
    }

    /// Classify the rewrite to apply to a nested store pair.
    ///
    /// Concrete distinct indices can commute unconditionally (the swap is sound
    /// because distinctness is proven). Symbolic indices are left in their
    /// original order — the runtime array theory solver handles the semantic
    /// reasoning about index equality/disequality via ROW1/ROW2 lemmas.
    ///
    /// Prior to this change, symbolic indices triggered `SwapWithEqualityGuard`
    /// which generated `ite(i=j, ...)` terms. This caused combinatorial
    /// explosion on storeinv-family benchmarks where N symbolic swap indices
    /// produce O(2^N) ITE branches (#6367). Z3's approach handles this at the
    /// theory solver level with binary clauses, not at the term level.
    ///
    /// Z3 ref: array_rewriter.cpp:158-176 (concrete swap only; symbolic sorting
    /// uses AST ID ordering but does NOT generate ITE guards).
    fn store_index_rewrite(&self, index: TermId, inner_index: TermId) -> StoreIndexRewrite {
        if let (Some(idx_outer), Some(idx_inner)) = (self.get_int(index), self.get_int(inner_index))
        {
            if idx_inner > idx_outer {
                StoreIndexRewrite::SwapDistinct
            } else {
                StoreIndexRewrite::Keep
            }
        } else if let (Some((val_outer, w_outer)), Some((val_inner, w_inner))) =
            (self.get_bitvec(index), self.get_bitvec(inner_index))
        {
            if w_outer == w_inner && val_inner > val_outer {
                StoreIndexRewrite::SwapDistinct
            } else {
                StoreIndexRewrite::Keep
            }
        } else {
            // Symbolic indices: keep original order. Commuting stores requires
            // proven distinctness — if i and j are equal at runtime,
            // store(store(a,j,w),i,v) ≠ store(store(a,i,v),j,w) because the
            // outer store wins at the shared index.
            // Z3 ref: array_rewriter.cpp:130-139 returns l_undef for symbolic
            // indices, blocking sort_store. Only concrete constants go through
            // are_distinct().
            StoreIndexRewrite::Keep
        }
    }

    /// Collapse store chains where the same index appears deeper than 1 level.
    ///
    /// Walks down the inner chain up to 10 levels. If a store at `index` is found,
    /// removes it by threading the base array through the intermediate parents,
    /// then wraps with `store(result, index, value)`.
    /// Z3 ref: array_rewriter.cpp:206-239
    fn squash_store(
        &mut self,
        index: TermId,
        value: TermId,
        inner_array: TermId,
        inner_index: TermId,
        inner_value: TermId,
    ) -> Option<TermId> {
        const MAX_DEPTH: usize = 10;
        if !self.are_provably_distinct_indices(index, inner_index) {
            return None;
        }

        let mut cursor = inner_array;
        let mut parents: Vec<(TermId, TermId)> = vec![(inner_index, inner_value)];
        let mut depth = 1usize;

        while depth < MAX_DEPTH {
            match self.get(cursor) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    let cur_index = a[1];
                    let cur_value = a[2];
                    let cur_base = a[0];

                    if cur_index == index {
                        let mut result = cur_base;
                        for &(p_idx, p_val) in parents.iter().rev() {
                            result = self.mk_store(result, p_idx, p_val);
                        }
                        return Some(self.mk_store(result, index, value));
                    }

                    if !self.are_provably_distinct_indices(index, cur_index) {
                        return None;
                    }

                    parents.push((cur_index, cur_value));
                    cursor = cur_base;
                    depth += 1;
                }
                _ => return None,
            }
        }
        None
    }

    /// Check if two indices are provably distinct.
    ///
    /// Handles:
    /// - Concrete constants (Int, BV): direct comparison
    /// - Structural patterns: `bvadd(base, k1)` vs `bvadd(base, k2)` where
    ///   k1 != k2, and `bvadd(base, k)` vs `base` (where k != 0)
    ///
    /// The structural patterns are critical for QF_ABV byte-level memory access:
    /// `select(store(store(store(store(mem, bvadd(sp,0), v0), bvadd(sp,1), v1),
    ///   bvadd(sp,2), v2), bvadd(sp,3), v3), bvadd(sp2, k))` — the store chain
    /// uses `bvadd(base, offset)` indices that differ only in the constant offset.
    /// Without structural detection, these consume symbolic ITE budget and generate
    /// huge CNF encodings (150k+ vars from 60-line benchmarks).
    pub(crate) fn are_provably_distinct_indices(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return false;
        }
        // Check 1: concrete constants
        if let (Some(va), Some(vb)) = (self.get_int(a), self.get_int(b)) {
            return va != vb;
        }
        if let (Some((va, wa)), Some((vb, wb))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return wa == wb && va != vb;
        }
        // Check 2: structural bvadd/bvsub patterns
        self.are_structurally_distinct_bv_indices(a, b)
    }

    /// Decompose a BV index into (base, constant_offset) form.
    ///
    /// Returns `Some((base, offset, width))` for patterns:
    /// - `bvadd(base, const)` -> (base, const, width)
    /// - `bvadd(const, base)` -> (base, const, width) [commutative]
    /// - `bvsub(base, const)` -> (base, -const mod 2^w, width)
    /// - bare `base` -> (base, 0, width) when base is a BV term
    fn decompose_bv_offset(&self, term: TermId) -> Option<(TermId, BigInt, u32)> {
        let width = match self.sort(term) {
            Sort::BitVec(bv) => bv.width,
            _ => return None,
        };

        match self.get(term) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                match name.as_str() {
                    "bvadd" => {
                        // bvadd(base, const) or bvadd(const, base)
                        if let Some((val, _)) = self.get_bitvec(args[1]) {
                            Some((args[0], val.clone(), width))
                        } else if let Some((val, _)) = self.get_bitvec(args[0]) {
                            Some((args[1], val.clone(), width))
                        } else {
                            None
                        }
                    }
                    "bvsub" => {
                        // bvsub(base, const) -> base + (-const mod 2^w)
                        if let Some((val, _)) = self.get_bitvec(args[1]) {
                            let modulus = BigInt::from(1u8) << width;
                            let neg_val = ((&modulus - val) % &modulus + &modulus) % &modulus;
                            Some((args[0], neg_val, width))
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => {
                // Bare BV term: offset = 0
                Some((term, BigInt::from(0u8), width))
            }
        }
    }

    /// Check structural distinctness for BV index expressions.
    ///
    /// Detects: `bvadd(base, k1)` vs `bvadd(base, k2)` where k1 != k2,
    /// and `bvadd(base, k)` vs `base` (implicit offset 0).
    fn are_structurally_distinct_bv_indices(&self, a: TermId, b: TermId) -> bool {
        let Some((base_a, off_a, w_a)) = self.decompose_bv_offset(a) else {
            return false;
        };
        let Some((base_b, off_b, w_b)) = self.decompose_bv_offset(b) else {
            return false;
        };
        // Same base, same width, different offsets
        base_a == base_b && w_a == w_b && off_a != off_b
    }

    /// Create a constant array: ((as const (Array T1 T2)) v)
    ///
    /// Returns an array where every index maps to the given default value.
    /// The array has sort (Array index_sort elem_sort) where elem_sort is the sort of the value.
    pub fn mk_const_array(&mut self, index_sort: Sort, value: TermId) -> TermId {
        let elem_sort = self.sort(value).clone();
        let array_sort = Sort::array(index_sort, elem_sort);

        self.intern(
            TermData::App(Symbol::named("const-array"), vec![value]),
            array_sort,
        )
    }

    /// Check if a term is a constant array, returning the default value if so
    pub fn get_const_array(&self, term: TermId) -> Option<TermId> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args)
                if name == "const-array" && args.len() == 1 =>
            {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// Lookup a named variable/constant
    pub fn lookup(&self, name: &str) -> Option<TermId> {
        self.names.get(name).map(|(id, _)| *id)
    }

    /// Check if a term is a Boolean constant
    pub fn is_bool_const(&self, id: TermId) -> Option<bool> {
        match self.get(id) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    /// Check if a term is true
    pub fn is_true(&self, id: TermId) -> bool {
        self.is_bool_const(id) == Some(true)
    }

    /// Check if a term is false
    pub fn is_false(&self, id: TermId) -> bool {
        self.is_bool_const(id) == Some(false)
    }

    /// Get all children of a term
    pub fn children(&self, id: TermId) -> Vec<TermId> {
        match self.get(id) {
            TermData::Const(_) | TermData::Var(_, _) => vec![],
            TermData::App(_, args) => args.clone(),
            TermData::Let(bindings, body) => {
                let mut children: Vec<_> = bindings.iter().map(|(_, t)| *t).collect();
                children.push(*body);
                children
            }
            TermData::Not(t) => vec![*t],
            TermData::Ite(c, t, e) => vec![*c, *t, *e],
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
        }
    }
}
