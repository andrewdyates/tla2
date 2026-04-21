// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-related BV axiom generation for combined theories (ABV, AUFBV).
//!
//! Generates array read-over-write (ROW) and functional consistency axioms
//! as CNF clauses for eager bit-blasting combined theory solving.
//! Uses normalized BV index keys to detect semantically equal indices.
//!
//! Split from `bv_axioms.rs` for code health (#7006, #5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use z4_bv::BvSolver;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, TermId};

use super::super::Executor;
use super::ArrayAxiomResult;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum NormalizedBvIndexKey {
    Raw(TermId),
    Const {
        width: u32,
        value: BigInt,
    },
    ZeroExtend {
        extra_bits: u32,
        inner: Box<Self>,
    },
    BvAdd {
        width: u32,
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    BvSub {
        width: u32,
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
}

impl NormalizedBvIndexKey {
    /// Check if two normalized index keys are provably distinct.
    ///
    /// Catches the common byte-load pattern: `bvadd(base, 0)` vs
    /// `bvadd(base, 1)` vs `bvadd(base, 2)` etc. — same symbolic base
    /// but different constant offsets.
    fn are_provably_distinct(a: &Self, b: &Self) -> bool {
        match (a, b) {
            // Two different constants at the same width
            (
                Self::Const {
                    width: w1,
                    value: v1,
                },
                Self::Const {
                    width: w2,
                    value: v2,
                },
            ) => w1 == w2 && v1 != v2,

            // base + c1 vs base + c2 where c1 != c2
            (
                Self::BvAdd {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::BvAdd {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
            ) if w1 == w2 && l1 == l2 => Self::are_provably_distinct(r1, r2),

            // base - c1 vs base - c2 where c1 != c2
            (
                Self::BvSub {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::BvSub {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
            ) if w1 == w2 && l1 == l2 => Self::are_provably_distinct(r1, r2),

            // base + nonzero_const vs base (after zero-folding, bare base = offset 0)
            (
                Self::BvAdd {
                    lhs, rhs: offset, ..
                },
                other,
            )
            | (
                other,
                Self::BvAdd {
                    lhs, rhs: offset, ..
                },
            ) if lhs.as_ref() == other => {
                matches!(offset.as_ref(), Self::Const { value, .. } if *value != BigInt::from(0u8))
            }

            // ZeroExtend with same extra bits — compare inner keys
            (
                Self::ZeroExtend {
                    extra_bits: e1,
                    inner: i1,
                },
                Self::ZeroExtend {
                    extra_bits: e2,
                    inner: i2,
                },
            ) if e1 == e2 => Self::are_provably_distinct(i1, i2),

            _ => false,
        }
    }
}

impl Executor {
    /// Ensure array-index/value BV terms are bit-blasted before generating
    /// array axioms. Select terms are opaque to the BV bitblaster, so their
    /// index subterms must be explicitly materialized.
    pub(in crate::executor) fn materialize_array_bv_terms(
        &self,
        bv_solver: &mut BvSolver<'_>,
        extra_terms: &[TermId],
    ) {
        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::new();

        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }
        for &term in extra_terms {
            self.collect_array_terms(term, &mut select_terms, &mut store_terms, &mut visited);
        }

        for &(select_term, _, select_idx) in &select_terms {
            let _ = bv_solver.ensure_term_bits(select_term);
            let _ = bv_solver.ensure_term_bits(select_idx);
        }

        for &(_, _, store_idx, store_val) in &store_terms {
            let _ = bv_solver.ensure_term_bits(store_idx);
            let _ = bv_solver.ensure_term_bits(store_val);
        }
    }

    fn bitvec_width(&self, term: TermId) -> Option<u32> {
        match self.ctx.terms.sort(term) {
            Sort::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }

    fn normalize_bv_const(value: &BigInt, width: u32) -> BigInt {
        let modulus = BigInt::from(1u8) << width;
        ((value % &modulus) + &modulus) % modulus
    }

    fn zero_const(width: u32) -> NormalizedBvIndexKey {
        NormalizedBvIndexKey::Const {
            width,
            value: BigInt::from(0u8),
        }
    }

    fn normalize_bv_index_key(&self, term: TermId) -> NormalizedBvIndexKey {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) => NormalizedBvIndexKey::Const {
                width: *width,
                value: Self::normalize_bv_const(value, *width),
            },
            TermData::App(sym, args) if args.len() == 1 && sym.name() == "zero_extend" => {
                let Some(arg_width) = self.bitvec_width(args[0]) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let Some(result_width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let indexed_extra_bits = match sym {
                    Symbol::Indexed(_, indices) => indices.first().copied(),
                    _ => None,
                };
                let extra_bits =
                    indexed_extra_bits.unwrap_or(result_width.saturating_sub(arg_width));
                if extra_bits == 0 {
                    return self.normalize_bv_index_key(args[0]);
                }
                match self.normalize_bv_index_key(args[0]) {
                    NormalizedBvIndexKey::Const { value, .. } => NormalizedBvIndexKey::Const {
                        width: result_width,
                        value: Self::normalize_bv_const(&value, result_width),
                    },
                    NormalizedBvIndexKey::ZeroExtend {
                        extra_bits: nested_extra,
                        inner: nested_inner,
                    } => NormalizedBvIndexKey::ZeroExtend {
                        extra_bits: nested_extra.saturating_add(extra_bits),
                        inner: nested_inner,
                    },
                    inner => NormalizedBvIndexKey::ZeroExtend {
                        extra_bits,
                        inner: Box::new(inner),
                    },
                }
            }
            TermData::App(sym, args) if args.len() == 2 && sym.name() == "bvadd" => {
                let Some(width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let lhs = self.normalize_bv_index_key(args[0]);
                let rhs = self.normalize_bv_index_key(args[1]);
                if rhs == Self::zero_const(width) {
                    return lhs;
                }
                if lhs == Self::zero_const(width) {
                    return rhs;
                }
                if let (
                    NormalizedBvIndexKey::Const { value: a, .. },
                    NormalizedBvIndexKey::Const { value: b, .. },
                ) = (&lhs, &rhs)
                {
                    return NormalizedBvIndexKey::Const {
                        width,
                        value: Self::normalize_bv_const(&(a + b), width),
                    };
                }
                NormalizedBvIndexKey::BvAdd {
                    width,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            TermData::App(sym, args) if args.len() == 2 && sym.name() == "bvsub" => {
                let Some(width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let lhs = self.normalize_bv_index_key(args[0]);
                let rhs = self.normalize_bv_index_key(args[1]);
                if rhs == Self::zero_const(width) {
                    return lhs;
                }
                if lhs == rhs {
                    return Self::zero_const(width);
                }
                if let (
                    NormalizedBvIndexKey::Const { value: a, .. },
                    NormalizedBvIndexKey::Const { value: b, .. },
                ) = (&lhs, &rhs)
                {
                    return NormalizedBvIndexKey::Const {
                        width,
                        value: Self::normalize_bv_const(&(a - b), width),
                    };
                }
                NormalizedBvIndexKey::BvSub {
                    width,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            _ => NormalizedBvIndexKey::Raw(term),
        }
    }

    /// Generate array axiom clauses for QF_ABV (#4087)
    ///
    /// Collects all select/store terms and generates bit-level axioms:
    /// - ROW1: `(i == j) → select(store(a, i, v), j) == v`
    /// - ROW2: `(i != j) → select(store(a, i, v), j) == select(a, j)`
    ///   (when `select(a, j)` exists and has bits)
    /// - Functional consistency: i = j → select(a, i) = select(a, j)
    ///   (when syntactically different indices exist)
    ///
    /// Uses the same diff-variable XOR encoding as EUF congruence axioms.
    pub(in crate::executor) fn generate_array_bv_axioms(
        &self,
        bv_solver: &BvSolver<'_>,
        bv_offset: u32,
        var_offset: u32,
        extra_terms: &[TermId],
    ) -> ArrayAxiomResult {
        let mut result = ArrayAxiomResult {
            clauses: Vec::new(),
            num_vars: 0,
        };

        // Collect all select and store terms from assertions and extra terms
        // (e.g., assumptions in check-sat-assuming). Shared visited set prevents
        // duplicate work when an assumption term also appears in assertions.
        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::new();

        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }
        for &term in extra_terms {
            self.collect_array_terms(term, &mut select_terms, &mut store_terms, &mut visited);
        }

        if select_terms.is_empty() {
            return result;
        }

        let offset_bit = |bit: i32| -> i32 {
            if bit > 0 {
                bit + bv_offset as i32
            } else {
                bit - bv_offset as i32
            }
        };

        // Build index: array TermId → vec of selects from that array
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
        let mut normalized_select_index: HashMap<TermId, HashMap<NormalizedBvIndexKey, TermId>> =
            HashMap::new();
        for &(select_term, array, index) in &select_terms {
            selects_by_array
                .entry(array)
                .or_default()
                .push((select_term, index));
            normalized_select_index
                .entry(array)
                .or_default()
                .entry(self.normalize_bv_index_key(index))
                .or_insert(select_term);
        }

        let mut next_var = var_offset + 1;

        // Pre-compute normalized index keys for all select and store indices.
        // This avoids redundant O(depth) normalize_bv_index_key calls in the
        // O(N^2) functional consistency loop and O(S×R) ROW loops.
        let mut norm_key_cache: HashMap<TermId, NormalizedBvIndexKey> = HashMap::new();
        for &(_sel, _arr, idx) in &select_terms {
            norm_key_cache
                .entry(idx)
                .or_insert_with(|| self.normalize_bv_index_key(idx));
        }
        for &(_store, _base, store_idx, _val) in &store_terms {
            norm_key_cache
                .entry(store_idx)
                .or_insert_with(|| self.normalize_bv_index_key(store_idx));
        }

        // ROW1/ROW2: For each select(store(a, i, v), j)
        for &(store_term, base_array, store_idx, store_val) in &store_terms {
            let Some(selects) = selects_by_array.get(&store_term) else {
                continue;
            };

            for &(select_term, sel_idx) in selects {
                // Skip syntactically equal indices (handled by mk_select rewriting)
                if store_idx == sel_idx {
                    continue;
                }

                // Get bit representations for all terms
                let Some(idx_i_bits) = bv_solver.get_term_bits(store_idx) else {
                    continue;
                };
                let Some(idx_j_bits) = bv_solver.get_term_bits(sel_idx) else {
                    continue;
                };
                if idx_i_bits.len() != idx_j_bits.len() || idx_i_bits.is_empty() {
                    continue;
                }

                let Some(result_bits) = bv_solver.get_term_bits(select_term) else {
                    continue;
                };
                let Some(val_bits) = bv_solver.get_term_bits(store_val) else {
                    continue;
                };
                if result_bits.len() != val_bits.len() || result_bits.is_empty() {
                    continue;
                }

                // Create diff variables for index bits: diff_k ↔ (i_k ⊕ j_k)
                // Skip bit positions where both are known-equal constants
                // (XOR is trivially 0, contributing nothing to "some_diff").
                let mut diff_vars = Vec::with_capacity(idx_i_bits.len());
                for (&bit_i, &bit_j) in idx_i_bits.iter().zip(idx_j_bits.iter()) {
                    let v_i = bv_solver.bit_constant_value(bit_i);
                    let v_j = bv_solver.bit_constant_value(bit_j);
                    if let (Some(ci), Some(cj)) = (v_i, v_j) {
                        if ci == cj {
                            continue; // Known-equal: XOR is always 0
                        }
                    }

                    let ob_i = offset_bit(bit_i);
                    let ob_j = offset_bit(bit_j);
                    let diff_var = next_var as i32;
                    next_var += 1;
                    diff_vars.push(diff_var);

                    // diff_k ↔ (i_k ⊕ j_k) — 4 XOR clauses
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(vec![-diff_var, ob_i, ob_j]));
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(vec![-diff_var, -ob_i, -ob_j]));
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(vec![-ob_i, ob_j, diff_var]));
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(vec![ob_i, -ob_j, diff_var]));
                }

                // If diff_vars is empty (all bits known-equal), skip this pair
                // — the indices are definitionally equal, handled by mk_select.
                if diff_vars.is_empty() {
                    continue;
                }

                // ROW1: (i == j) → (result == v)
                // Clausal: (some_diff) ∨ (result_k == v_k)
                // = (diff_0 ∨ diff_1 ∨ ... ∨ ¬result_k ∨ v_k)
                //   (diff_0 ∨ diff_1 ∨ ... ∨ result_k ∨ ¬v_k)
                let suffix_start = diff_vars.len();
                let mut clause_buf = Vec::with_capacity(suffix_start + 2);
                clause_buf.extend_from_slice(&diff_vars);
                clause_buf.push(0);
                clause_buf.push(0);

                for (&res_bit, &val_bit) in result_bits.iter().zip(val_bits.iter()) {
                    let ob_r = offset_bit(res_bit);
                    let ob_v = offset_bit(val_bit);

                    clause_buf[suffix_start] = -ob_r;
                    clause_buf[suffix_start + 1] = ob_v;
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(clause_buf.clone()));

                    clause_buf[suffix_start] = ob_r;
                    clause_buf[suffix_start + 1] = -ob_v;
                    result
                        .clauses
                        .push(z4_core::CnfClause::new(clause_buf.clone()));
                }

                // ROW2: (i != j) → (result == select(a, j))
                // Only when select(base_array, sel_idx) exists and has bits.
                // Match by normalized BV index (bvadd/bvsub zero folding, concrete
                // zero_extend folding) so semantically equivalent index terms are
                // connected even when not syntactically identical.
                let norm_sel_idx = norm_key_cache
                    .get(&sel_idx)
                    .cloned()
                    .unwrap_or_else(|| self.normalize_bv_index_key(sel_idx));
                let read_term = normalized_select_index
                    .get(&base_array)
                    .and_then(|by_idx| by_idx.get(&norm_sel_idx))
                    .copied();

                if let Some(read_term) = read_term {
                    if let Some(read_bits) = bv_solver.get_term_bits(read_term) {
                        if read_bits.len() == result_bits.len() {
                            // Create eq_idx variable: eq_idx ↔ ¬(diff_0 ∨ ... ∨ diff_n)
                            let eq_idx = next_var as i32;
                            next_var += 1;

                            // eq_idx → ¬diff_k for each k
                            for &diff_var in &diff_vars {
                                result
                                    .clauses
                                    .push(z4_core::CnfClause::new(vec![-eq_idx, -diff_var]));
                            }
                            // (diff_0 ∨ ... ∨ diff_n ∨ eq_idx)
                            let mut eq_def_clause = diff_vars.clone();
                            eq_def_clause.push(eq_idx);
                            result.clauses.push(z4_core::CnfClause::new(eq_def_clause));

                            // ROW2: ¬eq_idx → (result_k == read_k)
                            // = (eq_idx ∨ ¬result_k ∨ read_k) ∧ (eq_idx ∨ result_k ∨ ¬read_k)
                            for (&res_bit, &rd_bit) in result_bits.iter().zip(read_bits.iter()) {
                                let ob_r = offset_bit(res_bit);
                                let ob_rd = offset_bit(rd_bit);

                                result
                                    .clauses
                                    .push(z4_core::CnfClause::new(vec![eq_idx, -ob_r, ob_rd]));
                                result
                                    .clauses
                                    .push(z4_core::CnfClause::new(vec![eq_idx, ob_r, -ob_rd]));
                            }
                        }
                    }
                }
            }
        }

        // Functional consistency: for selects on the same array with different
        // syntactic indices, add (i == j) → (select(a, i) == select(a, j))
        //
        // Optimization: skip pairs where both indices are fully-constant and
        // distinct — they can never be equal, so functional consistency is
        // vacuously satisfied. This avoids O(N^2) axiom explosion on benchmarks
        // with many constant-indexed selects (e.g., egt-3092 has 34 selects on
        // one array at mostly-distinct constant addresses).
        //
        // Optimization 2: for non-constant pairs, skip diff variable creation
        // for bit positions where both indices have the same known constant
        // value — those bits can never differ, so the XOR is always false.
        for selects in selects_by_array.values() {
            if selects.len() < 2 {
                continue;
            }
            for i in 0..selects.len() {
                for j in (i + 1)..selects.len() {
                    let (sel1, idx1) = selects[i];
                    let (sel2, idx2) = selects[j];
                    if idx1 == idx2 {
                        continue; // Same index → same TermId by hash-consing
                    }

                    let Some(idx1_bits) = bv_solver.get_term_bits(idx1) else {
                        continue;
                    };
                    let Some(idx2_bits) = bv_solver.get_term_bits(idx2) else {
                        continue;
                    };
                    if idx1_bits.len() != idx2_bits.len() || idx1_bits.is_empty() {
                        continue;
                    }

                    // Skip pairs with provably-distinct indices.
                    // Check 1: all bits constant and at least one differs.
                    if bv_solver.are_bits_distinct_constants(idx1_bits, idx2_bits) {
                        continue;
                    }
                    // Check 2: any single bit position known-different makes
                    // "some_diff" always true, so functional consistency is
                    // vacuously satisfied for partially-constant pairs too.
                    let has_known_different_bit =
                        idx1_bits.iter().zip(idx2_bits.iter()).any(|(&b1, &b2)| {
                            matches!(
                                (bv_solver.bit_constant_value(b1), bv_solver.bit_constant_value(b2)),
                                (Some(c1), Some(c2)) if c1 != c2
                            )
                        });
                    if has_known_different_bit {
                        continue;
                    }
                    // Check 3: structural distinctness at the normalized key level
                    // (e.g., base+0 vs base+1 in byte-load patterns).
                    // Uses pre-computed cache to avoid O(N^2 × depth) overhead.
                    if norm_key_cache
                        .get(&idx1)
                        .zip(norm_key_cache.get(&idx2))
                        .is_some_and(|(nk1, nk2)| {
                            NormalizedBvIndexKey::are_provably_distinct(nk1, nk2)
                        })
                    {
                        continue;
                    }

                    let Some(sel1_bits) = bv_solver.get_term_bits(sel1) else {
                        continue;
                    };
                    let Some(sel2_bits) = bv_solver.get_term_bits(sel2) else {
                        continue;
                    };
                    if sel1_bits.len() != sel2_bits.len() || sel1_bits.is_empty() {
                        continue;
                    }

                    // Create diff variables only for bit positions that are NOT
                    // known-equal constants. Known-equal bits always have XOR = 0,
                    // so their diff variables are trivially false and don't
                    // contribute to the "some_diff" disjunction.
                    let mut diff_vars = Vec::with_capacity(idx1_bits.len());
                    for (&b1, &b2) in idx1_bits.iter().zip(idx2_bits.iter()) {
                        // Skip bit positions where both are the same known constant.
                        let v1 = bv_solver.bit_constant_value(b1);
                        let v2 = bv_solver.bit_constant_value(b2);
                        if let (Some(c1), Some(c2)) = (v1, v2) {
                            if c1 == c2 {
                                continue; // Known-equal: XOR is always 0
                            }
                        }

                        let ob1 = offset_bit(b1);
                        let ob2 = offset_bit(b2);
                        let diff_var = next_var as i32;
                        next_var += 1;
                        diff_vars.push(diff_var);

                        result
                            .clauses
                            .push(z4_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                    }

                    // If no diff variables were created (all bits known-equal),
                    // functional consistency is trivially required. But this case
                    // should not happen because idx1 != idx2 syntactically.
                    if diff_vars.is_empty() {
                        continue;
                    }

                    let suffix_start = diff_vars.len();
                    let mut clause_buf = Vec::with_capacity(suffix_start + 2);
                    clause_buf.extend_from_slice(&diff_vars);
                    clause_buf.push(0);
                    clause_buf.push(0);

                    for (&s1_bit, &s2_bit) in sel1_bits.iter().zip(sel2_bits.iter()) {
                        let ob1 = offset_bit(s1_bit);
                        let ob2 = offset_bit(s2_bit);

                        clause_buf[suffix_start] = -ob1;
                        clause_buf[suffix_start + 1] = ob2;
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(clause_buf.clone()));

                        clause_buf[suffix_start] = ob1;
                        clause_buf[suffix_start + 1] = -ob2;
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(clause_buf.clone()));
                    }
                }
            }
        }

        result.num_vars = next_var.saturating_sub(var_offset + 1);
        result
    }

    /// Flatten BV1 bvand assertions: `(= #b1 (bvand t1 t2))` becomes
    /// separate assertions `(= #b1 t1)` and `(= #b1 t2)`.
    ///
    /// The try3/try5 QF_ABV benchmarks encode their entire formula as a single
    /// assertion: `(= (_ bv1 1) (bvand (bvand ...) ...))`.
    /// Flattening the bvand tree exposes individual ITE-wrapped constraints
    /// as separate assertions, enabling store-flat substitution and better
    /// SAT solver propagation.
    pub(in crate::executor) fn flatten_bv1_bvand_assertions(&mut self) {
        let mut new_assertions = Vec::new();
        let mut modified = false;

        for &assertion in &self.ctx.assertions {
            // Match: (= #b1 (bvand ...)) at BV1 width
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(assertion).clone() {
                if sym.name() == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    // Check if one side is #b1 and the other is bvand at BV1
                    let bvand_term = if Self::is_bv1_one_const(&self.ctx.terms, lhs) {
                        Some(rhs)
                    } else if Self::is_bv1_one_const(&self.ctx.terms, rhs) {
                        Some(lhs)
                    } else {
                        None
                    };

                    if let Some(bvand) = bvand_term {
                        let mut leaves = Vec::new();
                        Self::collect_bv1_bvand_leaves_static(&self.ctx.terms, bvand, &mut leaves);
                        if leaves.len() > 1 {
                            modified = true;
                            let bv1_one = self.ctx.terms.mk_bitvec(BigInt::from(1u8), 1);
                            for leaf in leaves {
                                let eq = self.ctx.terms.mk_eq(bv1_one, leaf);
                                new_assertions.push(eq);
                            }
                            continue;
                        }
                    }
                }
            }
            new_assertions.push(assertion);
        }

        if modified {
            self.ctx.assertions = new_assertions;
        }
    }

    /// Check if a term is the BV1 constant #b1 (value 1, width 1).
    fn is_bv1_one_const(terms: &z4_core::TermStore, term: TermId) -> bool {
        matches!(
            terms.get(term),
            TermData::Const(Constant::BitVec { value, width })
                if *width == 1 && *value == BigInt::from(1u8)
        )
    }

    /// Recursively collect leaves of a BV1 bvand tree.
    fn collect_bv1_bvand_leaves_static(
        terms: &z4_core::TermStore,
        term: TermId,
        leaves: &mut Vec<TermId>,
    ) {
        if let TermData::App(ref sym, ref args) = terms.get(term) {
            if sym.name() == "bvand" && args.len() == 2 {
                if let Sort::BitVec(bv) = terms.sort(term) {
                    if bv.width == 1 {
                        let a = args[0];
                        let b = args[1];
                        Self::collect_bv1_bvand_leaves_static(terms, a, leaves);
                        Self::collect_bv1_bvand_leaves_static(terms, b, leaves);
                        return;
                    }
                }
            }
        }
        leaves.push(term);
    }

    /// Count the total number of select terms reachable from assertions.
    /// Used by the adaptive fixpoint gate to skip expensive axiom fixpoints
    /// on formulas with many array selects.
    pub(in crate::executor) fn count_array_selects_in_assertions(&self) -> usize {
        let mut selects = Vec::new();
        let mut stores = Vec::new();
        let mut visited = HashSet::new();
        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut selects, &mut stores, &mut visited);
        }
        selects.len()
    }

    /// Recursively collect select and store terms from an expression
    pub(in crate::executor) fn collect_array_terms(
        &self,
        term: TermId,
        selects: &mut Vec<(TermId, TermId, TermId)>,
        stores: &mut Vec<(TermId, TermId, TermId, TermId)>,
        visited: &mut HashSet<TermId>,
    ) {
        if visited.contains(&term) {
            return;
        }
        visited.insert(term);

        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "select" if args.len() == 2 => {
                        selects.push((term, args[0], args[1]));
                        // Recurse into array and index
                        self.collect_array_terms(args[0], selects, stores, visited);
                        self.collect_array_terms(args[1], selects, stores, visited);
                    }
                    "store" if args.len() == 3 => {
                        stores.push((term, args[0], args[1], args[2]));
                        // Recurse into array, index, and value
                        self.collect_array_terms(args[0], selects, stores, visited);
                        self.collect_array_terms(args[1], selects, stores, visited);
                        self.collect_array_terms(args[2], selects, stores, visited);
                    }
                    _ => {
                        // Recurse into other function applications
                        for &arg in args {
                            self.collect_array_terms(arg, selects, stores, visited);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                self.collect_array_terms(*inner, selects, stores, visited);
            }
            TermData::Ite(c, t, e) => {
                self.collect_array_terms(*c, selects, stores, visited);
                self.collect_array_terms(*t, selects, stores, visited);
                self.collect_array_terms(*e, selects, stores, visited);
            }
            _ => {}
        }
    }
}
