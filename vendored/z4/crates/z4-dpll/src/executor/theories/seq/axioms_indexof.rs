// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Index-finding seq axiom generation: indexof, last_indexof.
//!
//! Extracted from `axioms_search.rs` as part of code-health module split.
//! Replacement operations (seq.replace) are in the sibling `axioms_replace` module.
//! These methods share the pattern of introducing new contains terms
//! (returning `(Vec<TermId>, Vec<(TermId, TermId, TermId)>)`).

use num_bigint::BigInt;
use num_traits::Zero;

use super::super::super::Executor;
use super::scan::SeqTermScan;
use z4_core::term::{Constant, Symbol, TermData, TermId};

impl Executor {
    /// Generate `seq.indexof` axioms (#5841, #5998).
    ///
    /// Returns `(axioms, new_contains_terms)` where `new_contains_terms` are fresh
    /// `contains(s,t)` terms introduced by indexof that need skolem decomposition.
    ///
    /// Zero-offset (Z3 seq_axioms.cpp:429-476): decomposition + tightest_prefix.
    /// Non-zero offset (Z3 seq_axioms.cpp:477-511): reduction to zero-offset on suffix.
    pub(super) fn generate_seq_indexof_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> (Vec<TermId>, Vec<(TermId, TermId, TermId)>) {
        let mut axioms = Vec::new();
        let mut new_contains_terms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));

        for &(indexof_term, s, t, offset) in &scan.indexof_terms {
            let seq_sort = self.ctx.terms.sort(s).clone();
            let len_s = self.mk_seq_len(s);

            // Create contains(s, t) — tracked for caller axiom generation (#5998 Bug 1).
            let contains = self.ctx.terms.mk_app(
                Symbol::named("seq.contains"),
                vec![s, t],
                z4_core::Sort::Bool,
            );
            new_contains_terms.push((contains, s, t));

            let empty = self.mk_seq_empty(&seq_sort);
            // len(empty) = 0 — needed so solver can derive t != empty from len(t) > 0.
            let len_empty = self.mk_seq_len(empty);
            axioms.push(self.ctx.terms.mk_eq(len_empty, zero));
            let t_eq_empty = self.ctx.terms.mk_eq(t, empty);
            let t_ne_empty = self.ctx.terms.mk_not(t_eq_empty);

            // Explicit bridge: t = empty => len(t) = 0.
            // The solver needs this to derive `t != empty` when `len(t) > 0`.
            // Without it, congruence propagation of `t = empty => len(t) = 0`
            // may not fire in the combined EUF+LIA solver.
            let len_t = self.mk_seq_len(t);
            let len_t_eq_0 = self.ctx.terms.mk_eq(len_t, zero);
            let t_implies_len0 = self.ctx.terms.mk_implies(t_eq_empty, len_t_eq_0);
            axioms.push(t_implies_len0);

            // Universal: !contains(s, t) => r = -1
            let not_contains = self.ctx.terms.mk_not(contains);
            let eq_neg1 = self.ctx.terms.mk_eq(indexof_term, neg_one);
            axioms.push(self.ctx.terms.mk_implies(not_contains, eq_neg1));

            let is_zero_offset = offset == zero
                || matches!(
                    self.ctx.terms.get(offset),
                    TermData::Const(Constant::Int(ref v)) if v.is_zero()
                );

            if is_zero_offset {
                // === Zero-offset: indexof(s, t, 0) ===
                let sk_left = self.ctx.terms.mk_fresh_var("seq.idx.l", seq_sort.clone());
                let sk_right = self.ctx.terms.mk_fresh_var("seq.idx.r", seq_sort.clone());

                // contains(s, t) & t != "" => s = sk_left ++ t ++ sk_right
                let inner = self.ctx.terms.mk_app(
                    Symbol::named("seq.++"),
                    vec![t, sk_right],
                    seq_sort.clone(),
                );
                let full = self.ctx.terms.mk_app(
                    Symbol::named("seq.++"),
                    vec![sk_left, inner],
                    seq_sort.clone(),
                );
                let decomp = self.ctx.terms.mk_eq(s, full);
                let pos_cond = self.ctx.terms.mk_and(vec![contains, t_ne_empty]);
                axioms.push(self.ctx.terms.mk_implies(pos_cond, decomp));

                // contains(s, t) & t != "" => r = len(sk_left)
                let len_left = self.mk_seq_len(sk_left);
                let r_eq_len = self.ctx.terms.mk_eq(indexof_term, len_left);
                let ne2 = self.ctx.terms.mk_not(t_eq_empty);
                let pos_cond2 = self.ctx.terms.mk_and(vec![contains, ne2]);
                axioms.push(self.ctx.terms.mk_implies(pos_cond2, r_eq_len));

                // contains(s, t) => r >= 0
                let r_ge_0 = self.ctx.terms.mk_ge(indexof_term, zero);
                axioms.push(self.ctx.terms.mk_implies(contains, r_ge_0));

                // t = "" => r = 0
                let r_eq_0 = self.ctx.terms.mk_eq(indexof_term, zero);
                axioms.push(self.ctx.terms.mk_implies(t_eq_empty, r_eq_0));

                // Tightest prefix (#5998 Bug 2): leftmost occurrence guarantee.
                // Z3 seq_axioms.cpp:372-390.
                // t = "" OR !contains(sk_left ++ extract(t, 0, len(t)-1), t)
                let len_t = self.mk_seq_len(t);
                let one = self.ctx.terms.mk_int(BigInt::from(1));
                let len_t_m1 = self.ctx.terms.mk_sub(vec![len_t, one]);
                let first_t = self.ctx.terms.mk_app(
                    Symbol::named("seq.extract"),
                    vec![t, zero, len_t_m1],
                    seq_sort.clone(),
                );
                let pfx_init = self.ctx.terms.mk_app(
                    Symbol::named("seq.++"),
                    vec![sk_left, first_t],
                    seq_sort.clone(),
                );
                let cnt_earlier = self.ctx.terms.mk_app(
                    Symbol::named("seq.contains"),
                    vec![pfx_init, t],
                    z4_core::Sort::Bool,
                );
                // Track cnt_earlier so it gets contains axioms (#5998 R1 Finding 2).
                // Without this, the solver freely sets cnt_earlier = false, making
                // the tightest-prefix guarantee vacuous.
                new_contains_terms.push((cnt_earlier, pfx_init, t));
                let not_cnt_earlier = self.ctx.terms.mk_not(cnt_earlier);
                axioms.push(self.ctx.terms.mk_or(vec![t_eq_empty, not_cnt_earlier]));

                // Non-negativity for skolem lengths
                axioms.push(self.ctx.terms.mk_ge(len_left, zero));
                let len_right = self.mk_seq_len(sk_right);
                axioms.push(self.ctx.terms.mk_ge(len_right, zero));
            } else {
                // === Non-zero offset (#5998 Bug 3): reduce to zero-offset on suffix ===
                // Z3 seq_axioms.cpp:477-511.

                // offset < 0 => r = -1
                let off_neg = self.ctx.terms.mk_lt(offset, zero);
                let r_m1_a = self.ctx.terms.mk_eq(indexof_term, neg_one);
                axioms.push(self.ctx.terms.mk_implies(off_neg, r_m1_a));

                // offset >= len(s) & t != "" => r = -1
                let off_ge_len = self.ctx.terms.mk_ge(offset, len_s);
                let ge_ne = self.ctx.terms.mk_and(vec![off_ge_len, t_ne_empty]);
                let r_m1_b = self.ctx.terms.mk_eq(indexof_term, neg_one);
                axioms.push(self.ctx.terms.mk_implies(ge_ne, r_m1_b));

                // Redundant LIA-friendly variant: offset >= len(s) & len(t) > 0 => r = -1.
                // The solver may not derive t != "" from len(t) > 0 via EUF bridge, so
                // this gives LIA a direct path without needing empty-string reasoning.
                let len_t = self.mk_seq_len(t);
                let len_t_gt_0 = self.ctx.terms.mk_gt(len_t, zero);
                let ge_len_pos = self.ctx.terms.mk_and(vec![off_ge_len, len_t_gt_0]);
                let r_m1_lia = self.ctx.terms.mk_eq(indexof_term, neg_one);
                axioms.push(self.ctx.terms.mk_implies(ge_len_pos, r_m1_lia));

                // offset > len(s) => r = -1
                let off_gt_len = self.ctx.terms.mk_gt(offset, len_s);
                let r_m1_c = self.ctx.terms.mk_eq(indexof_term, neg_one);
                axioms.push(self.ctx.terms.mk_implies(off_gt_len, r_m1_c));

                // offset = len(s) & t = "" => r = offset
                let off_eq_len = self.ctx.terms.mk_eq(offset, len_s);
                let edge = self.ctx.terms.mk_and(vec![off_eq_len, t_eq_empty]);
                let r_eq_off = self.ctx.terms.mk_eq(indexof_term, offset);
                axioms.push(self.ctx.terms.mk_implies(edge, r_eq_off));

                // General: 0 <= offset < len(s) => split s = pfx ++ sfx
                // Use extract(s,...) to ground pfx/sfx in s (#5998).
                // Also inline extract axioms since these synthesized extract
                // terms aren't in the scan.
                let off_ge_0 = self.ctx.terms.mk_ge(offset, zero);
                let off_lt_len = self.ctx.terms.mk_lt(offset, len_s);
                let valid_off = self.ctx.terms.mk_and(vec![off_ge_0, off_lt_len]);

                // pfx = extract(s, 0, offset), sfx = extract(s, offset, len(s)-offset)
                let sk_pfx = self.ctx.terms.mk_app(
                    Symbol::named("seq.extract"),
                    vec![s, zero, offset],
                    seq_sort.clone(),
                );
                let sfx_len_expr = self.ctx.terms.mk_sub(vec![len_s, offset]);
                let sk_sfx = self.ctx.terms.mk_app(
                    Symbol::named("seq.extract"),
                    vec![s, offset, sfx_len_expr],
                    seq_sort.clone(),
                );

                // s = pfx ++ sfx (decomposition for EUF)
                let split = self.ctx.terms.mk_app(
                    Symbol::named("seq.++"),
                    vec![sk_pfx, sk_sfx],
                    seq_sort.clone(),
                );
                let s_eq_split = self.ctx.terms.mk_eq(s, split);
                axioms.push(self.ctx.terms.mk_implies(valid_off, s_eq_split));

                let len_pfx = self.mk_seq_len(sk_pfx);
                let pfx_eq_off = self.ctx.terms.mk_eq(len_pfx, offset);
                axioms.push(self.ctx.terms.mk_implies(valid_off, pfx_eq_off));

                // Inline extract decomposition for sfx.
                // s = ek_pre ++ sfx ++ ek_post, len(ek_pre) = offset
                {
                    let ek_pre = self
                        .ctx
                        .terms
                        .mk_fresh_var("seq.eidx.pre", seq_sort.clone());
                    let ek_post = self
                        .ctx
                        .terms
                        .mk_fresh_var("seq.eidx.post", seq_sort.clone());

                    let e_inner = self.ctx.terms.mk_app(
                        Symbol::named("seq.++"),
                        vec![sk_sfx, ek_post],
                        seq_sort.clone(),
                    );
                    let e_full = self.ctx.terms.mk_app(
                        Symbol::named("seq.++"),
                        vec![ek_pre, e_inner],
                        seq_sort.clone(),
                    );
                    let e_decomp = self.ctx.terms.mk_eq(s, e_full);
                    axioms.push(self.ctx.terms.mk_implies(valid_off, e_decomp));

                    let len_ek_pre = self.mk_seq_len(ek_pre);
                    let ek_pre_eq = self.ctx.terms.mk_eq(len_ek_pre, offset);
                    axioms.push(self.ctx.terms.mk_implies(valid_off, ek_pre_eq));

                    // len(sfx) = len(s) - offset
                    let len_sfx_here = self.mk_seq_len(sk_sfx);
                    let sfx_len_ax = self.ctx.terms.mk_eq(len_sfx_here, sfx_len_expr);
                    axioms.push(self.ctx.terms.mk_implies(valid_off, sfx_len_ax));

                    // len(ek_post) = 0 (sfx spans to end of s)
                    let len_ek_post = self.mk_seq_len(ek_post);
                    let ek_post_eq = self.ctx.terms.mk_eq(len_ek_post, zero);
                    axioms.push(self.ctx.terms.mk_implies(valid_off, ek_post_eq));

                    axioms.push(self.ctx.terms.mk_ge(len_ek_pre, zero));
                    axioms.push(self.ctx.terms.mk_ge(len_ek_post, zero));
                }

                // indexof(sfx, t, 0) — zero-offset search on suffix
                let idx_sfx = self.ctx.terms.mk_app(
                    Symbol::named("seq.indexof"),
                    vec![sk_sfx, t, zero],
                    z4_core::Sort::Int,
                );

                // The inner indexof also needs contains(sfx, t) axioms.
                // Synthesize contains(sfx, t) and track it (#5998 Bug 3).
                let cnt_sfx = self.ctx.terms.mk_app(
                    Symbol::named("seq.contains"),
                    vec![sk_sfx, t],
                    z4_core::Sort::Bool,
                );
                new_contains_terms.push((cnt_sfx, sk_sfx, t));

                // !contains(sfx, t) => indexof(sfx, t, 0) = -1
                let not_cnt_sfx = self.ctx.terms.mk_not(cnt_sfx);
                let idx_eq_m1 = self.ctx.terms.mk_eq(idx_sfx, neg_one);
                axioms.push(self.ctx.terms.mk_implies(not_cnt_sfx, idx_eq_m1));

                // indexof(sfx, t, 0) >= -1
                axioms.push(self.ctx.terms.mk_ge(idx_sfx, neg_one));

                // contains(sfx, t) => indexof(sfx, t, 0) >= 0
                let idx_ge0_cnt = self.ctx.terms.mk_ge(idx_sfx, zero);
                axioms.push(self.ctx.terms.mk_implies(cnt_sfx, idx_ge0_cnt));

                // --- Inline zero-offset decomposition for idx_sfx (#5998 R1 Finding 1) ---
                // idx_sfx = indexof(sk_sfx, t, 0) is a synthesized term NOT in the
                // scan, so it has no decomposition axioms. Inline them here so the
                // solver can't assign arbitrary values to idx_sfx.
                {
                    let sk_left2 = self.ctx.terms.mk_fresh_var("seq.idx2.l", seq_sort.clone());
                    let sk_right2 = self.ctx.terms.mk_fresh_var("seq.idx2.r", seq_sort.clone());

                    // contains(sfx, t) & t != "" => sfx = sk_left2 ++ t ++ sk_right2
                    let inner2 = self.ctx.terms.mk_app(
                        Symbol::named("seq.++"),
                        vec![t, sk_right2],
                        seq_sort.clone(),
                    );
                    let full2 = self.ctx.terms.mk_app(
                        Symbol::named("seq.++"),
                        vec![sk_left2, inner2],
                        seq_sort.clone(),
                    );
                    let decomp2 = self.ctx.terms.mk_eq(sk_sfx, full2);
                    let ne2 = self.ctx.terms.mk_not(t_eq_empty);
                    let pos_cond2 = self.ctx.terms.mk_and(vec![cnt_sfx, ne2]);
                    axioms.push(self.ctx.terms.mk_implies(pos_cond2, decomp2));

                    // contains(sfx, t) & t != "" => idx_sfx = len(sk_left2)
                    let len_left2 = self.mk_seq_len(sk_left2);
                    let idx_eq_len2 = self.ctx.terms.mk_eq(idx_sfx, len_left2);
                    let ne2b = self.ctx.terms.mk_not(t_eq_empty);
                    let pos_cond2b = self.ctx.terms.mk_and(vec![cnt_sfx, ne2b]);
                    axioms.push(self.ctx.terms.mk_implies(pos_cond2b, idx_eq_len2));

                    // t = "" => idx_sfx = 0
                    let idx_eq_0 = self.ctx.terms.mk_eq(idx_sfx, zero);
                    axioms.push(self.ctx.terms.mk_implies(t_eq_empty, idx_eq_0));

                    // Tightest prefix for inner indexof: leftmost occurrence in sfx.
                    // t = "" OR !contains(sk_left2 ++ extract(t, 0, len(t)-1), t)
                    let len_t2 = self.mk_seq_len(t);
                    let one = self.ctx.terms.mk_int(BigInt::from(1));
                    let len_t2_m1 = self.ctx.terms.mk_sub(vec![len_t2, one]);
                    let first_t2 = self.ctx.terms.mk_app(
                        Symbol::named("seq.extract"),
                        vec![t, zero, len_t2_m1],
                        seq_sort.clone(),
                    );
                    let pfx_init2 = self.ctx.terms.mk_app(
                        Symbol::named("seq.++"),
                        vec![sk_left2, first_t2],
                        seq_sort.clone(),
                    );
                    let cnt_earlier2 = self.ctx.terms.mk_app(
                        Symbol::named("seq.contains"),
                        vec![pfx_init2, t],
                        z4_core::Sort::Bool,
                    );
                    // Track for axiom generation.
                    new_contains_terms.push((cnt_earlier2, pfx_init2, t));
                    let not_cnt_earlier2 = self.ctx.terms.mk_not(cnt_earlier2);
                    axioms.push(self.ctx.terms.mk_or(vec![t_eq_empty, not_cnt_earlier2]));

                    // Non-negativity for inner skolems.
                    axioms.push(self.ctx.terms.mk_ge(len_left2, zero));
                    let len_right2 = self.mk_seq_len(sk_right2);
                    axioms.push(self.ctx.terms.mk_ge(len_right2, zero));
                }

                // indexof(sfx, t, 0) = -1 => r = -1
                let idx_m1 = self.ctx.terms.mk_eq(idx_sfx, neg_one);
                let nf = self.ctx.terms.mk_and(vec![valid_off, idx_m1]);
                let r_m1_d = self.ctx.terms.mk_eq(indexof_term, neg_one);
                axioms.push(self.ctx.terms.mk_implies(nf, r_m1_d));

                // indexof(sfx, t, 0) >= 0 => r = offset + indexof(sfx, t, 0)
                let idx_ge0 = self.ctx.terms.mk_ge(idx_sfx, zero);
                let found = self.ctx.terms.mk_and(vec![valid_off, idx_ge0]);
                let sum = self.ctx.terms.mk_add(vec![offset, idx_sfx]);
                let r_eq_sum = self.ctx.terms.mk_eq(indexof_term, sum);
                axioms.push(self.ctx.terms.mk_implies(found, r_eq_sum));

                axioms.push(self.ctx.terms.mk_ge(len_pfx, zero));
                let len_sfx = self.mk_seq_len(sk_sfx);
                axioms.push(self.ctx.terms.mk_ge(len_sfx, zero));

                // Concat length: len(sfx) = len(s) - offset when valid.
                // The synthesized concat (pfx ++ sfx) isn't in the scan, so
                // len(pfx ++ sfx) = len(pfx) + len(sfx) never fires. Assert directly.
                let sfx_len_eq = self.ctx.terms.mk_sub(vec![len_s, offset]);
                let len_sfx_ax = self.ctx.terms.mk_eq(len_sfx, sfx_len_eq);
                axioms.push(self.ctx.terms.mk_implies(valid_off, len_sfx_ax));
            }

            // r >= -1 always
            axioms.push(self.ctx.terms.mk_ge(indexof_term, neg_one));
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
        }

        (axioms, new_contains_terms)
    }

    /// Generate axioms for `seq.last_indexof(t, s)` (#6030).
    ///
    /// Ported from Z3 `seq_axioms.cpp:514-552` (add_last_indexof_axiom).
    ///
    /// For `i = last_indexof(t, s)`:
    ///   1. !contains(t, s)          => i = -1
    ///   2. s = ""                   => i = len(t)
    ///   3. contains(t, s) & s != "" => t = x ++ s ++ y & i = len(x)
    ///   4. contains(t, s) & s != "" => !contains(tail(s) ++ y, s)  [rightmost]
    ///   5. i >= -1
    ///   6. i <= len(t)
    pub(super) fn generate_seq_last_indexof_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> (Vec<TermId>, Vec<(TermId, TermId, TermId)>) {
        let mut axioms = Vec::new();
        let mut new_contains_terms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
        let one = self.ctx.terms.mk_int(BigInt::from(1));

        for &(lidx_term, t, s) in &scan.last_indexof_terms {
            let seq_sort = self.ctx.terms.sort(t).clone();
            let len_t = self.mk_seq_len(t);
            let len_s = self.mk_seq_len(s);

            // contains(t, s)
            let contains = self.ctx.terms.mk_app(
                Symbol::named("seq.contains"),
                vec![t, s],
                z4_core::Sort::Bool,
            );
            new_contains_terms.push((contains, t, s));

            let empty = self.mk_seq_empty(&seq_sort);
            let s_eq_empty = self.ctx.terms.mk_eq(s, empty);
            let s_ne_empty = self.ctx.terms.mk_not(s_eq_empty);

            // Axiom 1: !contains(t, s) => i = -1
            let not_contains = self.ctx.terms.mk_not(contains);
            let eq_neg1 = self.ctx.terms.mk_eq(lidx_term, neg_one);
            axioms.push(self.ctx.terms.mk_implies(not_contains, eq_neg1));

            // Axiom 2: s = "" => i = len(t)
            let eq_len_t = self.ctx.terms.mk_eq(lidx_term, len_t);
            axioms.push(self.ctx.terms.mk_implies(s_eq_empty, eq_len_t));

            // Skolem variables for decomposition
            let sk_left = self.ctx.terms.mk_fresh_var("seq.lidx.l", seq_sort.clone());
            let sk_right = self.ctx.terms.mk_fresh_var("seq.lidx.r", seq_sort.clone());

            // Axiom 3: contains(t, s) & s != "" => t = sk_left ++ s ++ sk_right
            let s_and_right =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![s, sk_right], seq_sort.clone());
            let full = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_left, s_and_right],
                seq_sort.clone(),
            );
            let decomp = self.ctx.terms.mk_eq(t, full);
            let guard = self.ctx.terms.mk_and(vec![contains, s_ne_empty]);
            axioms.push(self.ctx.terms.mk_implies(guard, decomp));

            // contains(t, s) & s != "" => i = len(sk_left)
            let len_left = self.mk_seq_len(sk_left);
            let i_eq_len_left = self.ctx.terms.mk_eq(lidx_term, len_left);
            let ne2 = self.ctx.terms.mk_not(s_eq_empty);
            let guard2 = self.ctx.terms.mk_and(vec![contains, ne2]);
            axioms.push(self.ctx.terms.mk_implies(guard2, i_eq_len_left));

            // Axiom 4 (rightmost guarantee):
            // contains(t, s) & s != "" => !contains(tail(s) ++ sk_right, s)
            // where tail(s) = extract(s, 1, len(s)-1)
            let len_s_m1 = self.ctx.terms.mk_sub(vec![len_s, one]);
            let tail_s = self.ctx.terms.mk_app(
                Symbol::named("seq.extract"),
                vec![s, one, len_s_m1],
                seq_sort.clone(),
            );
            let tail_and_right = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![tail_s, sk_right],
                seq_sort.clone(),
            );
            let contains_suffix = self.ctx.terms.mk_app(
                Symbol::named("seq.contains"),
                vec![tail_and_right, s],
                z4_core::Sort::Bool,
            );
            let not_contains_suffix = self.ctx.terms.mk_not(contains_suffix);
            let ne3 = self.ctx.terms.mk_not(s_eq_empty);
            let guard3 = self.ctx.terms.mk_and(vec![contains, ne3]);
            axioms.push(self.ctx.terms.mk_implies(guard3, not_contains_suffix));

            // Register the synthesized contains for axiom generation.
            new_contains_terms.push((contains_suffix, tail_and_right, s));

            // Axiom 5: i >= -1
            axioms.push(self.ctx.terms.mk_ge(lidx_term, neg_one));

            // Axiom 6: i <= len(t)
            let i_le_len = self.ctx.terms.mk_le(lidx_term, len_t);
            axioms.push(i_le_len);

            // Length non-negativity
            axioms.push(self.ctx.terms.mk_ge(len_t, zero));
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));

            // Skolem length non-negativity
            let len_right = self.mk_seq_len(sk_right);
            axioms.push(self.ctx.terms.mk_ge(len_left, zero));
            axioms.push(self.ctx.terms.mk_ge(len_right, zero));
        }

        (axioms, new_contains_terms)
    }
}
