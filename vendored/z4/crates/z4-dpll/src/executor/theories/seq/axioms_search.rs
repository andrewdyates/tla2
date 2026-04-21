// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Search-family seq axiom generation: contains, extract, prefixof, suffixof.
//!
//! Index-finding and replacement operations (indexof, last_indexof, replace)
//! are in the sibling `axioms_indexof` module.

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use super::super::super::Executor;
use super::scan::SeqTermScan;
use z4_core::term::{Constant, Symbol, TermData, TermId};

impl Executor {
    /// Generate `seq.contains` axioms (#5841, #6024).
    ///
    /// For each `seq.contains(s, t)` term `c`:
    /// - Ground: when s and t resolve to concrete sequences, force c = true/false
    /// - Positive: `c => s = sk_left ++ t ++ sk_right`  (Z3: theory_seq.cpp:3104)
    /// - Positive: `c => len(sk_left) >= 0 AND len(sk_right) >= 0`
    /// - Length: `c => len(s) >= len(t)`
    ///
    /// The ground evaluation (#6024) prevents false-SAT on concrete sequences by
    /// directly evaluating containment when both s and t are ground (composed of
    /// seq.unit/seq.++/seq.empty over constants). This mirrors Z3's `canonizes`
    /// mechanism. For symbolic sequences, !contains incompleteness remains (no
    /// axiom can force contains = true without concrete evaluation).
    pub(super) fn generate_seq_contains_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());

        // Build ground-sequence map from equality assertions for concrete evaluation (#6024).
        let ground_map = self.build_ground_seq_map();

        for &(contains_term, s, t) in &scan.contains_terms {
            let seq_sort = self.ctx.terms.sort(s).clone();

            // === Ground evaluation (#6024): if both s and t resolve to concrete ===
            // sequences (via equality assertions), evaluate contains directly.
            // This prevents false-SAT when asserting !contains on concrete sequences.
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                if self.ground_seq_contains(&s_elems, &t_elems) {
                    axioms.push(contains_term); // Force contains = true
                } else {
                    let not_c = self.ctx.terms.mk_not(contains_term);
                    axioms.push(not_c); // Force contains = false
                }
            }

            // Skolem witnesses: sk_left, sk_right such that
            // contains(s, t) => s = sk_left ++ t ++ sk_right
            let sk_left = self.ctx.terms.mk_fresh_var("seq.cnt.l", seq_sort.clone());
            let sk_right = self.ctx.terms.mk_fresh_var("seq.cnt.r", seq_sort.clone());

            // s = sk_left ++ t ++ sk_right
            let inner_concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![t, sk_right], seq_sort.clone());
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_left, inner_concat],
                seq_sort,
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);

            // contains(s, t) => decomposition
            axioms.push(self.ctx.terms.mk_implies(contains_term, decomp));

            // contains(s, t) => len(sk_left) >= 0
            let len_left = self.mk_seq_len(sk_left);
            let ge_left = self.ctx.terms.mk_ge(len_left, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_left));

            // contains(s, t) => len(sk_right) >= 0
            let len_right = self.mk_seq_len(sk_right);
            let ge_right = self.ctx.terms.mk_ge(len_right, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_right));

            // contains(s, t) => len(s) >= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let ge_len = self.ctx.terms.mk_ge(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_len));
        }

        axioms
    }

    /// Generate `seq.extract` axioms (#5841).
    ///
    /// For each `seq.extract(s, i, n)` term `e`:
    /// - `0 <= i AND i <= len(s) AND n >= 0 => s = sk_pre ++ e ++ sk_post`
    /// - `0 <= i AND i <= len(s) => len(sk_pre) = i`
    /// - `0 <= i AND i <= len(s) AND n >= 0 AND len(s) >= n + i => len(e) = n`
    /// - `0 <= i AND i <= len(s) AND n >= 0 AND len(s) < n + i => len(e) = len(s) - i`
    /// - `i < 0 OR i >= len(s) OR n <= 0 => e = seq.empty`
    ///
    /// Reference: Z3 seq_axioms.cpp:196-263
    pub(super) fn generate_seq_extract_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();

        for &(extract_term, s, i, n) in &scan.extract_terms {
            // Ground evaluation (#6040): when s is ground and i, n are constants,
            // compute the extraction result directly and force it.
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            if let Some(s_elems) = self.try_extract_ground_seq(s_ground) {
                if let (
                    TermData::Const(Constant::Int(i_val)),
                    TermData::Const(Constant::Int(n_val)),
                ) = (self.ctx.terms.get(i), self.ctx.terms.get(n))
                {
                    if let (Some(i_usize), Some(n_usize)) = (i_val.to_usize(), n_val.to_usize()) {
                        let seq_sort = self.ctx.terms.sort(s).clone();
                        let result_elems: Vec<TermId> = if i_usize < s_elems.len() && n_usize > 0 {
                            let end = (i_usize + n_usize).min(s_elems.len());
                            s_elems[i_usize..end].to_vec()
                        } else {
                            vec![] // out of bounds or n=0 → empty
                        };
                        // Force ground result via len + nth element equalities.
                        // Structural synthesis (seq.++ chains) doesn't work because
                        // the EUF solver lacks injectivity for seq.++. Instead, emit:
                        //   len(extract_term) = |result|
                        //   nth(extract_term, 0) = c0, nth(extract_term, 1) = c1, ...
                        // This lets the solver derive contradictions element-wise.
                        if result_elems.is_empty() {
                            let empty = self.mk_seq_empty(&seq_sort);
                            axioms.push(self.ctx.terms.mk_eq(extract_term, empty));
                            // Force len = 0 so arithmetic on len(extract) resolves.
                            let len_e = self.mk_seq_len(extract_term);
                            axioms.push(self.ctx.terms.mk_eq(len_e, zero));
                        } else if result_elems.len() == 1 {
                            // Single element: seq.unit is injective, so direct
                            // equality works: extract_term = seq.unit(c).
                            axioms.push(self.ctx.terms.mk_eq(extract_term, result_elems[0]));
                        } else {
                            // Multi-element: len + nth + concat nth materialization (#6040).
                            let elem_sort = seq_sort
                                .seq_element()
                                .cloned()
                                .unwrap_or(z4_core::Sort::Int);
                            let n_elems = result_elems.len();
                            let len_e = self.mk_seq_len(extract_term);
                            let n_int = self.ctx.terms.mk_int(BigInt::from(n_elems));
                            axioms.push(self.ctx.terms.mk_eq(len_e, n_int));
                            for (k, elem) in result_elems.iter().enumerate() {
                                let inner_c = match self.ctx.terms.get(*elem) {
                                    TermData::App(Symbol::Named(name), args)
                                        if name == "seq.unit" && args.len() == 1 =>
                                    {
                                        args[0]
                                    }
                                    _ => continue,
                                };
                                let idx = self.ctx.terms.mk_int(BigInt::from(k));
                                let nth_e = self.ctx.terms.mk_app(
                                    Symbol::named("seq.nth"),
                                    vec![extract_term, idx],
                                    elem_sort.clone(),
                                );
                                axioms.push(self.ctx.terms.mk_eq(nth_e, inner_c));
                            }
                            for &(concat_term, _) in &scan.concat_terms {
                                if self.ctx.terms.sort(concat_term) != &seq_sort {
                                    continue;
                                }
                                let eq_cond = self.ctx.terms.mk_eq(extract_term, concat_term);
                                for k in 0..n_elems {
                                    let idx = self.ctx.terms.mk_int(BigInt::from(k));
                                    let nth_e = self.ctx.terms.mk_app(
                                        Symbol::named("seq.nth"),
                                        vec![extract_term, idx],
                                        elem_sort.clone(),
                                    );
                                    let nth_c = self.ctx.terms.mk_app(
                                        Symbol::named("seq.nth"),
                                        vec![concat_term, idx],
                                        elem_sort.clone(),
                                    );
                                    let nth_eq = self.ctx.terms.mk_eq(nth_e, nth_c);
                                    axioms.push(self.ctx.terms.mk_implies(eq_cond, nth_eq));
                                }
                            }
                        }
                        // Ground evaluation complete; skip skolem decomposition.
                        continue;
                    }
                }
            }
            let seq_sort = self.ctx.terms.sort(s).clone();
            let len_s = self.mk_seq_len(s);
            let len_e = self.mk_seq_len(extract_term);

            // Skolems: sk_pre (prefix of length i), sk_post (suffix after extract)
            let sk_pre = self.ctx.terms.mk_fresh_var("seq.pre", seq_sort.clone());
            let sk_post = self.ctx.terms.mk_fresh_var("seq.post", seq_sort.clone());

            // Precondition: 0 <= i AND i <= len(s) AND n >= 0
            let i_ge_0 = self.ctx.terms.mk_ge(i, zero);
            let i_le_len = self.ctx.terms.mk_le(i, len_s);
            let n_ge_0 = self.ctx.terms.mk_ge(n, zero);
            let valid_cond = self.ctx.terms.mk_and(vec![i_ge_0, i_le_len, n_ge_0]);

            // s = sk_pre ++ e ++ sk_post
            let inner_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![extract_term, sk_post],
                seq_sort.clone(),
            );
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_pre, inner_concat],
                seq_sort.clone(),
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);
            axioms.push(self.ctx.terms.mk_implies(valid_cond, decomp));

            // len(sk_pre) = i  (when valid)
            let len_pre = self.mk_seq_len(sk_pre);
            let iv_ge = self.ctx.terms.mk_ge(i, zero);
            let iv_le = self.ctx.terms.mk_le(i, len_s);
            let i_valid = self.ctx.terms.mk_and(vec![iv_ge, iv_le]);
            let eq_pre_i = self.ctx.terms.mk_eq(len_pre, i);
            axioms.push(self.ctx.terms.mk_implies(i_valid, eq_pre_i));

            // len(e): exact or clamped
            // Case A: len(s) >= n + i => len(e) = n
            let n_plus_i = self.ctx.terms.mk_add(vec![n, i]);
            let ea_ge_i = self.ctx.terms.mk_ge(i, zero);
            let ea_le_i = self.ctx.terms.mk_le(i, len_s);
            let ea_ge_n = self.ctx.terms.mk_ge(n, zero);
            let ea_ge_s = self.ctx.terms.mk_ge(len_s, n_plus_i);
            let exact_cond = self
                .ctx
                .terms
                .mk_and(vec![ea_ge_i, ea_le_i, ea_ge_n, ea_ge_s]);
            let eq_len_n = self.ctx.terms.mk_eq(len_e, n);
            axioms.push(self.ctx.terms.mk_implies(exact_cond, eq_len_n));

            // Case B: len(s) < n + i => len(e) = len(s) - i
            let cb_ge_i = self.ctx.terms.mk_ge(i, zero);
            let cb_le_i = self.ctx.terms.mk_le(i, len_s);
            let cb_ge_n = self.ctx.terms.mk_ge(n, zero);
            let cb_lt_s = self.ctx.terms.mk_lt(len_s, n_plus_i);
            let clamped_cond = self
                .ctx
                .terms
                .mk_and(vec![cb_ge_i, cb_le_i, cb_ge_n, cb_lt_s]);
            let len_s_minus_i = self.ctx.terms.mk_sub(vec![len_s, i]);
            let eq_clamped = self.ctx.terms.mk_eq(len_e, len_s_minus_i);
            axioms.push(self.ctx.terms.mk_implies(clamped_cond, eq_clamped));

            // Out-of-bounds: i < 0 OR i > len(s) OR n <= 0 => e = seq.empty
            let empty = self.mk_seq_empty(&seq_sort);
            let oob_a = self.ctx.terms.mk_lt(i, zero);
            let oob_b = self.ctx.terms.mk_gt(i, len_s);
            let oob_c = self.ctx.terms.mk_le(n, zero);
            let oob = self.ctx.terms.mk_or(vec![oob_a, oob_b, oob_c]);
            let eq_empty = self.ctx.terms.mk_eq(extract_term, empty);
            axioms.push(self.ctx.terms.mk_implies(oob, eq_empty));

            // Inject len(empty) = 0 so OOB reasoning chains correctly.
            // The scan may not have seen this empty term since we just created it.
            let len_empty = self.mk_seq_len(empty);
            axioms.push(self.ctx.terms.mk_eq(len_empty, zero));

            // Non-negativity constraints for generated len terms
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_e, zero));
            axioms.push(self.ctx.terms.mk_ge(len_pre, zero));
        }

        axioms
    }

    /// Generate `seq.prefixof` axioms (#5841).
    ///
    /// For each `seq.prefixof(s, t)` term `p`:
    /// - Positive: `p => t = s ++ sk_suffix`  (Z3: theory_seq.cpp:3070)
    /// - Positive: `p => len(sk_suffix) >= 0`
    /// - Basic: `p => len(s) <= len(t)`
    ///
    /// Reference: Z3 theory_seq.cpp:3065-3078
    pub(super) fn generate_seq_prefixof_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();

        for &(prefix_term, s, t) in &scan.prefixof_terms {
            let seq_sort = self.ctx.terms.sort(t).clone();

            // Skolem: sk_suffix such that prefixof(s, t) => t = s ++ sk_suffix
            let sk_suffix = self
                .ctx
                .terms
                .mk_fresh_var("seq.p.suffix", seq_sort.clone());

            // t = s ++ sk_suffix
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![s, sk_suffix], seq_sort);
            let decomp = self.ctx.terms.mk_eq(t, concat);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, decomp));

            // len(sk_suffix) >= 0
            let len_suffix = self.mk_seq_len(sk_suffix);
            let ge_suffix = self.ctx.terms.mk_ge(len_suffix, zero);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, ge_suffix));

            // prefixof(s, t) => len(s) <= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let le_s_t = self.ctx.terms.mk_le(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, le_s_t));

            // Non-negativity
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_t, zero));

            // Completeness (#6035): ground evaluation for prefixof.
            //
            // When both s and t resolve to concrete sequences (via equality
            // assertions or nth reconstruction), evaluate prefixof directly.
            // Forces prefixof = true/false accordingly, preventing false-SAT
            // on NOT prefixof when s IS demonstrably a prefix.
            //
            // Previous extract-based approach (#6024) caused false-UNSAT (#6033).
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                let is_prefix = s_elems.len() <= t_elems.len()
                    && s_elems
                        .iter()
                        .zip(t_elems.iter())
                        .all(|(&se, &te)| self.ground_seq_elem_eq(se, te));
                if is_prefix {
                    axioms.push(prefix_term); // Force prefixof = true
                } else {
                    let not_p = self.ctx.terms.mk_not(prefix_term);
                    axioms.push(not_p); // Force prefixof = false
                }
            }
        }

        axioms
    }

    /// Generate `seq.suffixof` axioms (#5841).
    ///
    /// For each `seq.suffixof(s, t)` term `p`:
    /// - Positive: `p => t = sk_prefix ++ s`  (Z3: theory_seq.cpp:3085)
    /// - Positive: `p => len(sk_prefix) >= 0`
    /// - Basic: `p => len(s) <= len(t)`
    ///
    /// Reference: Z3 theory_seq.cpp:3080-3089
    pub(super) fn generate_seq_suffixof_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();

        for &(suffix_term, s, t) in &scan.suffixof_terms {
            let seq_sort = self.ctx.terms.sort(t).clone();

            // Skolem: sk_prefix such that suffixof(s, t) => t = sk_prefix ++ s
            let sk_prefix = self
                .ctx
                .terms
                .mk_fresh_var("seq.s.prefix", seq_sort.clone());

            // t = sk_prefix ++ s
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![sk_prefix, s], seq_sort);
            let decomp = self.ctx.terms.mk_eq(t, concat);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, decomp));

            // len(sk_prefix) >= 0
            let len_prefix = self.mk_seq_len(sk_prefix);
            let ge_prefix = self.ctx.terms.mk_ge(len_prefix, zero);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, ge_prefix));

            // suffixof(s, t) => len(s) <= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let le_s_t = self.ctx.terms.mk_le(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, le_s_t));

            // Non-negativity
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_t, zero));

            // Completeness (#6035): ground evaluation for suffixof.
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                let is_suffix = s_elems.len() <= t_elems.len()
                    && s_elems
                        .iter()
                        .rev()
                        .zip(t_elems.iter().rev())
                        .all(|(&se, &te)| self.ground_seq_elem_eq(se, te));
                if is_suffix {
                    axioms.push(suffix_term); // Force suffixof = true
                } else {
                    let not_s = self.ctx.terms.mk_not(suffix_term);
                    axioms.push(not_s); // Force suffixof = false
                }
            }
        }

        axioms
    }

    /// Generate contains axioms for a list of `(contains_term, s, t)` tuples.
    ///
    /// Used for synthesized contains terms (e.g. from indexof) that are not
    /// in the original assertion scan (#5998).
    pub(super) fn generate_seq_contains_axioms_for(
        &mut self,
        terms: &[(TermId, TermId, TermId)],
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());

        for &(contains_term, s, t) in terms {
            let seq_sort = self.ctx.terms.sort(s).clone();

            let sk_left = self.ctx.terms.mk_fresh_var("seq.cnt.l", seq_sort.clone());
            let sk_right = self.ctx.terms.mk_fresh_var("seq.cnt.r", seq_sort.clone());

            let inner_concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![t, sk_right], seq_sort.clone());
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_left, inner_concat],
                seq_sort,
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);
            axioms.push(self.ctx.terms.mk_implies(contains_term, decomp));

            let len_left = self.mk_seq_len(sk_left);
            let ge_left = self.ctx.terms.mk_ge(len_left, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_left));

            let len_right = self.mk_seq_len(sk_right);
            let ge_right = self.ctx.terms.mk_ge(len_right, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_right));

            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let ge_len = self.ctx.terms.mk_ge(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_len));
        }

        axioms
    }
}
