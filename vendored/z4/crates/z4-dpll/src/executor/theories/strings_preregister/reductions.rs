// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function reduction pre-registration for string theory.
//!
//! Emits CVC5-style reduction lemmas for `str.substr`, `str.replace`, and
//! `str.at` before the DPLL(T) solve loop.

use num_bigint::BigInt;
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, TermId};

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::super::strings_eval::ground_eval_string_term;

impl Executor {
    /// Pre-register CVC5-style reduction lemmas for extended string functions.
    ///
    /// For `str.substr(s, n, m)`:
    ///   IF n >= 0 AND len(s) > n AND m > 0
    ///   THEN s = sk_pre ++ skt ++ sk_suf AND
    ///        len(sk_pre) = n AND
    ///        (len(sk_suf) = len(s) - (n+m) OR len(sk_suf) = 0) AND
    ///        len(skt) <= m
    ///   ELSE skt = ""
    ///   AND substr(s, n, m) = skt
    ///
    /// For `str.replace(x, y, z)`:
    ///   IF y = ""
    ///   THEN rpw = str.++(z, x)
    ///   ELIF contains(x, y)
    ///   THEN x = str.++(rp1, y, rp2) AND
    ///        rpw = str.++(rp1, z, rp2) AND
    ///        NOT contains(str.++(rp1, substr(y, 0, len(y)-1)), y)
    ///   ELSE rpw = x
    ///   AND replace(x, y, z) = rpw
    ///
    /// Reference: CVC5 `theory_strings_preprocess.cpp:62-121` (substr),
    ///            CVC5 `theory_strings_preprocess.cpp:572-631` (replace),
    ///            CVC5 `theory_strings_preprocess.cpp:527-571` (str.at)
    pub(in crate::executor) fn preregister_extf_reductions(
        &mut self,
        assertions: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
        _decomposed_vars: &mut hashbrown::HashSet<TermId>,
        enable_substr_and_at: bool,
        enable_replace: bool,
    ) -> (Vec<TermId>, Vec<TermId>) {
        let mut reductions = Vec::new();
        let mut reduced_term_ids = Vec::new();
        let _seen_reduced_terms: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        let mut seen: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        let mut input_contains_terms: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        // Track haystack variables that receive a replace decomposition
        // (case 2: x = rp1 ++ y ++ rp2). These must be passed to the second
        // contains-decomposition pass to prevent double decomposition (#4057).
        let _replace_decomposed_haystacks: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();

        // DFS scan for str.substr, str.replace, and str.at terms.
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        let mut substr_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new(); // (substr_term, s, n, m)
        let mut replace_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new(); // (replace_term, x, y, z)
        let mut at_terms: Vec<(TermId, TermId, TermId)> = Vec::new(); // (at_term, s, n)

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.contains" && args.len() == 2 {
                        input_contains_terms.insert(term);
                    }
                    if enable_substr_and_at
                        && name == "str.substr"
                        && args.len() == 3
                        && seen.insert(term)
                    {
                        // Skip fully-ground substr — Wave 0 handles those via
                        // ground_eval_string_term.
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        let constant_bounds = matches!(
                            self.ctx.terms.get(args[1]),
                            TermData::Const(Constant::Int(_))
                        ) && matches!(
                            self.ctx.terms.get(args[2]),
                            TermData::Const(Constant::Int(_))
                        );
                        // Soundness guard for #4057: eager non-ground substr
                        // reduction on symbolic lengths (for example
                        // str.substr(c, 0, str.len(e))) introduces branch-local
                        // skolems that can over-constrain circular formulas.
                        // Keep eager preregistration only for syntactically
                        // constant bounds; the theory-side extf evaluation can
                        // still reduce the deferred cases later once values
                        // become concrete.
                        if !is_ground && constant_bounds {
                            substr_terms.push((term, args[0], args[1], args[2]));
                        }
                    } else if enable_replace
                        && name == "str.replace"
                        && args.len() == 3
                        && seen.insert(term)
                    {
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            replace_terms.push((term, args[0], args[1], args[2]));
                        }
                    } else if enable_substr_and_at
                        && name == "str.at"
                        && args.len() == 2
                        && seen.insert(term)
                    {
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            at_terms.push((term, args[0], args[1]));
                        }
                    }
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    let binding_vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                    let body_id = *body;
                    for val in binding_vals {
                        stack.push(val);
                    }
                    stack.push(body_id);
                }
                _ => {}
            }
        }

        // Emit substr reduction lemmas.
        for (substr_term, s, n, m) in substr_terms {
            reduced_term_ids.push(substr_term);
            // Reuse canonical skolems per substr term.
            let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, substr_term);
            let skt = skolem_cache.substr_result(&mut self.ctx.terms, substr_term);
            let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, substr_term);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));

            // len(s)
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

            // Condition: n >= 0 AND len(s) > n AND m > 0
            let c1 = self.ctx.terms.mk_ge(n, zero);
            let c2 = self.ctx.terms.mk_gt(len_s, n);
            let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
            let c3 = self.ctx.terms.mk_gt(m, zero2);
            let cond = self.ctx.terms.mk_and(vec![c1, c2, c3]);

            // THEN branch:
            // b1: s = sk_pre ++ skt ++ sk_suf
            let concat = self.ctx.terms.mk_app(
                Symbol::named("str.++"),
                vec![sk_pre, skt, sk_suf],
                Sort::String,
            );
            // Internal concat introduced by eager substr reduction. Mark as
            // reduced so the string NF checker does not treat it as a primary
            // concat source and derive branch-local conflicts (#4057).
            reduced_term_ids.push(concat);
            let b11 = self.ctx.terms.mk_eq(s, concat);

            // NOTE: We do NOT mark the substr haystack in decomposed_vars here.
            // The global ExecutorSkolemCache ensures canonical skolems, so the
            // second-pass contains decomposition (from replace reductions) can
            // safely decompose this variable without creating competing equations.
            // Previously this blocked the #4057 fix path.

            // b2: len(sk_pre) = n
            let len_sk_pre =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk_pre], Sort::Int);
            let b12 = self.ctx.terms.mk_eq(len_sk_pre, n);

            // b3: len(sk_suf) = len(s) - (n+m) OR len(sk_suf) = 0
            let len_sk_suf =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk_suf], Sort::Int);
            let n_plus_m = self.ctx.terms.mk_add(vec![n, m]);
            let len_s2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let remainder = self.ctx.terms.mk_sub(vec![len_s2, n_plus_m]);
            let suf_eq_remainder = self.ctx.terms.mk_eq(len_sk_suf, remainder);
            let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
            let suf_eq_zero = self.ctx.terms.mk_eq(len_sk_suf, zero3);
            let b13 = self.ctx.terms.mk_or(vec![suf_eq_remainder, suf_eq_zero]);

            // b4: len(skt) <= m
            let len_skt = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
            let b14 = self.ctx.terms.mk_le(len_skt, m);

            let then_branch = self.ctx.terms.mk_and(vec![b11, b12, b13, b14]);

            // ELSE branch: skt = ""
            let empty = self.ctx.terms.mk_string(String::new());
            let else_branch = self.ctx.terms.mk_eq(skt, empty);

            // ITE(cond, then, else)
            let ite = self.ctx.terms.mk_ite(cond, then_branch, else_branch);
            reductions.push(ite);

            // Bridge: substr(s, n, m) = skt
            let bridge = self.ctx.terms.mk_eq(substr_term, skt);
            reductions.push(bridge);

            // Non-negativity for all skolem lengths.
            for &sk in &[sk_pre, skt, sk_suf] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));
            }

            // lengthPositive bridge for all skolems.
            for &sk in &[sk_pre, skt, sk_suf] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Emit replace reduction lemmas.
        for (replace_term, x, y, z) in replace_terms {
            reduced_term_ids.push(replace_term);
            // Reuse canonical skolems per replace term.
            let rpw = skolem_cache.replace_result(&mut self.ctx.terms, replace_term);
            let rp1 = skolem_cache.replace_pre(&mut self.ctx.terms, replace_term);
            let rp2 = skolem_cache.replace_suffix(&mut self.ctx.terms, replace_term);

            let empty = self.ctx.terms.mk_string(String::new());

            // Case 1: y = "" => rpw = str.++(z, x)
            let y_eq_empty = self.ctx.terms.mk_eq(y, empty);
            let concat_zx =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![z, x], Sort::String);
            // Internal concat introduced by eager replace reduction. Mark as
            // reduced to keep NF checks focused on user-level concat terms.
            reduced_term_ids.push(concat_zx);
            let rpw_eq_zx = self.ctx.terms.mk_eq(rpw, concat_zx);

            // Case 2: y != "" AND contains(x, y) =>
            //   x = rp1 ++ y ++ rp2 AND rpw = rp1 ++ z ++ rp2 AND
            //   NOT contains(rp1 ++ substr(y, 0, len(y)-1), y)
            let contains_xy =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);
            // `contains(x, y)` introduced by replace reduction is an internal
            // branch guard. If this atom was not present in the original
            // assertions, mark it reduced so core predicate evaluation does
            // not treat it as a user-level fact and generate spurious
            // conflicts from branch-local values (#4057).
            if !input_contains_terms.contains(&contains_xy) {
                reduced_term_ids.push(contains_xy);
            }
            let concat_decomp =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, y, rp2], Sort::String);
            reduced_term_ids.push(concat_decomp);
            let x_eq_decomp = self.ctx.terms.mk_eq(x, concat_decomp);

            // NOTE: We do NOT mark the replace haystack in decomposed_vars here.
            // The global ExecutorSkolemCache ensures canonical skolems, so the
            // second-pass contains decomposition can safely process contains(x, y)
            // from replace reductions without creating competing equations.

            let concat_result =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, z, rp2], Sort::String);
            reduced_term_ids.push(concat_result);
            let rpw_eq_result = self.ctx.terms.mk_eq(rpw, concat_result);

            // First-occurrence guard: NOT contains(rp1 ++ substr(y, 0, len(y)-1), y)
            let len_y = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let len_y_minus_1 = self.ctx.terms.mk_sub(vec![len_y, one]);
            let zero_rep = self.ctx.terms.mk_int(BigInt::from(0));
            let y_prefix = self.ctx.terms.mk_app(
                Symbol::named("str.substr"),
                vec![y, zero_rep, len_y_minus_1],
                Sort::String,
            );
            // Internal helper substr used only in the replace "first
            // occurrence" guard.
            reduced_term_ids.push(y_prefix);
            let rp1_y_prefix =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, y_prefix], Sort::String);
            reduced_term_ids.push(rp1_y_prefix);
            let contains_guard = self.ctx.terms.mk_app(
                Symbol::named("str.contains"),
                vec![rp1_y_prefix, y],
                Sort::Bool,
            );
            if !input_contains_terms.contains(&contains_guard) {
                reduced_term_ids.push(contains_guard);
            }
            let not_contains = self.ctx.terms.mk_not(contains_guard);
            let case2_body = self
                .ctx
                .terms
                .mk_and(vec![x_eq_decomp, rpw_eq_result, not_contains]);

            // Case 3: y != "" AND NOT contains(x, y) => rpw = x
            let rpw_eq_x = self.ctx.terms.mk_eq(rpw, x);

            // Build the three-way ITE:
            // IF y = "" THEN rpw = z ++ x
            // ELIF contains(x, y) THEN <case2_body>
            // ELSE rpw = x
            let inner_ite = self.ctx.terms.mk_ite(contains_xy, case2_body, rpw_eq_x);
            let outer_ite = self.ctx.terms.mk_ite(y_eq_empty, rpw_eq_zx, inner_ite);
            reductions.push(outer_ite);

            // Bridge: replace(x, y, z) = rpw
            let bridge = self.ctx.terms.mk_eq(replace_term, rpw);
            reductions.push(bridge);

            // Non-negativity + lengthPositive for skolems.
            for &sk in &[rpw, rp1, rp2] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));

                let len_sk2 = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk2, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Emit str.at reduction lemmas.
        // CVC5 reference: theory_strings_preprocess.cpp:527-571
        //
        // str.at(s, n) = skt where:
        //   IF n >= 0 AND n < len(s)
        //   THEN s = sk1 ++ unit(skt) ++ sk2 AND
        //        len(sk1) = n AND
        //        len(sk2) = len(s) - (n+1)
        //
        // skt is a unit-length string (or empty if out of bounds).
        for (at_term, s, n) in at_terms {
            reduced_term_ids.push(at_term);

            let skt = self.ctx.terms.mk_fresh_var("sk_at_res", Sort::String);
            let sk1 = self.ctx.terms.mk_fresh_var("sk_at_pre", Sort::String);
            let sk2 = self.ctx.terms.mk_fresh_var("sk_at_suf", Sort::String);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let one = self.ctx.terms.mk_int(BigInt::from(1));

            // Condition: n >= 0 AND n < len(s)
            let c1 = self.ctx.terms.mk_ge(n, zero);
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let c2 = self.ctx.terms.mk_gt(len_s, n);
            let cond = self.ctx.terms.mk_and(vec![c1, c2]);

            // THEN branch:
            // s = sk1 ++ skt ++ sk2
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![sk1, skt, sk2], Sort::String);
            // Internal concat from eager str.at reduction. Mark as reduced so
            // the strings NF checker does not treat it as a primary concat
            // source and derive spurious conflicts (#4080).
            reduced_term_ids.push(concat);
            let b1 = self.ctx.terms.mk_eq(s, concat);

            // len(sk1) = n
            let len_sk1 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![sk1], Sort::Int);
            let b2 = self.ctx.terms.mk_eq(len_sk1, n);

            // len(sk2) = len(s) - (n+1)
            let len_sk2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![sk2], Sort::Int);
            let n_plus_1 = self.ctx.terms.mk_add(vec![n, one]);
            let len_s2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let remainder = self.ctx.terms.mk_sub(vec![len_s2, n_plus_1]);
            let b3 = self.ctx.terms.mk_eq(len_sk2, remainder);

            // len(skt) = 1 (unit length when in bounds)
            let len_skt = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
            let b4 = self.ctx.terms.mk_eq(len_skt, one);

            let then_branch = self.ctx.terms.mk_and(vec![b1, b2, b3, b4]);

            // cond => then_branch (implication, not ITE)
            // When out of bounds, skt is unconstrained per SMT-LIB semantics.
            let lemma = self.ctx.terms.mk_implies(cond, then_branch);
            reductions.push(lemma);

            // Bridge: str.at(s, n) = skt
            let bridge = self.ctx.terms.mk_eq(at_term, skt);
            reductions.push(bridge);

            // Non-negativity + lengthPositive for string skolems.
            for &sk in &[skt, sk1, sk2] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));

                let len_sk2_lp =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk2_lp, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        (reductions, reduced_term_ids)
    }
}
