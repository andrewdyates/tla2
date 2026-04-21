// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Core seq axiom collection and len/nth axiom generation.

use num_bigint::BigInt;
use num_traits::Zero;

use super::super::super::Executor;
use super::scan::SeqTermScan;
use z4_core::term::{Constant, Symbol, TermData, TermId};

impl Executor {
    /// Collect all Seq axioms from assertion terms (#5958, #5841, #6005).
    ///
    /// Generates axioms for: len, nth, contains, extract, prefixof, suffixof,
    /// indexof, replace.
    ///
    /// Uses a two-pass approach (#6005): after the first round of axiom
    /// generation, scans the generated axioms for new seq operations that
    /// weren't in the original assertions. If any are found, generates
    /// additional axioms for them. This handles the case where axiom generators
    /// synthesize seq terms (e.g., indexof creates `seq.extract` and
    /// `seq.contains` terms) that themselves need axiomatization.
    ///
    /// Capped at 2 passes to bound axiom growth. In practice, the second pass
    /// rarely finds new operations because generators already inline axioms
    /// for their synthesized terms.
    pub(super) fn collect_seq_len_axioms(&mut self) -> Vec<TermId> {
        // Inject nth-ground equalities into assertions before scanning (#6036).
        // This makes ALL axiom generators benefit from nth reconstruction.
        let nth_equalities = self.generate_nth_ground_equality_axioms();
        if !nth_equalities.is_empty() {
            let mut seen: hashbrown::HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                nth_equalities
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        let mut scan = self.scan_seq_terms();
        let mut axioms = self.generate_axioms_from_scan(&scan);

        // Second pass: scan generated axioms for new seq operations (#6005).
        // Capped at one extra pass to bound axiom growth. The bridge axiom
        // (contains <=> indexof) creates new terms that get axiomatized here.
        // Snapshot before scanning so we only axiomatize NEW terms — avoids
        // duplicate Skolem variables from re-processing first-pass terms.
        let offsets = scan.snapshot();
        scan.scan_roots(&self.ctx.terms, &axioms);
        let new_op_count = scan.axiom_op_count();
        let prev_op_count = offsets.contains
            + offsets.extract
            + offsets.prefixof
            + offsets.suffixof
            + offsets.indexof
            + offsets.last_indexof
            + offsets.replace;

        if new_op_count > prev_op_count {
            // Generate axioms ONLY for terms discovered in the second scan.
            let new_terms = scan.new_terms_since(&offsets);
            let extra = self.generate_axioms_from_scan(&new_terms);
            axioms.extend(extra);
        }
        // Not `else if` — also handle new nth terms even when new ops were found.
        // The previous `else if` skipped nth depth-iteration when both new ops
        // and new nth terms appeared simultaneously.
        if scan.nth_terms.len() > offsets.nth {
            let new_terms = scan.new_terms_since(&offsets);
            let nth_axioms = self.generate_seq_nth_axioms(&new_terms);
            axioms.extend(nth_axioms);
            for _nth_pass in 0..5 {
                let prev = scan.nth_terms.len();
                scan.scan_roots(&self.ctx.terms, &axioms);
                if scan.nth_terms.len() == prev {
                    break;
                }
                let extra_nth = self.generate_seq_nth_axioms(&scan);
                if extra_nth.is_empty() {
                    break;
                }
                axioms.extend(extra_nth);
            }
        }

        axioms
    }

    /// Generate all seq axioms from a completed scan.
    ///
    /// Ordering: indexof and replace run before contains because they create
    /// fresh `contains(s,t)` terms that need their own axioms (#5998).
    pub(super) fn generate_axioms_from_scan(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = self.generate_seq_len_axioms(scan);
        axioms.extend(self.generate_seq_nth_axioms(scan));
        axioms.extend(self.generate_seq_extract_axioms(scan));
        axioms.extend(self.generate_seq_prefixof_axioms(scan));
        axioms.extend(self.generate_seq_suffixof_axioms(scan));

        let mut new_contains = Vec::new();
        let (indexof_axioms, idx_contains) = self.generate_seq_indexof_axioms(scan);
        axioms.extend(indexof_axioms);
        new_contains.extend(idx_contains);
        let (last_idx_axioms, lidx_contains) = self.generate_seq_last_indexof_axioms(scan);
        axioms.extend(last_idx_axioms);
        new_contains.extend(lidx_contains);
        let (replace_axioms, rpl_contains) = self.generate_seq_replace_axioms(scan);
        axioms.extend(replace_axioms);
        new_contains.extend(rpl_contains);

        axioms.extend(self.generate_seq_contains_axioms(scan));
        if !new_contains.is_empty() {
            axioms.extend(self.generate_seq_contains_axioms_for(&new_contains));
        }
        axioms
    }

    /// Collect only `seq.nth` structural axioms (for non-LIA path, #5841).
    pub(super) fn collect_seq_nth_axioms(&mut self) -> Vec<TermId> {
        let scan = self.scan_seq_terms();
        self.generate_seq_nth_axioms(&scan)
    }

    /// Check whether assertions contain axiom-generating Seq operations (#5841).
    ///
    /// These operations (contains, extract, prefixof, suffixof, indexof) generate
    /// length constraints that require LIA routing.
    pub(super) fn assertions_contain_axiom_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = hashbrown::HashSet::new();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if matches!(
                        name.as_str(),
                        "seq.contains"
                            | "seq.extract"
                            | "seq.prefixof"
                            | "seq.suffixof"
                            | "seq.indexof"
                            | "seq.last_indexof"
                            | "seq.replace"
                    ) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// Scan assertions for seq-typed terms (read-only pass over the term DAG).
    pub(super) fn scan_seq_terms(&self) -> SeqTermScan {
        let mut scan = SeqTermScan::new();
        scan.scan_roots(&self.ctx.terms, &self.ctx.assertions);
        scan
    }

    /// Generate length axiom terms from collected seq structure terms.
    pub(super) fn generate_seq_len_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let mut seen_len_args: hashbrown::HashSet<TermId> =
            scan.len_terms.iter().map(|&(_, inner)| inner).collect();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let one = self.ctx.terms.mk_int(BigInt::from(1));

        // Axiom 1: seq.len(s) >= 0 for each seq.len term
        for &(len_term, _) in &scan.len_terms {
            axioms.push(self.ctx.terms.mk_ge(len_term, zero));
        }

        // Axiom 2: seq.len(seq.unit(x)) = 1
        for &unit_term in &scan.unit_terms {
            let len = self.mk_seq_len(unit_term);
            axioms.push(self.ctx.terms.mk_eq(len, one));
            if seen_len_args.insert(unit_term) {
                axioms.push(self.ctx.terms.mk_ge(len, zero));
            }
        }

        // Axiom 3: seq.len(seq.empty) = 0
        for &empty_term in &scan.empty_terms {
            let len = self.mk_seq_len(empty_term);
            axioms.push(self.ctx.terms.mk_eq(len, zero));
        }
        // Bridge explicit String `seq.empty` terms from user assertions to the
        // canonical empty-string term used by internally generated axioms (#6342).
        for &empty_term in &scan.empty_terms {
            let sort = self.ctx.terms.sort(empty_term).clone();
            if sort == z4_core::Sort::String {
                let canonical = self.mk_seq_empty(&sort);
                if empty_term != canonical {
                    axioms.push(self.ctx.terms.mk_eq(empty_term, canonical));
                }
            }
        }

        // Axiom 4: seq.len(seq.++(a, b)) = seq.len(a) + seq.len(b)
        for (concat_term, args) in &scan.concat_terms {
            let concat_len = self.mk_seq_len(*concat_term);
            let arg_lens: Vec<TermId> = args.iter().map(|&a| self.mk_seq_len(a)).collect();
            let sum = self.ctx.terms.mk_add(arg_lens.clone());
            axioms.push(self.ctx.terms.mk_eq(concat_len, sum));
            for len in arg_lens {
                axioms.push(self.ctx.terms.mk_ge(len, zero));
            }
        }

        axioms
    }

    /// Generate `seq.nth` axioms from collected terms (#5841).
    ///
    /// Axiom 5: `seq.nth(seq.unit(x), 0) = x` — element extraction from unit sequence.
    /// Axiom 6: `seq.nth(seq.++(a, b), i) = ite(i < len(a), nth(a, i), nth(b, i - len(a)))`
    ///
    /// Concat decomposition creates new nth terms that may themselves need the
    /// unit axiom, so we process in two passes.
    pub(super) fn generate_seq_nth_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        // New nth terms created by concat decomposition that need unit-axiom check.
        let mut derived_nth: Vec<(TermId, TermId, TermId)> = Vec::new();

        for &(nth_term, seq_arg, idx_arg) in &scan.nth_terms {
            match self.ctx.terms.get(seq_arg) {
                TermData::App(Symbol::Named(name), args)
                    if name == "seq.unit" && args.len() == 1 =>
                {
                    let element = args[0];
                    // Axiom 5: seq.nth(seq.unit(x), 0) = x (index must be 0).
                    let is_zero_idx = idx_arg == zero
                        || matches!(
                            self.ctx.terms.get(idx_arg),
                            TermData::Const(Constant::Int(ref v)) if v.is_zero()
                        );
                    if is_zero_idx {
                        axioms.push(self.ctx.terms.mk_eq(nth_term, element));
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "seq.++" && args.len() == 2 => {
                    let left = args[0];
                    let right = args[1];
                    let elem_sort = self.ctx.terms.sort(nth_term).clone();

                    // Axiom 6: seq.nth(seq.++(a, b), i) =
                    //   ite(i < seq.len(a), seq.nth(a, i), seq.nth(b, i - seq.len(a)))
                    let len_a = self.mk_seq_len(left);
                    let nth_left = self.ctx.terms.mk_app(
                        Symbol::named("seq.nth"),
                        vec![left, idx_arg],
                        elem_sort.clone(),
                    );
                    let idx_offset = self.ctx.terms.mk_sub(vec![idx_arg, len_a]);
                    let nth_right = self.ctx.terms.mk_app(
                        Symbol::named("seq.nth"),
                        vec![right, idx_offset],
                        elem_sort,
                    );
                    let cond = self.ctx.terms.mk_lt(idx_arg, len_a);
                    let ite_term = self.ctx.terms.mk_ite(cond, nth_left, nth_right);
                    axioms.push(self.ctx.terms.mk_eq(nth_term, ite_term));

                    // Also inject len(a) >= 0 if not already present.
                    axioms.push(self.ctx.terms.mk_ge(len_a, zero));

                    // Track derived nth terms for second-pass axiomatization.
                    derived_nth.push((nth_left, left, idx_arg));
                    derived_nth.push((nth_right, right, idx_offset));
                }
                _ => {}
            }
        }

        // Second pass: apply unit axiom to nth terms created by concat decomposition.
        // For derived terms, the index may be a symbolic expression (e.g., i - len(a))
        // that equals 0 only after LIA reasoning. We inject:
        //   1. nth(seq.unit(x), 0) = x  (canonical zero-index axiom)
        //   2. idx = 0  => nth(seq.unit(x), idx) = nth(seq.unit(x), 0)
        //      (via EUF congruence once LIA proves idx = 0)
        // Approach: inject the canonical axiom + equality bridge so the
        // Nelson-Oppen combination of LIA and EUF can chain the reasoning.
        for (nth_term, seq_arg, idx_arg) in derived_nth {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(seq_arg) {
                if name == "seq.unit" && args.len() == 1 {
                    let element = args[0];
                    let is_zero_idx = idx_arg == zero
                        || matches!(
                            self.ctx.terms.get(idx_arg),
                            TermData::Const(Constant::Int(ref v)) if v.is_zero()
                        );
                    if is_zero_idx {
                        // Statically zero — unconditional axiom.
                        axioms.push(self.ctx.terms.mk_eq(nth_term, element));
                    } else {
                        // Symbolic index: create canonical nth(unit(x), 0) = x axiom
                        // and assert idx = 0 => nth_term = nth_at_zero (via implication).
                        let elem_sort = self.ctx.terms.sort(nth_term).clone();
                        let nth_at_zero = self.ctx.terms.mk_app(
                            Symbol::named("seq.nth"),
                            vec![seq_arg, zero],
                            elem_sort,
                        );
                        // Axiom: nth(unit(x), 0) = x
                        axioms.push(self.ctx.terms.mk_eq(nth_at_zero, element));
                        // Bridge: idx = 0 => nth_term = nth_at_zero
                        // (EUF congruence: if idx = 0, then nth(s, idx) = nth(s, 0))
                        let idx_eq_zero = self.ctx.terms.mk_eq(idx_arg, zero);
                        let nth_eq_canonical = self.ctx.terms.mk_eq(nth_term, nth_at_zero);
                        axioms.push(self.ctx.terms.mk_implies(idx_eq_zero, nth_eq_canonical));
                    }
                }
            }
        }

        axioms
    }
}
