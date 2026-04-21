// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen interface term evaluation and equality propagation.
//!
//! Contains the integer and real constant collection + evaluation loops
//! that discover interface equalities from arithmetic model values.
//!
//! Split from `mod.rs` for code health (#5970).

use num_bigint::BigInt;
use num_rational::BigRational;
use z4_core::term::{Constant, TermData};
use z4_core::{DiscoveredEquality, TermId, TermStore, TheoryLit};

use super::InterfaceBridge;
use super::InterfaceTrailEntry;
use super::{evaluate_arith_term_with_reasons, evaluate_real_arith_term_with_reasons};

impl InterfaceBridge {
    /// Collect integer constants from a term and register them.
    /// Uses a visited set to avoid exponential re-traversal of shared DAG subterms (#3712).
    pub(crate) fn collect_int_constants(&mut self, terms: &TermStore, term: TermId) {
        let mut visited = hashbrown::HashSet::new();
        self.collect_int_constants_inner(terms, term, &mut visited);
    }

    fn collect_int_constants_inner(
        &mut self,
        terms: &TermStore,
        term: TermId,
        visited: &mut hashbrown::HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                if !self.int_const_terms.contains_key(n) {
                    self.int_const_terms.insert(n.clone(), term);
                    self.interface_trail
                        .push(InterfaceTrailEntry::ConstTerm(n.clone()));
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_int_constants_inner(terms, arg, visited);
                }
            }
            TermData::Not(inner) => self.collect_int_constants_inner(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                self.collect_int_constants_inner(terms, *c, visited);
                self.collect_int_constants_inner(terms, *t, visited);
                self.collect_int_constants_inner(terms, *e, visited);
            }
            _ => {}
        }
    }

    /// Evaluate interface terms and return new equalities with reasons (#4068).
    ///
    /// The `get_int_value_with_reasons` closure returns both the integer value
    /// and the `TheoryLit` reasons (from LIA tight bounds) that fix a variable
    /// to that value. These reasons are collected across all variables in each
    /// arithmetic term so that receiving theories have complete proof provenance
    /// for conflict explanations.
    ///
    /// The caller is responsible for asserting the returned equalities into
    /// whichever sub-solvers need them (EUF, and optionally Strings).
    ///
    /// #6846: Equalities with empty reasons (free UF-valued variables) are
    /// returned as speculative pairs rather than asserted directly. The
    /// combined solver upgrades them to `NeedModelEquality` /
    /// `NeedModelEqualities` at fixpoint so the SAT layer can choose them
    /// explicitly instead of hard-wiring proofless equalities into EUF.
    pub(crate) fn evaluate_and_propagate(
        &mut self,
        terms: &TermStore,
        get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
        debug: bool,
        label: &str,
    ) -> (Vec<DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let mut arith_terms: Vec<TermId> = self.interface_arith_terms.iter().copied().collect();
        arith_terms.sort_unstable(); // Deterministic iteration order (#3041)
        if debug {
            for &t in &arith_terms {
                safe_eprintln!("[N-O {}] Interface term {:?}: {:?}", label, t, terms.get(t));
            }
        }
        let mut new_eqs = Vec::new();
        let mut speculative_pairs = Vec::new();
        for arith_term in arith_terms {
            let mut reasons = Vec::new();
            if let Some(value) = evaluate_arith_term_with_reasons(
                terms,
                get_int_value_with_reasons,
                arith_term,
                &mut reasons,
            ) {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Evaluated {:?} = {} ({} reasons)",
                        label,
                        arith_term,
                        value,
                        reasons.len()
                    );
                }
                if let Some(&const_term) = self.int_const_terms.get(&value) {
                    // Skip trivially-true self-equalities: a bare constant
                    // (e.g., `10`) can appear both as an interface arith term
                    // and in int_const_terms, yielding arith_term == const_term.
                    if arith_term == const_term {
                        continue;
                    }
                    // #6846: Free UF-valued equalities have no arithmetic
                    // provenance. Keep them speculative so the SAT layer can
                    // choose the equality instead of learning it
                    // unconditionally.
                    if reasons.is_empty() {
                        speculative_pairs.push((arith_term, const_term));
                        continue;
                    }
                    // Contradictory value guard: if this arith_term was
                    // previously propagated with a DIFFERENT const_term,
                    // the LIA model changed between N-O iterations. The old
                    // equality (e.g., sum=0) is already in EUF; propagating
                    // the new one (sum=10) would let EUF derive 0=10 →
                    // false-UNSAT. Skip to avoid the contradiction (#6846).
                    if let Some(&prev_const) = self.propagated_term_values.get(&arith_term) {
                        if prev_const != const_term {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] SKIP contradictory: {:?} was {:?} now {:?}",
                                    label,
                                    arith_term,
                                    prev_const,
                                    const_term
                                );
                            }
                            continue;
                        }
                    }
                    let pair = (arith_term, const_term);
                    if self.propagated_interface_eqs.insert(pair) {
                        self.interface_trail
                            .push(InterfaceTrailEntry::PropagatedEq(arith_term, const_term));
                        // Record the value for contradictory-change detection.
                        if self
                            .propagated_term_values
                            .insert(arith_term, const_term)
                            .is_none()
                        {
                            self.interface_trail
                                .push(InterfaceTrailEntry::PropagatedValue(arith_term));
                        }
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Interface term {:?} = {} (const {:?}, {} reasons)",
                                label,
                                arith_term,
                                value,
                                const_term,
                                reasons.len()
                            );
                        }
                        // Deduplicate reasons by term to keep conflict clauses minimal.
                        reasons.sort_by_key(|r| r.term);
                        reasons.dedup_by_key(|r| r.term);
                        new_eqs.push(DiscoveredEquality::new(arith_term, const_term, reasons));
                    }
                }
            }
        }
        // Postcondition (#4714):
        for eq in &new_eqs {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {label} evaluate_and_propagate returned self-equality ({:?} = {:?})",
                eq.lhs,
                eq.rhs
            );
        }
        (new_eqs, speculative_pairs)
    }

    /// Collect rational (Real) constants from a term and register them (#4915).
    /// Parallel to `collect_int_constants` but for Real-sorted constants.
    pub(crate) fn collect_real_constants(&mut self, terms: &TermStore, term: TermId) {
        let mut visited = hashbrown::HashSet::new();
        self.collect_real_constants_inner(terms, term, &mut visited);
    }

    fn collect_real_constants_inner(
        &mut self,
        terms: &TermStore,
        term: TermId,
        visited: &mut hashbrown::HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::Const(Constant::Rational(r)) => {
                if !self.real_const_terms.contains_key(&r.0) {
                    self.real_const_terms.insert(r.0.clone(), term);
                    self.interface_trail
                        .push(InterfaceTrailEntry::RealConstTerm(r.0.clone()));
                }
            }
            TermData::Const(Constant::Int(n)) => {
                // Integer constants can appear in Real-sorted expressions
                // (e.g., `(= x 2)` where x is Real is parsed as `(= x 2.0)`).
                let rational = BigRational::from(n.clone());
                if !self.real_const_terms.contains_key(&rational) {
                    self.real_const_terms.insert(rational.clone(), term);
                    self.interface_trail
                        .push(InterfaceTrailEntry::RealConstTerm(rational));
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_real_constants_inner(terms, arg, visited);
                }
            }
            TermData::Not(inner) => self.collect_real_constants_inner(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                self.collect_real_constants_inner(terms, *c, visited);
                self.collect_real_constants_inner(terms, *t, visited);
                self.collect_real_constants_inner(terms, *e, visited);
            }
            _ => {}
        }
    }

    /// Evaluate Real-valued interface terms and return new equalities (#4915).
    ///
    /// Parallel to `evaluate_and_propagate` but uses rational arithmetic.
    /// See `evaluate_and_propagate` docs for empty-reason handling (#6846).
    pub(crate) fn evaluate_and_propagate_real(
        &mut self,
        terms: &TermStore,
        get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
        debug: bool,
        label: &str,
    ) -> (Vec<DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let mut arith_terms: Vec<TermId> = self.interface_arith_terms.iter().copied().collect();
        arith_terms.sort_unstable(); // Deterministic iteration order (#3041)
        let mut new_eqs = Vec::new();
        let mut speculative_pairs = Vec::new();
        for arith_term in arith_terms {
            let mut reasons = Vec::new();
            if let Some(value) = evaluate_real_arith_term_with_reasons(
                terms,
                get_real_value_with_reasons,
                arith_term,
                &mut reasons,
            ) {
                if let Some(&const_term) = self.real_const_terms.get(&value) {
                    if arith_term == const_term {
                        continue;
                    }
                    // Filter out non-Boolean reason terms. NRA's McCormick
                    // refinement can produce bounds whose reasons reference
                    // bare Real/Int variables instead of Boolean assertion
                    // atoms. These can't map to SAT literals, causing partial
                    // conflict clauses dropped by soundness guard #3826.
                    reasons.retain(|r| {
                        (r.term.0 as usize) < terms.len()
                            && matches!(terms.sort(r.term), z4_core::Sort::Bool)
                    });
                    if reasons.is_empty() {
                        speculative_pairs.push((arith_term, const_term));
                        continue;
                    }
                    // Contradictory value guard (parallel to Int path).
                    if let Some(&prev_const) = self.propagated_term_values.get(&arith_term) {
                        if prev_const != const_term {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] SKIP contradictory real: {:?} was {:?} now {:?}",
                                    label,
                                    arith_term,
                                    prev_const,
                                    const_term
                                );
                            }
                            continue;
                        }
                    }
                    let pair = (arith_term, const_term);
                    if self.propagated_interface_eqs.insert(pair) {
                        self.interface_trail
                            .push(InterfaceTrailEntry::PropagatedEq(arith_term, const_term));
                        if self
                            .propagated_term_values
                            .insert(arith_term, const_term)
                            .is_none()
                        {
                            self.interface_trail
                                .push(InterfaceTrailEntry::PropagatedValue(arith_term));
                        }
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Real interface term {:?} = {} (const {:?}, {} reasons)",
                                label,
                                arith_term,
                                value,
                                const_term,
                                reasons.len()
                            );
                        }
                        reasons.sort_by_key(|r| r.term);
                        reasons.dedup_by_key(|r| r.term);
                        new_eqs.push(DiscoveredEquality::new(arith_term, const_term, reasons));
                    }
                }
            }
        }
        for eq in &new_eqs {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {label} evaluate_and_propagate_real returned self-equality ({:?} = {:?})",
                eq.lhs,
                eq.rhs
            );
        }
        // speculative_pairs contains zero-reason equalities from line 435.
        // Callers route these through NeedModelEquality/NeedModelEqualities
        // (SAT-level decisions), matching the #6846 fix for the Int path.
        // See UfNraSolver::check() and combiner_check.rs:326-354.
        (new_eqs, speculative_pairs)
    }
}
