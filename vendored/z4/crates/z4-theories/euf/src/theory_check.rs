// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF conflict detection helpers for `TheorySolver::check()`.
//!
//! Each method checks one category of conflict: disequalities, distinct
//! constraints, constant clashes, and Boolean congruence.

use z4_core::term::{Constant, TermData, TermId};
use z4_core::{Sort, TheoryLit, TheoryResult};

use crate::solver::EufSolver;

impl EufSolver<'_> {
    /// Check for conflicts from explicit disequalities `(= a b) = false`
    /// where `find(a) = find(b)`.
    pub(crate) fn check_disequality_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        self.scratch_diseqs.clear();
        for (&lit_term, &v) in &self.assigns {
            if !v {
                if let Some((lhs, rhs)) = self.decode_eq(lit_term) {
                    if self.terms.sort(lhs) == self.terms.sort(rhs) {
                        self.scratch_diseqs.push((lit_term, lhs, rhs));
                    }
                }
            }
        }
        self.scratch_diseqs
            .sort_by_key(|(lit_term, _, _)| lit_term.0);

        for idx in 0..self.scratch_diseqs.len() {
            let (lit_term, lhs, rhs) = self.scratch_diseqs[idx];
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Diseq: term {} != term {} (reps: {} vs {})",
                    lhs.0,
                    rhs.0,
                    lhs_rep,
                    rhs_rep
                );
            }
            if lhs_rep == rhs_rep {
                if debug {
                    safe_eprintln!("[EUF CHECK] CONFLICT DETECTED!");
                }
                let reasons = self.explain(lhs, rhs);
                if debug {
                    safe_eprintln!(
                        "[EUF CHECK] Conflict explained with {} reasons (vs {} all equalities)",
                        reasons.len(),
                        self.all_true_equalities().len()
                    );
                }
                // Empty reasons is legitimate when the equality was asserted
                // via unconditional shared equality (no preconditions).
                // #6812: Do NOT filter out cross-theory reasons from the conflict.
                // In Nelson-Oppen, explain() returns shared equality reasons that
                // reference terms from another theory (LRA, LIA, arrays). These
                // cross-theory reasons are REQUIRED in the conflict clause.
                self.conflict_count += 1;
                return Some(self.conflict_with_reasons(reasons, TheoryLit::new(lit_term, false)));
            }
        }

        None
    }

    /// Check for conflicts from `(distinct a b c ...) = true`
    /// where two arguments are in the same equivalence class.
    pub(crate) fn check_distinct_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        self.scratch_distincts.clear();
        for (&lit_term, &v) in &self.assigns {
            if v {
                if let Some(args) = self.decode_distinct(lit_term) {
                    self.scratch_distincts.push((lit_term, args.to_vec()));
                }
            }
        }
        self.scratch_distincts
            .sort_by_key(|(lit_term, _)| lit_term.0);

        if debug {
            safe_eprintln!(
                "[EUF CHECK] Found {} distinct constraints",
                self.scratch_distincts.len()
            );
        }

        for idx in 0..self.scratch_distincts.len() {
            let lit_term = self.scratch_distincts[idx].0;
            let n_args = self.scratch_distincts[idx].1.len();
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Checking distinct term {} with {} args",
                    lit_term.0,
                    n_args
                );
            }
            for i in 0..n_args {
                for j in (i + 1)..n_args {
                    // Index directly into scratch buffer to avoid long-lived borrows (#5575).
                    let arg_i = self.scratch_distincts[idx].1[i];
                    let arg_j = self.scratch_distincts[idx].1[j];
                    let (rep_i, rep_j) = (
                        self.enode_find_const(arg_i.0),
                        self.enode_find_const(arg_j.0),
                    );
                    if debug {
                        safe_eprintln!(
                            "[EUF CHECK] args[{}]={} (rep={}) vs args[{}]={} (rep={})",
                            i,
                            arg_i.0,
                            rep_i,
                            j,
                            arg_j.0,
                            rep_j
                        );
                    }
                    if rep_i == rep_j {
                        let reasons = self.explain(arg_i, arg_j);
                        debug_assert!(
                            !reasons.is_empty(),
                            "BUG(#4840): EUF explain returned empty conflict reasons for distinct ({}, {})",
                            arg_i.0, arg_j.0
                        );
                        if reasons.is_empty() {
                            return Some(TheoryResult::Unknown);
                        }
                        self.conflict_count += 1;
                        return Some(
                            self.conflict_with_reasons(reasons, TheoryLit::new(lit_term, true)),
                        );
                    }
                }
            }
        }

        None
    }

    /// Check for conflicts from distinct constants in the same equivalence class.
    ///
    /// Different constants (e.g., 5 and 6) must never be equal. This axiom is
    /// implicit in most theories: distinct numerals denote distinct values.
    pub(crate) fn check_constant_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        self.scratch_rep_to_const.clear();
        for i in 0..self.terms.len() {
            let term_id = TermId(i as u32);
            if let TermData::Const(c) = self.terms.get(term_id) {
                // Skip Boolean constants - they're handled separately
                if matches!(c, Constant::Bool(_)) {
                    continue;
                }
                let rep = if self.enodes_init {
                    self.enode_find_const(term_id.0)
                } else {
                    self.uf.find(term_id.0)
                };
                if let Some(&(other_term, ref other_const)) = self.scratch_rep_to_const.get(&rep) {
                    if c != other_const {
                        if debug {
                            safe_eprintln!(
                                "[EUF CHECK] Constant conflict: {:?} and {:?} in same class (rep={})",
                                c, other_const, rep
                            );
                        }
                        let mut reasons = self.explain(term_id, other_term);
                        if reasons.is_empty() {
                            // #6812: explain() returned empty reasons for a constant
                            // conflict. Fallback: collect ALL shared equality reasons
                            // + all true equalities as a conservative (sound)
                            // over-approximation.
                            for (_, lits) in &self.shared_equality_reasons {
                                reasons.extend(lits.iter().copied());
                            }
                            reasons.extend(self.all_true_equalities());
                            reasons.sort_by_key(|l| (l.term, l.value));
                            reasons.dedup_by_key(|l| (l.term, l.value));
                            if reasons.is_empty() {
                                return Some(TheoryResult::Unknown);
                            }
                        }
                        self.conflict_count += 1;
                        return Some(TheoryResult::Unsat(reasons));
                    }
                } else {
                    self.scratch_rep_to_const.insert(rep, (term_id, c.clone()));
                }
            }
        }

        None
    }

    /// Check for conflicts from Boolean congruence: merged Boolean-valued terms
    /// must share their truth value assignment.
    pub(crate) fn check_bool_congruence_conflicts(&mut self) -> Option<TheoryResult> {
        // Sort by TermId for deterministic conflict detection — different HashMap
        // iteration orders can cause different (but valid) conflicts to be found
        // first, leading to non-deterministic solver behavior (#3041).
        self.scratch_bool_terms.clear();
        for (&term, &val) in &self.assigns {
            if self.terms.sort(term) != &Sort::Bool {
                continue;
            }
            let enforce = match self.terms.get(term) {
                TermData::Var(_, _) => true,
                TermData::App(sym, _) => !Self::is_builtin_symbol(sym),
                _ => false,
            };
            if enforce {
                self.scratch_bool_terms.push((term, val));
            }
        }
        self.scratch_bool_terms.sort_by_key(|(term, _)| *term);

        self.scratch_rep_value.clear();
        for idx in 0..self.scratch_bool_terms.len() {
            let (term, val) = self.scratch_bool_terms[idx];
            let rep = if self.enodes_init {
                self.enode_find_const(term.0)
            } else {
                self.uf.find(term.0)
            };
            if let Some(&(other_term, other_val)) = self.scratch_rep_value.get(&rep) {
                if other_val != val {
                    // Use explain() for minimal conflict clause
                    let mut reasons = self.explain(term, other_term);
                    debug_assert!(
                        !reasons.is_empty(),
                        "BUG(#4840): EUF explain returned empty conflict reasons for bool-congruence ({}, {})",
                        term.0, other_term.0
                    );
                    if reasons.is_empty() {
                        return Some(TheoryResult::Unknown);
                    }
                    reasons.push(TheoryLit::new(other_term, other_val));
                    self.conflict_count += 1;
                    return Some(self.conflict_with_reasons(reasons, TheoryLit::new(term, val)));
                }
            } else {
                self.scratch_rep_value.insert(rep, (term, val));
            }
        }

        None
    }
}
