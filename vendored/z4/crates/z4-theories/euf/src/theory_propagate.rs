// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF theory propagation helpers for `TheorySolver::propagate()`.
//!
//! Positive equality propagation and disequality propagation, extracted
//! from `theory_impl.rs` to keep each file under 500 lines.

use z4_core::TheoryLit;
use z4_core::TheoryPropagation;

use crate::solver::EufSolver;

impl EufSolver<'_> {
    /// Propagate implied equalities: `(= a b) = true` when `find(a) = find(b)`.
    ///
    /// Scans pre-indexed equality terms (`eq_terms`) for unassigned equalities
    /// whose sides are in the same equivalence class, then uses `explain()` to
    /// build minimal propagation reasons.
    pub(crate) fn propagate_positive_equalities(
        &mut self,
        propagations: &mut Vec<TheoryPropagation>,
    ) {
        let debug = self.debug_euf;

        let n_eqs = self.eq_terms.len();
        self.scratch_potential_props.clear();
        for i in 0..n_eqs {
            let (term_id, lhs, rhs) = self.eq_terms[i];
            if self.assigns.contains_key(&term_id) {
                continue;
            }
            if self.terms.sort(lhs) != self.terms.sort(rhs) {
                continue;
            }
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            if lhs_rep == rhs_rep {
                self.scratch_potential_props.push((term_id, lhs, rhs));
            }
        }

        for idx in 0..self.scratch_potential_props.len() {
            let (term_id, lhs, rhs) = self.scratch_potential_props[idx];
            let reasons = self.explain(lhs, rhs);
            if debug {
                safe_eprintln!(
                    "[EUF PROPAGATE] Propagating eq {} = true (terms {} == {}) with {} reasons",
                    term_id.0,
                    lhs.0,
                    rhs.0,
                    reasons.len()
                );
            }
            // Skip propagation if explain() returned empty (broken proof forest).
            // An incomplete propagation reason would produce an unsound learned
            // clause — stronger than justified by the actual equality chain. (#6849)
            if reasons.is_empty() {
                continue;
            }
            debug_assert!(
                !self.assigns.contains_key(&term_id),
                "BUG: EUF propagate: term {} already assigned (should have been filtered)",
                term_id.0
            );
            debug_assert!(
                reasons.iter().all(|l| self.assigns.contains_key(&l.term)),
                "BUG: EUF propagate: reason for term {} references unassigned term",
                term_id.0
            );
            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(term_id, true),
                reason: reasons,
            });
        }
    }

    /// Propagate disequalities: `(= c d) = false` when `find(c) != find(d)` and
    /// there exists an asserted `(= a b) = false` with `find(a) = find(c)` and
    /// `find(b) = find(d)` (or symmetric).
    ///
    /// Without this, the SAT solver must guess values that the theory already
    /// knows are false, causing exponential branching on QG-classification
    /// and similar dense UF benchmarks (#5575).
    pub(crate) fn propagate_disequalities(&mut self, propagations: &mut Vec<TheoryPropagation>) {
        let debug = self.debug_euf;
        let n_eqs = self.eq_terms.len();

        // Build diseq index: (min_rep, max_rep) -> (a, b, eq_term)
        self.scratch_diseq_index.clear();
        for (&lit_term, &value) in &self.assigns {
            if value {
                continue; // only interested in false equalities (disequalities)
            }
            if let Some((a, b)) = self.decode_eq(lit_term) {
                if self.terms.sort(a) != self.terms.sort(b) {
                    continue;
                }
                let (a_rep, b_rep) = (self.enode_find_const(a.0), self.enode_find_const(b.0));
                if a_rep == b_rep {
                    continue; // conflict, not propagation — handled by check()
                }
                let key = (a_rep.min(b_rep), a_rep.max(b_rep));
                self.scratch_diseq_index
                    .entry(key)
                    .or_insert((a, b, lit_term));
            }
        }

        if self.scratch_diseq_index.is_empty() {
            return;
        }

        // Find unassigned equality terms whose sides map to a known disequality pair
        self.scratch_neg_props.clear();
        for i in 0..n_eqs {
            let (term_id, lhs, rhs) = self.eq_terms[i];
            if self.assigns.contains_key(&term_id) {
                continue;
            }
            if self.terms.sort(lhs) != self.terms.sort(rhs) {
                continue;
            }
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            if lhs_rep == rhs_rep {
                continue; // same class — handled by positive propagation
            }
            let key = (lhs_rep.min(rhs_rep), lhs_rep.max(rhs_rep));
            if let Some(&(diseq_a, diseq_b, diseq_term)) = self.scratch_diseq_index.get(&key) {
                self.scratch_neg_props
                    .push((term_id, lhs, rhs, diseq_a, diseq_b, diseq_term));
            }
        }

        for idx in 0..self.scratch_neg_props.len() {
            let (term_id, lhs, rhs, diseq_a, diseq_b, diseq_term) = self.scratch_neg_props[idx];
            // Build reason: disequality + equality chains
            let mut reasons = vec![TheoryLit::new(diseq_term, false)];

            // Find which orientation matches
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            let (da_rep, db_rep) = (
                self.enode_find_const(diseq_a.0),
                self.enode_find_const(diseq_b.0),
            );

            let (match_a, match_b) = if lhs_rep == da_rep && rhs_rep == db_rep {
                (diseq_a, diseq_b)
            } else if lhs_rep == db_rep && rhs_rep == da_rep {
                (diseq_b, diseq_a)
            } else {
                debug_assert!(false, "BUG: diseq propagation orientation mismatch");
                continue;
            };

            // Explain lhs = match_a (if not the same term)
            if lhs != match_a {
                let sub_reasons = self.explain(lhs, match_a);
                reasons.extend(sub_reasons);
            }
            // Explain rhs = match_b (if not the same term)
            if rhs != match_b {
                let sub_reasons = self.explain(rhs, match_b);
                reasons.extend(sub_reasons);
            }

            // Deduplicate reasons
            reasons.sort_by_key(|l| (l.term.0, l.value));
            reasons.dedup_by_key(|l| (l.term.0, l.value));

            if debug {
                safe_eprintln!(
                    "[EUF PROPAGATE] Propagating eq {} = false (terms {} != {}) with {} reasons (diseq {} via {})",
                    term_id.0,
                    lhs.0,
                    rhs.0,
                    reasons.len(),
                    diseq_term.0,
                    if match_a == diseq_a { "direct" } else { "swapped" }
                );
            }
            debug_assert!(
                !self.assigns.contains_key(&term_id),
                "BUG: EUF diseq propagate: term {} already assigned",
                term_id.0
            );

            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(term_id, false),
                reason: reasons,
            });
        }
    }
}
