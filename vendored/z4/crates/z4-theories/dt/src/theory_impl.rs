// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `DtSolver`.
//!
//! Implements the DPLL(T) theory interface for the datatype theory.

use super::*;

impl TheorySolver for DtSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = if let Some(inner) = self.decode_not(literal) {
            (inner, !value)
        } else {
            (literal, value)
        };

        // Check if this is an equality
        if let Some((lhs, rhs)) = self.decode_eq(term) {
            self.process_equality(term, lhs, rhs, val);
            return;
        }

        // Check if this term itself is a constructor (for direct constructor assertions)
        if let Some((dt_name, ctor_name, args)) = self.try_extract_constructor(term) {
            if !self.term_constructors.contains_key(&term) {
                self.register_constructor(term, &dt_name, &ctor_name, &args);
            }
        }

        // Check for tester assertions (is-Constructor)
        if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
            if name.starts_with("is-") && args.len() == 1 {
                if let Some((_dt_name, ctor_name)) = self.tester_map.get(name).cloned() {
                    self.tester_results.insert(args[0], (ctor_name, val, term));
                    self.current_scope.tester_keys.push(args[0]);
                }
            }
        }
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            constructors = self.term_constructors.len(),
            eq_lits = self.asserted_eq_lits.len(),
            diseqs = self.asserted_diseqs.len(),
            "DT check"
        );

        if self.debug {
            tracing::trace!(
                constructors = self.term_constructors.len(),
                eq_lits = self.asserted_eq_lits.len(),
                diseqs = self.asserted_diseqs.len(),
                scopes = self.scopes.len(),
                "DT check verbose"
            );
        }

        #[cfg(debug_assertions)]
        self.debug_check_invariants();

        // Run injectivity FIRST: it may merge terms in the union-find via
        // constructor argument equalities (e.g., mk-rec(f1(s),...) = mk-rec(f1(t),...)
        // → f1(s) = f1(t)). Subsequent checks need the updated classes (#5082).
        if let Some(conflict) = self.check_injectivity_conflicts() {
            tracing::debug!("DT check: injectivity conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check for constructor clashes (including those exposed by injectivity merges).
        if let Some(conflict) = self.check_clash() {
            tracing::debug!("DT check: constructor clash conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check tester results against constructors in equivalence classes (#5082).
        if let Some(conflict) = self.check_tester_conflicts() {
            tracing::debug!("DT check: tester-constructor conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check for implied equality vs asserted disequality conflicts.
        if let Some(conflict) = self.check_disequality_conflicts() {
            tracing::debug!("DT check: disequality conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Occurs check (acyclicity) for recursive datatypes.
        //
        // Cycles like `x = cons(1, x)` imply infinite values and are UNSAT for
        // finite algebraic datatypes (SMT-LIB). See designs/2026-01-31-dt-acyclicity.md.
        if let Some(conflict) = self.occurs_check() {
            tracing::debug!("DT check: acyclicity conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        tracing::debug!("DT check: sat");
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = std::mem::take(&mut self.pending);
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("dt_checks", self.check_count),
            ("dt_conflicts", self.conflict_count),
            ("dt_propagations", self.propagation_count),
        ]
    }

    fn push(&mut self) {
        self.current_scope.asserted_eq_lits_len = self.asserted_eq_lits.len();
        self.current_scope.asserted_diseqs_len = self.asserted_diseqs.len();
        // Snapshot union-find for full restore on pop (#3656).
        // Path compression in find() makes trail-based reversal impossible,
        // so we save the entire parent map.
        self.current_scope.parent_snapshot = self.parent.clone();
        self.scopes.push(std::mem::take(&mut self.current_scope));
    }

    fn pop(&mut self) {
        if let Some(mut scope) = self.scopes.pop() {
            // Restore union-find from snapshot (#3656).
            // This undoes all union() merges and path compression from the popped scope.
            // Use take() to avoid cloning — the snapshot is consumed and current_scope
            // will get a fresh snapshot on the next push().
            self.parent = std::mem::take(&mut scope.parent_snapshot);
            // Undo constructor registrations from current scope
            for term_id in &self.current_scope.registered_ctors {
                self.term_constructors.remove(term_id);
            }
            // Undo tester results from current scope
            for term_id in &self.current_scope.tester_keys {
                self.tester_results.remove(term_id);
            }
            // Undo equality assertions
            self.asserted_eq_lits.truncate(scope.asserted_eq_lits_len);
            self.asserted_diseqs.truncate(scope.asserted_diseqs_len);
            // Clear propagated pairs, pending propagations, and pending
            // injectivity equalities since the assertions that derived them
            // may have been popped. These will be re-discovered on subsequent
            // check() calls. (#3725: stale propagations must not leak across scopes)
            self.propagated_eq_pairs.clear();
            self.pending.clear();
            self.pending_injectivity_eqs.clear();
            self.current_scope = scope;
        }
    }

    fn reset(&mut self) {
        self.term_constructors.clear();
        self.parent.clear();
        self.pending.clear();
        self.scopes.clear();
        self.current_scope = DtScope::default();
        self.tester_results.clear();
        self.asserted_eq_lits.clear();
        self.pending_injectivity_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.asserted_diseqs.clear();
        // Note: datatype_defs, ctor_to_dt, and tester_map are preserved across reset
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        // Return injectivity-derived equalities for Nelson-Oppen propagation.
        // These are discovered during check() when same-constructor terms are
        // in the same equivalence class.
        EqualityPropagationResult {
            equalities: std::mem::take(&mut self.pending_injectivity_eqs),
            conflict: None,
        }
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, _reason: &[TheoryLit]) {
        // Receive equality from another theory (e.g., EUF → DT in Nelson-Oppen).
        // Merge the terms in our union-find so that injectivity checks are aware.
        self.assert_equality(lhs, rhs);
    }
}
