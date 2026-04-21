// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving: push/pop scopes, value queries, trail access.

use super::*;

impl Solver {
    /// Push a new assertion scope.
    ///
    /// Clauses added after a `push()` are scoped and removed by `pop()`, while
    /// learned clauses are retained.
    pub fn push(&mut self) {
        // Permanently disable clause-deleting inprocessing techniques once
        // incremental mode is entered (#3662).
        self.disable_destructive_inprocessing();
        // Mark that push/pop has been used — original_ledger may
        // contain scope-selector clauses after pop() (#5077).
        self.cold.has_ever_scoped = true;

        // No NEW eliminations happen after push because
        // disable_destructive_inprocessing() gates all destructive
        // techniques (#3644, #3456, #3510). Variables eliminated BEFORE
        // push are reactivated by reset_search_state() when the arena is
        // rebuilt from original_ledger, with competitive VSIDS activity
        // to ensure they are branched on (#7981).

        let selector = self.new_var_internal();
        let idx = selector.index();
        if idx >= self.cold.scope_selector_set.len() {
            self.cold.scope_selector_set.resize(idx + 1, false);
        }
        self.cold.scope_selector_set[idx] = true;
        // Permanently record this variable as a scope selector (#5522).
        // Unlike scope_selector_set (cleared on pop), was_scope_selector is
        // never cleared. Used by verify_against_original to skip scoped
        // clauses while still verifying base-formula clauses.
        if idx >= self.cold.was_scope_selector.len() {
            self.cold.was_scope_selector.resize(idx + 1, false);
        }
        self.cold.was_scope_selector[idx] = true;
        self.cold.scope_selectors.push(selector);
        // Register ¬selector as an LRAT axiom so the checker can verify
        // derivations that depend on assumption decisions (#7108).
        // The axiom consumes an LRAT ID; advance solver-side counters to
        // prevent subsequent add_clause from reusing the same ID.
        #[cfg(debug_assertions)]
        {
            let mut axiom_id = 0u64;
            if let Some(ref mut pm) = self.proof_manager {
                let neg_selector = Literal::negative(selector);
                axiom_id = pm.register_lrat_axiom(&[neg_selector]);
                if axiom_id != 0 {
                    if self.cold.next_original_clause_id <= axiom_id {
                        self.cold.next_original_clause_id = axiom_id + 1;
                    }
                    if self.cold.next_clause_id <= axiom_id {
                        self.cold.next_clause_id = axiom_id + 1;
                    }
                }
            }
            self.cold.scope_selector_axiom_ids.push(axiom_id);
        }
        self.freeze(selector);
        // Save forward checker state so it resumes active RUP checking after
        // pop(), even if this scope ends in UNSAT (#4481).
        self.forward_checker_push();
        self.emit_diagnostic_scope_push(selector, 0);
    }

    /// Pop the most recent assertion scope.
    ///
    /// Returns `false` if there is no active scope.
    #[must_use = "returns false if no scope was active"]
    pub fn pop(&mut self) -> bool {
        let scope_depth_before = self.cold.scope_selectors.len();
        let Some(selector) = self.cold.scope_selectors.pop() else {
            return false;
        };
        #[cfg(debug_assertions)]
        self.cold.scope_selector_axiom_ids.pop();
        self.cold.scope_selector_set[selector.index()] = false;
        self.melt(selector);

        // No reconstruction truncation needed in pop(). Pre-push
        // eliminations are handled by reset_search_state() which rebuilds
        // the arena from original_ledger and reactivates variables with
        // competitive VSIDS activity (#3644, #3456, #3510, #7981).

        // Clear has_empty_clause only if it was set *inside* the scope being
        // popped (or deeper). Base-level empty clauses (depth 0) are permanent
        // UNSAT and must survive every pop.
        let mut retracted_empty_clause = false;
        if self.has_empty_clause
            && self.cold.empty_clause_scope_depth > self.cold.scope_selectors.len()
        {
            // Retract the empty clause from the LRAT proof stream (Fix 2 of #4475).
            if let Some(ec_id) = self.cold.empty_clause_lrat_id.take() {
                let _ = self.proof_emit_delete(&[], ec_id);
            }
            self.has_empty_clause = false;
            self.cold.empty_clause_in_proof = false;
            self.pending_theory_conflict = None;
            retracted_empty_clause = true;
        }

        // Restore forward checker state so it resumes active RUP checking
        // after a scoped UNSAT (#4481).
        self.forward_checker_pop();

        // Permanently disable clauses guarded by this selector, even if there
        // are still outer scopes active.
        let _ = self.add_clause_unscoped(vec![Literal::positive(selector)], false);
        self.emit_diagnostic_scope_pop(scope_depth_before, selector, retracted_empty_clause);
        true
    }

    /// Get the current scope depth.
    ///
    /// Returns the number of active push() scopes.
    pub fn scope_depth(&self) -> usize {
        self.cold.scope_selectors.len()
    }

    /// Get the current assignment for a variable
    pub fn value(&self, var: Variable) -> Option<bool> {
        self.var_value_from_vals(var.index())
    }

    /// Get the current decision level
    ///
    /// Returns 0 at the root level, incremented after each decision.
    pub fn current_decision_level(&self) -> u32 {
        self.decision_level
    }

    /// Get the decision level at which a variable was assigned
    ///
    /// Returns None if the variable is unassigned.
    pub fn var_level(&self, var: Variable) -> Option<u32> {
        if self.var_is_assigned(var.index()) {
            Some(self.var_data[var.index()].level)
        } else {
            None
        }
    }

    /// Get all currently assigned literals (the trail)
    ///
    /// Returns literals in assignment order. Useful for incremental
    /// theory solving where the theory needs to see partial assignments.
    pub fn trail(&self) -> &[Literal] {
        &self.trail
    }

    /// Get the number of assigned literals
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }
}
