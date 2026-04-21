// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor, snapshot restoration, config, and initialization for LRA.
//!
//! `new()`, `from_snapshot()`, `set_terms()`/`unset_terms()`,
//! `soft_reset_warm()`, `terms()`, and mode setters. Scope management
//! (push/pop), full/soft reset, and structural snapshots are in
//! `lifecycle_scope`.

use super::*;

impl LraSolver {
    /// Create a new LRA solver.
    ///
    /// Takes `&TermStore` to populate initial caches. The reference is NOT stored;
    /// only a raw pointer is kept for subsequent `set_terms` calls.
    #[must_use]
    pub fn new(terms: &TermStore) -> Self {
        Self {
            terms_ptr: std::ptr::from_ref(terms),
            rows: Vec::new(),
            vars: Vec::new(),
            term_to_var: HashMap::new(),
            var_to_term: HashMap::new(),
            next_var: 0,
            trail: Vec::new(),
            scopes: Vec::new(),
            asserted: HashMap::new(),
            asserted_trail: Vec::new(),
            atom_cache: HashMap::new(),
            current_parsing_atom: None,
            dirty: true,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::new(),
            trivial_conflict: None,
            bound_atoms: HashSet::new(),
            persistent_unsupported_atoms: HashSet::new(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1, // non-zero seed for xorshift32
            pivot_rng: 1,
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_lra: lra_debug_flags().debug_lra,
            debug_lra_bounds: lra_debug_flags().debug_lra_bounds,
            debug_lra_assert: lra_debug_flags().debug_lra_assert,
            debug_lra_reset: lra_debug_flags().debug_lra_reset,
            debug_lra_nelson_oppen: lra_debug_flags().debug_lra_nelson_oppen,
            debug_intern: lra_debug_flags().debug_intern,
            // Per-theory runtime statistics (#4706)
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            propagation_throttle_skips: 0,
            propagation_budget_exhaustions: 0,
            bcp_simplex_skips: 0,
            eager_reason_count: 0,
            deferred_reason_count: 0,
            simplex_sat_count: 0,
            registered_atoms: HashSet::new(),
            atom_index: HashMap::new(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::new(),
            combined_theory_mode: false,
            atom_slack: HashMap::new(),
            expr_to_slack: HashMap::new(),
            slack_var_set: HashSet::new(),
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::new(),
            fixed_term_value_members: HashMap::new(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            col_index: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            bounds_tightened_since_simplex: true,
            direct_bounds_changed_since_implied: true,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: Vec::new(),
            row_computed_gen: Vec::new(),
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            rows_at_check_start: 0,
            to_int_terms: Vec::new(),
            injected_to_int_axioms: HashSet::new(),
            propagation_dirty_vars: HashSet::new(),
            compound_use_index: HashMap::new(),
            var_to_atoms: HashMap::new(),
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            basic_var_to_row: HashMap::new(),
            touched_rows: HashSet::new(),
            propagate_direct_touched_rows_pending: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            unassigned_atom_count: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            in_infeasible_heap: Vec::new(),
            heap_stale: true,
            reason_seen_buf: HashSet::new(),
            not_inner_cache: HashMap::new(),
            const_bool_cache: HashMap::new(),
            refinement_eligible_cache: HashMap::new(),
            is_integer_sort_cache: HashMap::new(),
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::new(),
        }
    }

    /// Construct an `LraSolver` directly from a structural snapshot, avoiding
    /// the allocate-then-overwrite pattern of `new()` + `import_structural_snapshot()`.
    ///
    /// Returns `Some(solver)` if the snapshot downcasts successfully, `None` otherwise.
    /// The returned solver is in a clean assertion state (same as after `import_structural_snapshot`):
    /// all bounds are cleared, basic variable values are set to row constants, and
    /// `touched_rows` is empty.
    ///
    /// #6590: This eliminates ~50 empty collection allocations per split-loop iteration
    /// when a snapshot is available from a previous iteration.
    pub fn from_snapshot(terms: &TermStore, snapshot: Box<dyn std::any::Any>) -> Option<Self> {
        Self::try_from_snapshot(terms, snapshot).ok()
    }

    pub(crate) fn try_from_snapshot(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        let snap = snapshot.downcast::<LraStructuralSnapshot>()?;
        let var_count = snap.vars.len();
        // Build propagation_dirty_vars from the atom and compound indices.
        let mut propagation_dirty_vars: HashSet<u32> =
            HashSet::with_capacity(snap.atom_index.len() + snap.compound_use_index.len());
        propagation_dirty_vars.extend(snap.atom_index.keys().copied());
        propagation_dirty_vars.extend(snap.compound_use_index.keys().copied());
        let mut solver = Self {
            terms_ptr: std::ptr::from_ref(terms),
            // Structural fields from snapshot (moved, not cloned):
            rows: snap.rows,
            vars: snap.vars,
            term_to_var: snap.term_to_var,
            var_to_term: snap.var_to_term,
            next_var: snap.next_var,
            atom_cache: snap.atom_cache,
            registered_atoms: snap.registered_atoms,
            atom_index: snap.atom_index,
            compound_use_index: snap.compound_use_index,
            var_to_atoms: snap.var_to_atoms,
            atom_slack: snap.atom_slack,
            expr_to_slack: snap.expr_to_slack,
            slack_var_set: snap.slack_var_set,
            basic_var_to_row: snap.basic_var_to_row,
            col_index: snap.col_index,
            to_int_terms: snap.to_int_terms,
            unassigned_atom_count: snap.unassigned_atom_count,
            not_inner_cache: snap.not_inner_cache,
            const_bool_cache: snap.const_bool_cache,
            refinement_eligible_cache: snap.refinement_eligible_cache,
            is_integer_sort_cache: snap.is_integer_sort_cache,
            // Assertion-derived fields start clean:
            trail: Vec::new(),
            scopes: Vec::new(),
            asserted: HashMap::new(),
            asserted_trail: Vec::new(),
            current_parsing_atom: None,
            dirty: true,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::new(),
            trivial_conflict: None,
            bound_atoms: HashSet::new(),
            persistent_unsupported_atoms: HashSet::new(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1,
            pivot_rng: 1,
            debug_lra: lra_debug_flags().debug_lra,
            debug_lra_bounds: lra_debug_flags().debug_lra_bounds,
            debug_lra_assert: lra_debug_flags().debug_lra_assert,
            debug_lra_reset: lra_debug_flags().debug_lra_reset,
            debug_lra_nelson_oppen: lra_debug_flags().debug_lra_nelson_oppen,
            debug_intern: lra_debug_flags().debug_intern,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            propagation_throttle_skips: 0,
            propagation_budget_exhaustions: 0,
            bcp_simplex_skips: 0,
            eager_reason_count: 0,
            deferred_reason_count: 0,
            simplex_sat_count: 0,
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::new(),
            combined_theory_mode: false,
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::new(),
            fixed_term_value_members: HashMap::new(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            bounds_tightened_since_simplex: true,
            direct_bounds_changed_since_implied: true,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: vec![0; var_count],
            row_computed_gen: Vec::new(),
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            rows_at_check_start: 0,
            injected_to_int_axioms: HashSet::new(),
            propagation_dirty_vars,
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            touched_rows: HashSet::new(),
            propagate_direct_touched_rows_pending: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            in_infeasible_heap: vec![false; var_count],
            heap_stale: true,
            reason_seen_buf: HashSet::new(),
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::new(),
        };
        // Clear variable bounds and restore simplex invariant (same as import_structural_snapshot).
        for var_info in &mut solver.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &solver.rows {
            let basic = row.basic_var as usize;
            if basic < solver.vars.len() {
                solver.vars[basic].value = InfRational::from_rational(row.constant.to_big());
            }
        }
        // #6617: unassigned_atom_count is initialized from snapshot above, so no
        // full recount needed.
        Ok(solver)
    }

    /// Kani-only constructor: initializes only the pointer field, avoids
    /// `TermStore::new()` and `lra_debug_flags()` which trigger deep
    /// BTree/HashMap symbolic exploration that CBMC cannot handle (#6612).
    #[cfg(kani)]
    pub(crate) fn new_kani_minimal(ptr: *const TermStore) -> Self {
        Self {
            terms_ptr: ptr,
            rows: Vec::new(),
            vars: Vec::new(),
            term_to_var: HashMap::new(),
            var_to_term: HashMap::new(),
            next_var: 0,
            trail: Vec::new(),
            scopes: Vec::new(),
            asserted: HashMap::new(),
            asserted_trail: Vec::new(),
            atom_cache: HashMap::new(),
            current_parsing_atom: None,
            dirty: false,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::new(),
            trivial_conflict: None,
            bound_atoms: HashSet::new(),
            persistent_unsupported_atoms: HashSet::new(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1,
            pivot_rng: 1,
            debug_lra: false,
            debug_lra_bounds: false,
            debug_lra_assert: false,
            debug_lra_reset: false,
            debug_lra_nelson_oppen: false,
            debug_intern: false,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            propagation_throttle_skips: 0,
            propagation_budget_exhaustions: 0,
            bcp_simplex_skips: 0,
            eager_reason_count: 0,
            deferred_reason_count: 0,
            simplex_sat_count: 0,
            registered_atoms: HashSet::new(),
            atom_index: HashMap::new(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::new(),
            combined_theory_mode: false,
            atom_slack: HashMap::new(),
            expr_to_slack: HashMap::new(),
            slack_var_set: HashSet::new(),
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::new(),
            fixed_term_value_members: HashMap::new(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            col_index: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            bounds_tightened_since_simplex: false,
            direct_bounds_changed_since_implied: false,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: Vec::new(),
            row_computed_gen: Vec::new(),
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            rows_at_check_start: 0,
            to_int_terms: Vec::new(),
            injected_to_int_axioms: HashSet::new(),
            propagation_dirty_vars: HashSet::new(),
            compound_use_index: HashMap::new(),
            var_to_atoms: HashMap::new(),
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            basic_var_to_row: HashMap::new(),
            touched_rows: HashSet::new(),
            propagate_direct_touched_rows_pending: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            unassigned_atom_count: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            in_infeasible_heap: Vec::new(),
            heap_stale: true,
            reason_seen_buf: HashSet::new(),
            not_inner_cache: HashMap::new(),
            const_bool_cache: HashMap::new(),
            refinement_eligible_cache: HashMap::new(),
            is_integer_sort_cache: HashMap::new(),
            dirty_vars_scratch: Vec::new(),
        }
    }

    /// Set the TermStore pointer for the next operation batch (#6590 Packet 2).
    ///
    /// # Safety contract
    /// The caller must ensure the `TermStore` outlives any subsequent calls to
    /// `register_atom`, `check`, `assert_literal`, etc. before `unset_terms`.
    pub fn set_terms(&mut self, terms: &TermStore) {
        self.terms_ptr = std::ptr::from_ref(terms);
    }

    /// Clear the TermStore pointer after an operation batch (#6590 Packet 2).
    pub fn unset_terms(&mut self) {
        self.terms_ptr = std::ptr::null();
    }

    /// Warm soft-reset: clear assertion state but preserve simplex variable
    /// values and basis (#6590 Packet 3).
    ///
    /// Like `soft_reset()`, this clears bounds, assertion trails, and conflict
    /// state so the solver is ready for a new set of assertions. Unlike
    /// `soft_reset()`, it keeps variable values from the previous iteration.
    /// When the same (or similar) atoms are re-asserted, `check()` calls
    /// `restore_feasibility()` which only pivots variables whose bounds have
    /// been violated — matching Z3's persistent `lar_solver` warm-start.
    pub fn soft_reset_warm(&mut self) {
        self.asserted.clear();
        self.asserted_trail.clear();
        self.trail.clear();
        self.scopes.clear();
        self.pending_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.propagated_atoms.clear();
        // Preserve any dirty vars already accumulated by the current warm
        // iteration, then reseed the structural keys needed for the next pass.
        // This keeps compound wakeups alive across persistent split-loop
        // warm resets instead of starting each round from a blank dirty set.
        self.propagation_dirty_vars
            .extend(self.atom_index.keys().copied());
        self.propagation_dirty_vars
            .extend(self.compound_use_index.keys().copied());
        self.last_compound_propagations_queued = 0;
        self.last_compound_wake_dirty_hits = 0;
        self.last_compound_wake_candidates = 0;
        self.implied_bounds.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.trivial_conflict = None;
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        self.dirty = true;
        self.last_check_trail_pos = 0;
        self.bounds_tightened_since_simplex = true;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.rows_at_check_start = 0;

        // Preserve already-encoded model-equality pairs across warm iterations.
        // The persistent split loop keeps the SAT solver alive, so fixed-term and
        // offset equalities requested in an earlier round are still available as
        // SAT atoms. Clearing this set would re-request the same equality batch
        // every warm iteration and can starve convergence on large chains.
        // WARM: clear bounds but KEEP variable values from previous iteration.
        // The simplex basis (row structure, basic/non-basic assignment) persists.
        // Values approximate the previous feasible solution; restore_feasibility()
        // will fix any variables whose new bounds are violated.
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            // var_info.value preserved — this is the warm-start win
        }

        self.bound_atoms.clear();
        self.injected_to_int_axioms.clear();
        self.touched_rows.clear();
        for i in 0..self.rows.len() {
            self.touched_rows.insert(i);
        }
        self.propagate_direct_touched_rows_pending = false;
        self.recount_unassigned_atoms();
        self.infeasible_heap.clear();
        for b in self.in_infeasible_heap.iter_mut() {
            *b = false;
        }
        self.heap_stale = true;
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
    }

    /// Access the TermStore via the stored raw pointer.
    ///
    /// Returns a reference with a lifetime detached from `&self` so that
    /// calling `self.terms()` does not prevent subsequent `&mut self` access
    /// to other fields. This is sound because the raw pointer's validity is
    /// guaranteed by the `set_terms()` caller, not by `&self`.
    ///
    /// # Panics
    /// Panics if `terms_ptr` is null (i.e., `set_terms` was not called).
    #[inline]
    #[allow(clippy::needless_lifetimes)]
    #[allow(unsafe_code)]
    pub(crate) fn terms<'t>(&self) -> &'t TermStore {
        let ptr = self.terms_ptr;
        assert!(
            !ptr.is_null(),
            "BUG: LraSolver::terms() called without set_terms()"
        );
        // SAFETY: The TermStore pointer is set by set_terms() and guaranteed
        // alive for the duration of the operation batch. The lifetime is
        // independent of &self, allowing concurrent &mut self field access.
        unsafe { &*ptr }
    }

    /// Enable integer mode: strict bounds are canonicalized to non-strict.
    /// `expr < 0` becomes `expr <= -1`, `expr > 0` becomes `expr >= 1`.
    pub fn set_integer_mode(&mut self, enabled: bool) {
        self.integer_mode = enabled;
    }

    /// Enable combined theory mode: suppress unsupported-atom marking for
    /// unknown function/term catch-all arms in `parse_linear_expr`.
    /// Cross-theory terms (array selects, UF applications) are expected in
    /// combined solvers and handled by the Nelson-Oppen loop (#5524).
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.combined_theory_mode = enabled;
    }

    /// Drain buffered disequality split requests collected during batch evaluation (#6259).
    ///
    /// When `check()` finds multiple violated single-variable disequalities, it returns
    /// the first via `NeedDisequalitySplit` and buffers the rest here. The DPLL(T) split
    /// loop should call this method to retrieve all remaining splits and process them in
    /// a single iteration, avoiding O(N) solver restarts.
    pub fn drain_pending_diseq_splits(&mut self) -> Vec<DisequalitySplitRequest> {
        std::mem::take(&mut self.pending_diseq_splits)
    }
}
