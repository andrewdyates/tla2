// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving state management.
//!
//! This module provides state management for incremental SMT solving:
//! - `IncrementalBvState`: Persistent state for BV theory with rebuild-on-pop reuse
//! - `IncrementalTheoryState`: Persistent state for other theories (EUF/LRA/LIA)
//!
//! All incremental subsystems implement [`IncrementalSubsystem`], which
//! provides the push/pop/reset interface used by `Executor::execute()`.
//! Adding a new subsystem requires:
//! 1. Implementing `IncrementalSubsystem` for the type
//! 2. Adding the field to the `for_each_incremental_subsystem!` macro in `executor.rs`
//!
//! Key design invariant (designs/2026-01-29-incremental-cnf-scoping-soundness.md):
//! - Definitional clauses (Tseitin definitions) are added GLOBALLY
//! - Only assertion activation (unit clause on root literal) is scoped
//! - This ensures cached term→var mappings remain valid after pop

#[cfg(test)]
mod tests;

/// Trait for subsystems that participate in incremental push/pop/reset scoping.
///
/// Every field in `Executor` that maintains scope state must implement this
/// trait. The executor dispatches push/pop/reset to all registered subsystems
/// via the `for_each_incremental_subsystem!` macro.
pub(crate) trait IncrementalSubsystem {
    /// Save current state for later restoration by `pop`.
    fn push(&mut self);

    /// Restore state to before the matching `push`.
    /// Returns `true` if a scope was popped, `false` on underflow (no matching push).
    fn pop(&mut self) -> bool;

    /// Reset all state to initial conditions.
    fn reset(&mut self);
}

mod bv_state;
pub(crate) use bv_state::IncrementalBvState;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{Sort, TermData, TermId, TermStore, TseitinState};
use z4_sat::Solver as SatSolver;

/// Persistent state for incremental theory solving (QF_UF, QF_LRA, QF_LIA, etc.)
///
/// This maintains:
/// - Tseitin variable mappings for consistent term-to-var mappings across check-sat calls
/// - A persistent SAT solver that retains learned clauses
/// - Set of encoded assertions to avoid re-encoding terms with cached vars
/// - Scope depth tracking with pending push support
///
/// Key design invariant (designs/2026-01-29-incremental-cnf-scoping-soundness.md):
/// - Definitional clauses (Tseitin definitions) are added GLOBALLY via add_clause_global()
/// - Only assertion activation (unit clause on root literal) is scoped via add_clause()
/// - This ensures cached term→var mappings remain valid after pop: their definitions
///   are always active, only the assertions that use them are scoped.
#[derive(Clone, Default)]
pub(crate) struct LiaDerivedAssertionMetadata {
    /// Shallowest scope where this derived assertion must remain active.
    pub(crate) activation_depth: usize,
    /// Source assertion sets that justify keeping the derived assertion active.
    pub(crate) source_sets: Vec<Vec<TermId>>,
}

pub(crate) struct IncrementalTheoryState {
    /// Persistent SAT solver that retains learned clauses
    pub(crate) persistent_sat: Option<SatSolver>,
    /// Persistent SAT solver for incremental LIA solving.
    ///
    /// LIA uses a branch-and-bound loop that adds temporary split constraints.
    /// We keep a dedicated solver here so we can retain learned clauses across
    /// check-sat calls without interfering with other incremental theory modes.
    pub(crate) lia_persistent_sat: Option<SatSolver>,
    /// Map of assertions that have been encoded (globally) in this session to root literals.
    /// Used to avoid re-encoding terms whose definitions are already in the solver and to
    /// re-add scoped activation clauses after pop.
    pub(crate) encoded_assertions: HashMap<TermId, i32>,
    /// Scope depth where each assertion's activation clause was last added.
    ///
    /// An activation added at depth `d` remains valid for all deeper scopes `>= d`.
    /// After pop, only assertions with activation depth greater than the new
    /// scope depth must be re-activated.
    pub(crate) assertion_activation_scope: HashMap<TermId, usize>,
    /// Saved Tseitin state for consistent term-to-var mappings across calls.
    /// Used by `persistent_sat` pipelines.
    pub(crate) tseitin_state: TseitinState,
    /// Per-solver Tseitin encoding state for `lia_persistent_sat` (#6853).
    ///
    /// The LIA solver uses a separate SAT solver (`lia_persistent_sat`) with
    /// its own variable space. Sharing a Tseitin state between two solvers
    /// causes variable index collisions: a Tseitin variable cached from
    /// encoding for one solver can coincide with a scope selector allocated
    /// by `push()` in the other solver. Separate Tseitin states eliminate
    /// this cross-solver pollution entirely.
    pub(crate) lia_tseitin_state: TseitinState,
    /// Encoded assertion roots for `lia_persistent_sat` (#6853).
    pub(crate) lia_encoded_assertions: HashMap<TermId, i32>,
    /// Activation scope depths for `lia_persistent_sat` (#6853).
    pub(crate) lia_assertion_activation_scope: HashMap<TermId, usize>,
    /// Clausification proof ledger aligned with SAT original-clause insertion order.
    ///
    /// This mirrors every original clause added to the persistent SAT solver:
    /// definitional clauses carry their Tseitin proof annotation, while root
    /// activations and re-activations append `None`.
    pub(crate) clausification_proofs: Vec<Option<z4_core::ClausificationProof>>,
    /// Theory-lemma proof ledger aligned with SAT original-clause insertion order.
    ///
    /// When a persistent original SAT clause comes from `NeedLemmas`, this
    /// stores the theory-proof annotation SatProofManager should emit for that
    /// same original clause index.
    pub(crate) original_clause_theory_proofs: Vec<Option<z4_core::TheoryLemmaProof>>,
    /// Permanent theory lemmas replayed into each fresh theory rebuild.
    ///
    /// The no-split incremental pipeline recreates the theory solver on every
    /// SAT round, so clauses learned via `NeedLemmas` must be replayed here to
    /// preserve `note_applied_theory_lemma` metadata across rounds and across
    /// incremental `check-sat` calls.
    pub(crate) theory_lemmas: Vec<z4_core::TheoryLemma>,
    /// O(1) membership test for persistent theory-lemma replay.
    pub(crate) theory_lemma_keys: HashSet<Vec<z4_core::TheoryLit>>,
    /// Current scope depth (0 = global, 1+ = in push scope)
    pub(crate) scope_depth: usize,
    /// Pending push count: increments on SMT push before solver exists.
    /// Applied when solver is created via apply_pending_pushes().
    pub(crate) pending_push: usize,
    /// Derived LIA assertions for the active preprocessed assertion set.
    pub(crate) lia_derived_assertions: HashMap<TermId, LiaDerivedAssertionMetadata>,
    /// Theory atoms registered for theory communication
    pub(crate) theory_atoms: Vec<TermId>,
    /// Assertions that existed before incremental mode was first enabled.
    ///
    /// Incremental mode is toggled by `push`, but the first incremental solve
    /// may happen inside that pushed scope. These pre-existing assertions are
    /// semantically global and must keep global activation clauses.
    pub(crate) pre_push_assertions: HashSet<TermId>,
    /// Whether assertion activation clauses may need to be re-added.
    ///
    /// This is set on `pop()` because scoped activation clauses are disabled when
    /// a scope is popped. It avoids re-adding duplicate activation units on every
    /// `check-sat` while still restoring activations after scope drops.
    pub(crate) needs_activation_reassert: bool,
    /// Cumulative theory conflicts across incremental check-sat calls (#662).
    pub(crate) theory_conflicts: u64,
    /// Cumulative theory propagations across incremental check-sat calls (#662).
    pub(crate) theory_propagations: u64,
    /// Cumulative DPLL(T) round trips across incremental check-sat calls (#4802).
    /// Mirrors the DpllT `timings.round_trips` counter for the incremental path.
    pub(crate) round_trips: u64,
    /// Cumulative SAT solve time (seconds). Tracked per solve call (#5175).
    pub(crate) sat_solve_secs: f64,
    /// Cumulative theory sync time (seconds). Tracked per solve call (#5175).
    pub(crate) theory_sync_secs: f64,
    /// Cumulative theory check time (seconds). Tracked per solve call (#5175).
    pub(crate) theory_check_secs: f64,
}

impl IncrementalTheoryState {
    pub(crate) fn new() -> Self {
        Self {
            persistent_sat: None,
            lia_persistent_sat: None,
            encoded_assertions: HashMap::new(),
            assertion_activation_scope: HashMap::new(),
            tseitin_state: TseitinState::new(),
            lia_tseitin_state: TseitinState::new(),
            lia_encoded_assertions: HashMap::new(),
            lia_assertion_activation_scope: HashMap::new(),
            clausification_proofs: Vec::new(),
            original_clause_theory_proofs: Vec::new(),
            theory_lemmas: Vec::new(),
            theory_lemma_keys: HashSet::new(),
            scope_depth: 0,
            pending_push: 0,
            lia_derived_assertions: HashMap::new(),
            theory_atoms: Vec::new(),
            pre_push_assertions: HashSet::new(),
            needs_activation_reassert: false,
            theory_conflicts: 0,
            theory_propagations: 0,
            round_trips: 0,
            sat_solve_secs: 0.0,
            theory_sync_secs: 0.0,
            theory_check_secs: 0.0,
        }
    }

    /// Sync tseitin_state.next_var to account for ALL SAT solver allocations.
    ///
    /// CRITICAL: Use total_num_vars() not user_num_vars() to include scope selectors.
    /// Scope selectors are allocated by push() and occupy variable indices that
    /// Tseitin encoding must avoid. (#1447)
    #[cfg(test)]
    pub(crate) fn sync_tseitin_next_var(&mut self) {
        let mut next_var = self.tseitin_state.next_var.max(1);

        if let Some(ref sat) = self.persistent_sat {
            let sat_num_vars =
                u32::try_from(sat.total_num_vars()).expect("SAT solver num_vars does not fit u32");
            next_var = next_var.max(sat_num_vars + 1);
        }
        if let Some(ref sat) = self.lia_persistent_sat {
            let sat_num_vars =
                u32::try_from(sat.total_num_vars()).expect("SAT solver num_vars does not fit u32");
            next_var = next_var.max(sat_num_vars + 1);
        }

        self.tseitin_state.next_var = self.tseitin_state.next_var.max(next_var);
    }

    /// Drop encoded assertions that are no longer active in the SMT context.
    ///
    /// Definitional clauses remain global; only activation clauses are scoped.
    /// After pop, a previously encoded assertion may need to be re-activated when
    /// asserted again, so stale encoded entries must be removed.
    pub(crate) fn retain_encoded_assertions(&mut self, active_assertions: &[TermId]) {
        fn is_still_active(
            term: &TermId,
            active: &HashSet<TermId>,
            derived: &HashMap<TermId, LiaDerivedAssertionMetadata>,
        ) -> bool {
            active.contains(term)
                || derived.get(term).is_some_and(|meta| {
                    meta.source_sets
                        .iter()
                        .any(|sources| sources.iter().all(|source| active.contains(source)))
                })
        }

        if self.encoded_assertions.is_empty() && self.lia_encoded_assertions.is_empty() {
            return;
        }
        let active: HashSet<TermId> = active_assertions.iter().copied().collect();
        self.encoded_assertions
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        self.assertion_activation_scope
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        // #6853: Per-solver LIA encoding fields
        self.lia_encoded_assertions
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        self.lia_assertion_activation_scope
            .retain(|term, _| is_still_active(term, &active, &self.lia_derived_assertions));
        // Note: we do NOT prune lia_derived_assertions here. Its lifecycle is
        // managed by replace_lia_derived_assertions() which clears and
        // repopulates every check-sat. Pruning here would remove metadata for
        // new-but-not-yet-encoded assertions, causing desired_activation_depth()
        // to fall through to the wrong depth and produce permanent global
        // activation clauses that conflict with later scoped assertions (#6853).

        // Note: we do NOT drop the persistent SAT solver here. The SAT solver's
        // push/pop mechanism already deactivated the scoped activation clauses for
        // popped assertions. Global definition clauses remain but are harmless since
        // their root variables are not activated. The scope filter on the array axiom
        // generators (#6726) prevents phantom axioms from dead terms.
    }

    /// Apply any pending pushes to the SAT solver.
    /// Called after solver is created to sync scope state.
    pub(crate) fn apply_pending_pushes(&mut self) {
        if let Some(ref mut sat) = self.persistent_sat {
            for _ in 0..self.pending_push {
                sat.push();
            }
            self.pending_push = 0;
        }
    }

    /// Replace the currently active LIA-derived assertion metadata.
    pub(crate) fn replace_lia_derived_assertions<I>(&mut self, entries: I)
    where
        I: IntoIterator<Item = (TermId, usize, Vec<TermId>)>,
    {
        self.lia_derived_assertions.clear();
        for (term, activation_depth, mut sources) in entries {
            sources.sort_by_key(|source| source.index());
            sources.dedup();

            let meta = self.lia_derived_assertions.entry(term).or_insert_with(|| {
                LiaDerivedAssertionMetadata {
                    activation_depth,
                    source_sets: Vec::new(),
                }
            });
            meta.activation_depth = meta.activation_depth.min(activation_depth);
            if !meta.source_sets.contains(&sources) {
                meta.source_sets.push(sources);
            }
        }
    }

    /// Reset LIA-specific SAT solver and encoding state (#6853).
    ///
    /// LIA preprocessing can change the assertion set between check-sats.
    /// Accumulated global Tseitin definition clauses from prior check-sats
    /// over-constrain the variable space when combined with new activation
    /// clauses, causing false UNSAT. Resetting the LIA state before each
    /// check-sat ensures a clean encoding.
    pub(crate) fn reset_lia_sat(&mut self) {
        self.lia_persistent_sat = None;
        self.lia_encoded_assertions.clear();
        self.lia_assertion_activation_scope.clear();
        self.lia_tseitin_state = TseitinState::new();
    }

    /// Compute the activation depth for an assertion root clause.
    pub(crate) fn desired_activation_depth(
        &self,
        assertion: TermId,
        active_assertion_depths: &HashMap<TermId, usize>,
    ) -> usize {
        if let Some(meta) = self.lia_derived_assertions.get(&assertion) {
            return meta.activation_depth.min(self.scope_depth);
        }
        active_assertion_depths
            .get(&assertion)
            .copied()
            .or_else(|| self.pre_push_assertions.contains(&assertion).then_some(0))
            .unwrap_or(self.scope_depth)
            .min(self.scope_depth)
    }
}

impl IncrementalSubsystem for IncrementalTheoryState {
    fn push(&mut self) {
        self.scope_depth += 1;
        // #6853 fix: Each solver has its own Tseitin state. Advance
        // each state's next_var past the scope selector allocated by push()
        // so future Tseitin encoding avoids it.
        if let Some(ref mut sat) = self.persistent_sat {
            sat.push();
            let sat_total = u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            self.tseitin_state.next_var = self.tseitin_state.next_var.max(sat_total + 1);
        } else {
            self.pending_push += 1;
        }
        if let Some(ref mut sat) = self.lia_persistent_sat {
            sat.push();
            let sat_total = u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            self.lia_tseitin_state.next_var = self.lia_tseitin_state.next_var.max(sat_total + 1);
        }
    }

    fn pop(&mut self) -> bool {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
            if let Some(ref mut sat) = self.persistent_sat {
                let _ = sat.pop();
            } else if self.pending_push > 0 {
                self.pending_push -= 1;
            }
            if let Some(ref mut sat) = self.lia_persistent_sat {
                let _ = sat.pop();
            }
            // NeedLemmas replay is not scope-aware yet, so any pop can leave
            // the SAT solver without the scoped lemma clauses that were added
            // in the popped frame. Clear the replay ledger to avoid reapplying
            // stale lemmas into a fresh theory rebuild (#6720).
            self.theory_lemmas.clear();
            self.theory_lemma_keys.clear();
            self.original_clause_theory_proofs.clear();
            // Invalidate activation scope entries for assertions whose scoped
            // activation clauses were disabled by this pop. Only activations at
            // depth <= scope_depth survive (scope 0 activations are global and
            // always survive; deeper activations are scoped to their push level).
            // Without this, the re-activation check incorrectly skips assertions
            // that were first encoded at a deeper scope (#2822).
            self.assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            // #6853: LIA per-solver activation scopes
            self.lia_assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            // Popping any scope can disable activation clauses that were first added
            // in that popped frame. Re-assert on the next check-sat to restore them.
            self.needs_activation_reassert = true;
            true
        } else {
            false
        }
    }

    fn reset(&mut self) {
        self.persistent_sat = None;
        self.lia_persistent_sat = None;
        self.encoded_assertions.clear();
        self.assertion_activation_scope.clear();
        self.tseitin_state = TseitinState::new();
        self.lia_encoded_assertions.clear();
        self.lia_assertion_activation_scope.clear();
        self.lia_tseitin_state = TseitinState::new();
        self.clausification_proofs.clear();
        self.original_clause_theory_proofs.clear();
        self.theory_lemmas.clear();
        self.theory_lemma_keys.clear();
        self.scope_depth = 0;
        self.pending_push = 0;
        self.lia_derived_assertions.clear();
        self.theory_atoms.clear();
        self.pre_push_assertions.clear();
        self.needs_activation_reassert = false;
        self.theory_conflicts = 0;
        self.theory_propagations = 0;
        self.round_trips = 0;
        self.sat_solve_secs = 0.0;
        self.theory_sync_secs = 0.0;
        self.theory_check_secs = 0.0;
    }
}

/// Collect all theory atoms reachable from a set of assertion terms.
///
/// This performs a DFS traversal of each assertion term and collects all sub-terms
/// that are theory atoms (comparisons, equalities, etc.). Used by incremental solving
/// to determine which CNF variables should be synced to the theory solver - only atoms
/// that appear under active assertions should be synced (#338).
pub(crate) fn collect_active_theory_atoms(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashSet<TermId> {
    let mut active_atoms = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = Vec::new();

    for &term in assertions {
        if seen.insert(term) {
            stack.push(term);
        }
    }

    while let Some(term) = stack.pop() {
        // Check if this term is a theory atom
        if crate::is_theory_atom(terms, term) {
            active_atoms.insert(term);
        }
        // Continue traversing into children
        for child in terms.children(term) {
            if seen.insert(child) {
                stack.push(child);
            }
        }
    }

    // Bool-sorted terms that appear as arguments to UF applications must be
    // theory atoms so their truth values reach the EUF solver. Without this,
    // congruence closure cannot propagate through Bool-valued UF arguments
    // (e.g., Concat(y, n) vs Concat(z, n) where y,z are Bool). (#4610)
    // This mirrors the same scan in DpllT::from_tseitin_impl (lib.rs:899-928).
    for idx in 0..terms.len() {
        let term_id = TermId::new(idx as u32);
        if let TermData::App(z4_core::term::Symbol::Named(name), args) = terms.get(term_id) {
            match name.as_str() {
                "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => continue,
                _ => {}
            }
            if args.is_empty() {
                continue;
            }
            for &arg in args {
                if terms.sort(arg) == &Sort::Bool {
                    active_atoms.insert(arg);
                }
            }
        }
    }

    active_atoms
}
