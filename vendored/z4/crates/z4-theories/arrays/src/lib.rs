// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 Arrays - Array theory solver
//!
//! Implements the theory of arrays using the standard axioms:
//! - Read-over-write (same index): select(store(a, i, v), i) = v
//! - Read-over-write (different index): i ≠ j → select(store(a, i, v), j) = select(a, j)
//! - Extensionality: (∀i. select(a, i) = select(b, i)) → a = b
//!
//! This solver works in conjunction with EUF for equality reasoning.

#![warn(missing_docs)]
#![warn(clippy::all)]

mod theory_check;
mod theory_impl;
mod theory_propagate;

mod axiom_checkers;
mod axiom_store_checks;
mod bridge;
mod equality;
mod equality_query;
mod final_check;
mod incremental;
mod model;
mod propagation;
mod store_chain;

pub(crate) use bridge::SelectResolution;
pub use bridge::UndecidedIndexPair;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use std::cell::RefCell;
use std::rc::Rc;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData, TermId, TermStore};

/// A store chain entry: (array_term, base_array, effective_stores as (index, value) pairs).
type StoreChainEntry = (TermId, TermId, Vec<(TermId, TermId)>);

use z4_core::{
    DiscoveredEquality, EqualityPropagationResult, ModelEqualityRequest, Sort, TheoryLemma,
    TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};

/// Interpretation of a single array in the model
#[derive(Debug, Clone, Default)]
pub struct ArrayInterpretation {
    /// Default value for all indices (if this is a const-array or has a known default)
    pub default: Option<String>,
    /// Explicit index-value mappings (from store operations)
    pub stores: Vec<(String, String)>,
    /// Index sort for formatting
    pub index_sort: Option<Sort>,
    /// Element sort for formatting
    pub element_sort: Option<Sort>,
}

/// Model for array theory - maps array terms to their interpretations
#[derive(Debug, Clone, Default)]
pub struct ArrayModel {
    /// Maps array term IDs to their interpretations
    pub array_values: HashMap<TermId, ArrayInterpretation>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ArrayVarData {
    /// `store(a, i, v)` terms whose result array is this term.
    stores_as_result: Vec<TermId>,
    /// `select(a, j)` terms reading from this array term.
    parent_selects: Vec<TermId>,
    /// `store(a, i, v)` terms whose base array is this term.
    parent_stores: Vec<TermId>,
    /// Whether delayed upward ROW2 work may be needed for this array term.
    prop_upward: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingAxiom {
    /// Downward ROW2 work for one `(store, select)` pair.
    Row2Down { store: TermId, select: TermId },
}

/// Array theory solver
///
/// Implements McCarthy's theory of arrays with the following axioms:
/// 1. ROW1 (read-over-write same): select(store(a, i, v), i) = v
/// 2. ROW2 (read-over-write diff): i ≠ j → select(store(a, i, v), j) = select(a, j)
/// 3. Extensionality: a ≠ b → ∃i. select(a, i) ≠ select(b, i)
pub struct ArraySolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Current assignments: term -> bool
    assigns: HashMap<TermId, bool>,
    /// Trail for backtracking: (term, previous_value)
    trail: Vec<(TermId, Option<bool>)>,
    /// Scope markers (trail positions)
    scopes: Vec<usize>,
    /// Cache of select terms: select_term -> (array, index)
    select_cache: HashMap<TermId, (TermId, TermId)>,
    /// Exact select lookup: `(array_term, index_term) -> select_term`.
    /// Used by hot ROW2/self-store paths to avoid rescanning `parent_selects`
    /// when they need the syntactic `select(array, index)` term.
    select_pair_index: HashMap<(TermId, TermId), TermId>,
    /// Cache of store terms: store_term -> (array, index, value)
    store_cache: HashMap<TermId, (TermId, TermId, TermId)>,
    /// Cache of const-array terms: const_array_term -> default_value
    const_array_cache: HashMap<TermId, TermId>,
    /// Equality terms we track: eq_term -> (lhs, rhs)
    equality_cache: HashMap<TermId, (TermId, TermId)>,
    /// Reverse index: term -> equality terms involving that term.
    /// Maintained in sync with `equality_cache` for O(1) lookup in
    /// `register_store` (#6820).
    term_to_equalities: HashMap<TermId, Vec<TermId>>,
    /// Dirty flag for a full cache rebuild.
    dirty: bool,
    /// Number of terms already scanned into the term caches.
    populated_terms: usize,
    /// Per-array incremental tracking for ROW2 registration (#6282 packet 1).
    array_vars: HashMap<TermId, ArrayVarData>,
    /// Equality-driven `array_vars` merges performed by `notify_equality`.
    /// Replayed in debug invariant checks so `array_vars` can legitimately be
    /// richer than the raw structural term caches after cross-theory equality
    /// notifications (#6703).
    array_var_merge_log: Vec<(TermId, TermId)>,
    /// Deduplicates repeated ROW2 registrations by `(store_term, select_index)`.
    axiom_fingerprints: HashSet<(TermId, TermId)>,
    /// Exact ROW2 fingerprint indices recorded per store term.
    ///
    /// Unlike Z3's enode-root fingerprints, these remain exact `TermId`s so a
    /// fingerprint inserted under a branch-local equality does not suppress a
    /// distinct-index branch after backtracking. `queue_row2_down_axiom()`
    /// consults the current equality graph against this exact history to avoid
    /// re-queuing alias-equivalent ROW2 work.
    row2_fingerprint_indices: HashMap<TermId, Vec<TermId>>,
    /// Incrementally registered ROW2 work. Packet 2 consumes this queue.
    pending_axioms: Vec<PendingAxiom>,
    /// Axioms blocked on missing equality atoms. Moved back to `pending_axioms`
    /// only when new terms are created (`populated_terms` increases), since new
    /// equality atoms can only appear via term registration (#6820).
    blocked_axioms: Vec<PendingAxiom>,
    /// The `populated_terms` count when `blocked_axioms` were last examined.
    /// If `populated_terms == blocked_axiom_term_gen`, blocked axioms are
    /// still blocked and need not be re-examined.
    blocked_axiom_term_gen: usize,
    /// Event-driven const-array read candidates: `(select_term, const_array_term)`.
    /// Populated in `register_select()` and `notify_equality()`.
    /// Drained in `check_const_array_read()` instead of scanning `select_cache`.
    pending_const_reads: Vec<(TermId, TermId)>,
    /// Event-driven ROW1 (read-hit) candidates: `(select_term, store_term)`.
    /// Populated at the same three points as ROW2 down axioms:
    /// - `register_select()`: select's syntactic array has `stores_as_result`
    /// - `register_store()`: store term has existing `parent_selects`
    /// - `notify_equality()`: cross-product of merged equivalence classes
    ///
    /// Drain semantics: on each `check_row1()`, drain the queue. Pairs where
    /// indices are equal but no conflict is detected yet (because the
    /// disequality on values hasn't been propagated) are RETAINED for future
    /// re-checking. Pairs with non-matching indices are discarded (handled by
    /// ROW2). Cleared on `pop()` and `clear_term_caches()`.
    pending_row1: Vec<(TermId, TermId)>,
    /// Event-driven ROW2 upward (axiom 2b) candidates: `(select_term, store_term)`.
    /// Populated at the same three points as other event-driven queues:
    /// - `register_select()`: select's array has `parent_stores` (upward direction)
    /// - `register_store()`: store's base array has existing `parent_selects`
    /// - `notify_equality()`: cross parent_stores × parent_selects
    ///
    /// ROW2 upward propagates selects from base arrays "up" to store results:
    /// `select(A, j) = select(store(A,i,v), j)` when `i ≠ j`.
    /// Drained in `check_row2_upward_with_guidance()` instead of scanning
    /// `select_cache`. Cleared on `pop()` and `clear_term_caches()`.
    pending_row2_upward: Vec<(TermId, TermId)>,
    /// Event-driven self-store candidates: `(eq_term, store_term)`.
    /// Populated when an equality involving a store term is assigned true
    /// (`record_assignment`) or when a new store/equality is registered.
    /// `check_self_store()` drains this queue instead of scanning
    /// `equality_cache`. Cleared on `pop()` and `clear_term_caches()`.
    pending_self_store: Vec<(TermId, TermId)>,
    /// Permanent theory lemmas already applied to the SAT solver.
    applied_theory_lemmas: HashSet<Vec<TheoryLit>>,
    /// When true, expensive O(n²) checks (ROW2 upward, ROW2 extended, nested
    /// select conflicts) are deferred from `check()` to `final_check()`. Set by
    /// combined solvers that call `final_check()` at fixpoint (#6282 Packet 2).
    defer_expensive_checks: bool,
    /// Deduplicates NeedModelEquality requests from `check_row2_upward_with_guidance`.
    /// Prevents the same undecided index pair from being requested repeatedly,
    /// which would cause an infinite loop in the N-O fixpoint (#6282 Phase A).
    /// Cleared on `soft_reset()`.
    requested_model_eqs: HashSet<(TermId, TermId)>,

    // === Indexed data structures (rebuilt from equality_cache + assigns) ===
    /// Map from unordered term pair to equality term: {min(a,b), max(a,b)} -> eq_term
    eq_pair_index: HashMap<(TermId, TermId), TermId>,
    /// Set of unordered term pairs asserted distinct: {min(a,b), max(a,b)}
    diseq_set: HashSet<(TermId, TermId)>,
    /// Adjacency list for true equalities: term -> [(other_term, eq_term)]
    eq_adj: HashMap<TermId, Vec<(TermId, TermId)>>,
    /// Whether the assignment-derived indices need a full rebuild.
    assign_dirty: bool,
    /// Equality atoms assigned before `register_term()` sees them while the
    /// caches are otherwise warm. Drained after the next incremental term scan
    /// so `eq_adj` / `diseq_set` can be updated without a full rebuild.
    pending_registered_equalities: Vec<TermId>,
    /// Monotonic version for equality-graph connectivity updates.
    /// Bumped only when `eq_adj`'s connected components can change.
    eq_adj_version: u64,
    /// External disequalities injected by the combined solver (e.g., from LIA).
    /// These survive `rebuild_assign_indices()` and are merged into `diseq_set` (#4665).
    external_diseqs: HashSet<(TermId, TermId)>,
    /// Reason-carrying external disequalities from arithmetic tight bounds (#6546).
    /// When present, `explain_distinct_if_provable()` can justify ROW2 store-chain
    /// skips for these pairs. Only non-empty, deduplicated reason vectors are stored.
    external_diseq_reasons: HashMap<(TermId, TermId), Vec<TheoryLit>>,
    /// External equalities injected by the combined solver (e.g., from LIA).
    /// These survive `rebuild_assign_indices()` and are merged into `eq_adj` (#4665).
    external_eqs: Vec<(TermId, TermId)>,
    /// Equalities already reported via `propagate_equalities()`.
    /// Prevents the N-O fixpoint loop from re-discovering the same equality
    /// every iteration (#5121). Cleared on `pop()`.
    sent_equalities: HashSet<(TermId, TermId)>,
    /// Propagations already emitted in the current scope.
    /// Prevents the eager theory extension from re-processing the exact same
    /// implication clause on every call when the justification has not changed.
    sent_propagations: HashSet<(TheoryLit, Vec<TheoryLit>)>,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    /// Cached equivalence class map for the current `eq_adj_version`.
    /// Reused across repeated `check()` / `final_check()` calls until the
    /// equality graph connectivity changes.
    equiv_class_map: HashMap<TermId, usize>,
    /// Cached equivalence class members for the current `eq_adj_version`.
    equiv_classes: Vec<Vec<TermId>>,
    /// `eq_adj_version` that last populated `equiv_class_map` / `equiv_classes`.
    equiv_class_cache_version: Option<u64>,
    #[cfg(test)]
    /// Regression-only counter used to assert that repeated `check()` calls do
    /// not rebuild the equivalence cache when the equality graph is unchanged.
    equiv_class_cache_builds: u64,
    #[cfg(test)]
    /// Regression-only counter used to assert that warm-cache equality updates
    /// do not force full `eq_adj` / `diseq_set` reconstruction.
    assign_index_rebuilds: u64,
    /// Snapshot of `(eq_adj_version, select_cache.len(), store_cache.len(),
    /// external_diseqs.len(), external_eqs.len(), diseq_set.len())` at the last
    /// `propagate_equalities()` call. When the snapshot matches the current
    /// state, the method short-circuits to an empty result because no new
    /// equalities can be discovered (#6546).
    prop_eq_snapshot: Option<(u64, usize, usize, usize, usize, usize)>,
    /// Snapshot of `(eq_adj_version, diseq_set.len(), select_cache.len(),
    /// store_cache.len(), requested_model_eqs.len())` at the last `final_check()`
    /// call that returned `Sat` (all sub-checks passed). When the snapshot
    /// matches the current state, `final_check` short-circuits because no new
    /// conflicts, lemmas, or model equality requests can be discovered (#6546).
    final_check_snapshot: Option<(u64, usize, usize, usize, usize)>,
    final_check_call_count: u64,
    /// Memoized affine Int normal forms keyed by the immutable term DAG.
    ///
    /// The parse result depends only on `terms`, not on solver assignments, so
    /// it is safe to retain across scopes and repeated `propagate()` calls.
    affine_int_expr_cache: RefCell<HashMap<TermId, Option<Rc<AffineIntExpr>>>>,
}

type AffineIntExpr = (HashMap<String, BigInt>, BigInt);

impl<'a> ArraySolver<'a> {
    /// Create a new array solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        ArraySolver {
            terms,
            assigns: HashMap::new(),
            trail: Vec::new(),
            scopes: Vec::new(),
            select_cache: HashMap::new(),
            select_pair_index: HashMap::new(),
            store_cache: HashMap::new(),
            const_array_cache: HashMap::new(),
            equality_cache: HashMap::new(),
            term_to_equalities: HashMap::new(),
            dirty: true,
            populated_terms: 0,
            array_vars: HashMap::new(),
            array_var_merge_log: Vec::new(),
            axiom_fingerprints: HashSet::new(),
            row2_fingerprint_indices: HashMap::new(),
            pending_axioms: Vec::new(),
            blocked_axioms: Vec::new(),
            blocked_axiom_term_gen: 0,
            pending_const_reads: Vec::new(),
            pending_row1: Vec::new(),
            pending_row2_upward: Vec::new(),
            pending_self_store: Vec::new(),
            applied_theory_lemmas: HashSet::new(),
            defer_expensive_checks: false,
            requested_model_eqs: HashSet::new(),
            eq_pair_index: HashMap::new(),
            diseq_set: HashSet::new(),
            eq_adj: HashMap::new(),
            assign_dirty: true,
            pending_registered_equalities: Vec::new(),
            eq_adj_version: 0,
            external_diseqs: HashSet::new(),
            external_diseq_reasons: HashMap::new(),
            external_eqs: Vec::new(),
            sent_equalities: HashSet::new(),
            sent_propagations: HashSet::new(),
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            equiv_class_map: HashMap::new(),
            equiv_classes: Vec::new(),
            equiv_class_cache_version: None,
            #[cfg(test)]
            equiv_class_cache_builds: 0,
            #[cfg(test)]
            assign_index_rebuilds: 0,
            prop_eq_snapshot: None,
            final_check_snapshot: None,
            final_check_call_count: 0,
            affine_int_expr_cache: RefCell::new(HashMap::new()),
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
