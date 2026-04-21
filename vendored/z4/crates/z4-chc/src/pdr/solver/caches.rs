// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Centralized cache subsystem for PdrSolver (#3590).
//!
//! All revision-sensitive and bounded caches live here.  `PdrCacheStore`
//! provides coordinated invalidation (`clear_on_restart`, per-field caps)
//! and keeps the parent `PdrSolver` struct focused on algorithmic state.

use std::cell::RefCell;
use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{ChcExpr, ChcVar, PredicateId};

use super::super::implication_cache::ImplicationCache;
use super::super::lemma_cluster::ClusterStore;

// ── Capacity limits (memory defense, #2780) ────────────────────────────────

const MAX_PUSH_CACHE_ENTRIES: usize = 50_000;
const MAX_SELF_INDUCTIVE_CACHE_ENTRIES: usize = 50_000;
const MAX_BLOCKS_INIT_CACHE_ENTRIES: usize = 25_000;
const MAX_INDUCTIVE_BLOCKING_CACHE_ENTRIES: usize = 50_000;
const MAX_CUMULATIVE_CONSTRAINT_CACHE_ENTRIES: usize = 10_000;
const MAX_SPURIOUS_CEX_WEAKNESS_ENTRIES: usize = 20_000;
const MAX_CLAUSE_GUARDED_KEYS: usize = 4_096;
const MAX_DISEQ_VALUES_ENTRIES: usize = 10_000;

// ── PdrCacheStore ──────────────────────────────────────────────────────────

/// Consolidated cache subsystem for `PdrSolver`.
///
/// Groups all revision-sensitive, bounded, and static caches into a single
/// struct with coordinated invalidation and capacity enforcement.
pub(in crate::pdr) struct PdrCacheStore {
    // ── Static lookups (computed once at init, never modified) ──────────
    /// Canonical variables for each predicate's arguments.
    pub predicate_vars: FxHashMap<PredicateId, Vec<ChcVar>>,
    /// For each predicate P, the body predicates P's transitions depend on.
    pub push_cache_deps: FxHashMap<PredicateId, Vec<PredicateId>>,
    /// Inverse of `push_cache_deps`: which predicates use P in their body.
    pub predicate_users: FxHashMap<PredicateId, Vec<PredicateId>>,
    /// Predicates that have fact clauses (init rules).
    pub predicates_with_facts: FxHashSet<PredicateId>,
    /// Predicates transitively reachable from init via transitions.
    pub reachable_predicates: FxHashSet<PredicateId>,

    // ── Dynamic caches (revision/frame-dependent, bounded) ─────────────
    /// Lemma push checks: `(level, pred_idx, formula_hash) -> (expr, sig, can_push)`.
    /// Collision safety (#2860): stores full `ChcExpr` for verification.
    pub push_cache: FxHashMap<(usize, usize, u64), (ChcExpr, u64, bool)>,
    /// Self-inductiveness checks: `(pred, hash) -> (expr, frame1_rev, is_self_inductive)`.
    pub self_inductive_cache: FxHashMap<(PredicateId, u64), (ChcExpr, u64, bool)>,
    /// Blocks-initial-states checks: `(pred, hash) -> (expr, blocks_all)`.
    /// Monotonic (facts don't change).
    pub blocks_init_cache: FxHashMap<(PredicateId, u64), (ChcExpr, bool)>,
    /// Inductive-blocking checks: `(pred, level, hash) -> (expr, lemma_count, result)`.
    pub inductive_blocking_cache: FxHashMap<(PredicateId, usize, u64), (ChcExpr, usize, bool)>,
    /// Init-only value checks: `(pred, var_name, value) -> (frame1_rev, is_init_only)`.
    pub init_only_value_cache: FxHashMap<(PredicateId, String, i64), (u64, bool)>,
    /// Cumulative frame constraint: `(level, pred) -> (revision_sum, formula)`.
    /// Uses `RefCell` because callers need `&self` access.
    pub cumulative_constraint_cache: RefCell<FxHashMap<(usize, PredicateId), (u64, ChcExpr)>>,
    /// Per-predicate Entry-CEGAR refinement budget.
    pub entry_cegar_budget: FxHashMap<PredicateId, usize>,
    /// Disequality values per `(pred, var, level)` for enumeration detection.
    pub diseq_values: FxHashMap<(PredicateId, String, usize), Vec<i64>>,
    /// Spurious CEX weakness per `(pred, root_state_hash)`.
    pub spurious_cex_weakness: FxHashMap<(PredicateId, u64), u8>,
    /// Blocked states for convex closure per predicate.
    pub blocked_states_for_convex: FxHashMap<PredicateId, VecDeque<FxHashMap<String, i64>>>,
    /// Clause-guarded propagated lemmas: `(target_pred, clause_idx) -> [(expr, max_level)]`.
    pub clause_guarded_lemmas: FxHashMap<(PredicateId, usize), Vec<(ChcExpr, usize)>>,
    /// LAWI-style model-guided implication cache.
    pub implication_cache: ImplicationCache,
    /// Lemma cluster store for global generalization.
    pub cluster_store: ClusterStore,
}

impl PdrCacheStore {
    /// Create a cache store with pre-computed static lookups.
    ///
    /// Static lookups are computed once during `PdrSolver::new()` from the
    /// CHC problem and never modified afterwards.  Dynamic caches start empty.
    pub(crate) fn new(
        predicate_vars: FxHashMap<PredicateId, Vec<ChcVar>>,
        push_cache_deps: FxHashMap<PredicateId, Vec<PredicateId>>,
        predicate_users: FxHashMap<PredicateId, Vec<PredicateId>>,
        predicates_with_facts: FxHashSet<PredicateId>,
        reachable_predicates: FxHashSet<PredicateId>,
    ) -> Self {
        Self {
            predicate_vars,
            push_cache_deps,
            predicate_users,
            predicates_with_facts,
            reachable_predicates,
            push_cache: FxHashMap::default(),
            self_inductive_cache: FxHashMap::default(),
            blocks_init_cache: FxHashMap::default(),
            inductive_blocking_cache: FxHashMap::default(),
            init_only_value_cache: FxHashMap::default(),
            cumulative_constraint_cache: RefCell::new(FxHashMap::default()),
            entry_cegar_budget: FxHashMap::default(),
            diseq_values: FxHashMap::default(),
            spurious_cex_weakness: FxHashMap::default(),
            blocked_states_for_convex: FxHashMap::default(),
            clause_guarded_lemmas: FxHashMap::default(),
            implication_cache: ImplicationCache::new(),
            cluster_store: ClusterStore::new(),
        }
    }

    /// Clear all revision-dependent caches on solver restart (#1270).
    ///
    /// Caches that survive restart:
    /// - `blocks_init_cache` (facts never change)
    /// - `implication_cache` (countermodels remain valid)
    /// - `clause_guarded_lemmas` (propagated lemmas survive restarts)
    /// - `entry_cegar_budget` (budget depletion is permanent)
    /// - All static lookups
    pub(crate) fn clear_on_restart(&mut self) {
        self.push_cache.clear();
        self.self_inductive_cache.clear();
        self.inductive_blocking_cache.clear();
        self.init_only_value_cache.clear();
        self.cumulative_constraint_cache.borrow_mut().clear();
        self.spurious_cex_weakness.clear();
        self.blocked_states_for_convex.clear();
        self.diseq_values.clear();
    }

    /// Bounded insert: if `cache` is at capacity and key is new, clear and re-insert.
    ///
    /// Simple "clear everything on overflow" strategy — avoids LRU complexity.
    #[inline]
    pub(crate) fn bounded_insert<K, V>(cache: &mut FxHashMap<K, V>, key: K, value: V, cap: usize)
    where
        K: std::hash::Hash + Eq,
    {
        if cache.len() >= cap && !cache.contains_key(&key) {
            cache.clear();
        }
        cache.insert(key, value);
    }

    // ── Per-cache cap accessors ────────────────────────────────────────

    pub(crate) const fn push_cache_cap() -> usize {
        MAX_PUSH_CACHE_ENTRIES
    }
    pub(crate) const fn self_inductive_cache_cap() -> usize {
        MAX_SELF_INDUCTIVE_CACHE_ENTRIES
    }
    pub(crate) const fn blocks_init_cache_cap() -> usize {
        MAX_BLOCKS_INIT_CACHE_ENTRIES
    }
    pub(crate) const fn inductive_blocking_cache_cap() -> usize {
        MAX_INDUCTIVE_BLOCKING_CACHE_ENTRIES
    }
    pub(crate) const fn cumulative_constraint_cache_cap() -> usize {
        MAX_CUMULATIVE_CONSTRAINT_CACHE_ENTRIES
    }
    pub(crate) const fn spurious_cex_weakness_cap() -> usize {
        MAX_SPURIOUS_CEX_WEAKNESS_ENTRIES
    }
    pub(crate) const fn clause_guarded_keys_cap() -> usize {
        MAX_CLAUSE_GUARDED_KEYS
    }
    pub(crate) const fn diseq_values_cap() -> usize {
        MAX_DISEQ_VALUES_ENTRIES
    }
}
