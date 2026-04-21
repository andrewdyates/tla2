// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared DPLL(T) support types extracted from `lib.rs`.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
use z4_sat::{Literal, Solver as SatSolver, TlaTraceWriter, Variable};

/// Cached env flag for `Z4_DEBUG_DPLL` (checked once per process via `OnceLock`).
#[inline]
pub(crate) fn debug_dpll_enabled() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();
    *CACHE.get_or_init(|| std::env::var_os("Z4_DEBUG_DPLL").is_some())
}

/// Cached env flag for `Z4_DEBUG_SYNC` (checked once per process via `OnceLock`).
#[inline]
pub(crate) fn debug_sync_enabled() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();
    *CACHE.get_or_init(|| std::env::var_os("Z4_DEBUG_SYNC").is_some())
}

/// Iterate var->term mappings in deterministic variable order.
///
/// Internal storage uses `HashMap` for O(1)-amortized lookups, but model-to-theory
/// synchronization requires deterministic traversal for stable debugging/proof output.
pub(crate) fn iter_var_to_term_sorted(
    var_to_term: &HashMap<u32, TermId>,
) -> impl Iterator<Item = (u32, TermId)> {
    let mut pairs: Vec<(u32, TermId)> = var_to_term
        .iter()
        .map(|(&var, &term)| (var, term))
        .collect();
    pairs.sort_unstable_by_key(|(var, _)| *var);
    pairs.into_iter()
}

/// Convert a DIMACS literal (1-indexed, signed) to a `z4_sat::Literal` (0-indexed).
///
/// DIMACS convention: positive lit `n` → variable `n-1` positive,
/// negative lit `-n` → variable `n-1` negative. Lit 0 is invalid.
#[inline]
pub(crate) fn cnf_lit_to_sat(lit: i32) -> Literal {
    debug_assert_ne!(lit, 0, "Tseitin literal 0 is invalid");
    if lit > 0 {
        let var = Variable::new((lit - 1) as u32);
        Literal::positive(var)
    } else {
        let var = Variable::new((-lit - 1) as u32);
        Literal::negative(var)
    }
}

/// RAII guard for accumulating phase timing into a `Duration`.
///
/// Modeled on Z3's `scoped_watch` (`reference/z3/src/util/stopwatch.h:83`)
/// and CaDiCaL's `START`/`STOP` macros (`reference/cadical/src/profile.hpp:153`).
/// Accumulates elapsed wall time into the target `Duration` on drop.
pub(crate) struct PhaseTimer<'a> {
    target: &'a mut Duration,
    start: Instant,
}

impl<'a> PhaseTimer<'a> {
    #[inline]
    pub(crate) fn new(target: &'a mut Duration) -> Self {
        Self {
            target,
            start: Instant::now(),
        }
    }
}

impl Drop for PhaseTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        *self.target += self.start.elapsed();
    }
}

/// Construction-side timing breakdown for DPLL(T) setup work.
///
/// These counters are intentionally separate from solve-loop timings so
/// constructor-heavy benchmarks can distinguish setup cost from SAT/theory
/// round-trip cost.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllConstructionTimings {
    /// Total `from_tseitin_impl()` wall time.
    pub from_tseitin: Duration,
    /// Clause loading into the SAT solver.
    pub clause_load: Duration,
    /// Theory-atom discovery and deduplication.
    pub theory_atom_scan: Duration,
    /// Variable freezing plus initial theory internalization.
    pub freeze_internalize: Duration,
    /// `TheoryExtension::new()` atom registration and sorting.
    pub extension_register_atoms: Duration,
    /// Bound-axiom generation, materialization, and debug validation.
    pub extension_bound_axioms: Duration,
}

/// Timing breakdown for DPLL(T) solve calls (#4802).
///
/// Follows CaDiCaL's flat struct design (`reference/cadical/src/stats.hpp`)
/// with Z3's hierarchical naming (e.g., `time.spacer.solve.reach`).
/// Accumulates across all solve calls on the same `DpllT` instance.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllTimings {
    /// Total SAT solver time (`sat.solve()` calls)
    pub sat_solve: Duration,
    /// Total theory sync time (model communication to theory solver)
    pub theory_sync: Duration,
    /// Total theory check time (consistency + propagation checking)
    pub theory_check: Duration,
    /// DPLL(T) round-trip count (SAT → theory → SAT iterations)
    pub round_trips: u64,
}

/// Deterministic eager-extension counters for batching diagnostics.
///
/// Unlike wall-clock timings, these counters are stable across noisy machines
/// and directly measure whether the level-0 batching guard is active on a path.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllEagerStats {
    /// Number of `propagate()` calls observed by the eager extension.
    pub propagate_calls: u64,
    /// Number of early returns because theory state did not change.
    pub state_unchanged_skips: u64,
    /// Number of inline bound-refinement handoffs from theory to SAT replay.
    pub bound_refinement_handoffs: u64,
    /// Number of deferred theory checks due to batching.
    pub batch_defers: u64,
    /// Number of times batching was otherwise ready but blocked by `sat_level == 0`.
    pub level0_batch_guard_hits: u64,
    /// Number of eager theory checks executed at SAT decision level 0.
    pub level0_checks: u64,
    /// Number of theory lemma clauses injected inline during BCP (#6546).
    pub inline_lemma_clauses: u64,
}

impl DpllEagerStats {
    #[inline]
    pub(crate) fn accumulate_from(&mut self, other: &Self) {
        self.propagate_calls += other.propagate_calls;
        self.state_unchanged_skips += other.state_unchanged_skips;
        self.bound_refinement_handoffs += other.bound_refinement_handoffs;
        self.batch_defers += other.batch_defers;
        self.level0_batch_guard_hits += other.level0_batch_guard_hits;
        self.level0_checks += other.level0_checks;
        self.inline_lemma_clauses += other.inline_lemma_clauses;
    }
}

/// Split-loop-local solve timing accumulator.
///
/// Survives repeated fresh `DpllT::from_tseitin*()` rebuilds so the exported
/// `time.dpll.*` counters include every solver instance, not only the last one.
#[derive(Debug, Clone, Default)]
pub(crate) struct SplitLoopTimingStats {
    /// Sum of all DPLL(T) solve-call timings across split-loop rebuilds.
    pub dpll: DpllTimings,
    /// Wall time spent extracting theory models on SAT.
    pub model_extract: Duration,
    /// Wall time spent storing the final result/model back onto the executor.
    pub store_model: Duration,
    /// Total wall time for the entire split loop (#6503).
    pub total: Duration,
}

/// SAT-side state that can be preserved while rebuilding a DPLL(T) wrapper.
///
/// Used by string-theory CEGAR flows that need to mutate the term store
/// (allocate new split/skolem terms) between solver steps without discarding
/// SAT learned clauses and variable assignments.
pub(crate) struct DpllSatState {
    pub(crate) sat: SatSolver,
    pub(crate) var_to_term: HashMap<u32, TermId>,
    pub(crate) term_to_var: HashMap<TermId, u32>,
    pub(crate) theory_atoms: Vec<TermId>,
    pub(crate) theory_atom_set: HashSet<TermId>,
    pub(crate) debug_dpll: bool,
    pub(crate) debug_sync: bool,
    pub(crate) theory_conflict_count: u64,
    pub(crate) theory_propagation_count: u64,
    pub(crate) partial_clause_count: u64,
    pub(crate) eager_stats: DpllEagerStats,
    pub(crate) timings: DpllTimings,
    pub(crate) construction_timings: DpllConstructionTimings,
    pub(crate) diagnostic_trace: Option<crate::diagnostic_trace::DpllDiagnosticWriter>,
    pub(crate) dpll_tla_trace: Option<TlaTraceWriter>,
}

/// A simple empty theory solver for propositional logic.
pub(crate) struct PropositionalTheory;

impl TheorySolver for PropositionalTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {
        // No theory reasoning needed
    }

    fn check(&mut self) -> TheoryResult {
        // Propositional logic is always consistent
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // No propagations
        vec![]
    }

    fn push(&mut self) {
        // No state to push
    }

    fn pop(&mut self) {
        // No state to pop
    }

    fn reset(&mut self) {
        // Nothing to reset
    }
}
