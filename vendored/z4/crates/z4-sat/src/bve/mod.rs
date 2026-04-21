// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Variable Elimination (BVE)
//!
//! Implements variable elimination as an inprocessing technique.
//! For a variable x, we can eliminate it by:
//! 1. Collecting all clauses containing x (positive occurrences)
//! 2. Collecting all clauses containing ~x (negative occurrences)
//! 3. Computing all resolvents between positive and negative clauses
//! 4. If the total size of resolvents <= original clauses, eliminate x
//!
//! The "bounded" part ensures we only eliminate if it doesn't increase the
//! formula size too much (bounded by a growth limit).
//!
//! Reference: Een & Biere, "Effective Preprocessing in SAT through Variable
//! and Clause Elimination", SAT 2005.

use crate::clause::ClauseSignature;
use crate::elim_heap::ElimHeap;
use crate::kani_compat::DetHashMap;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

// Re-import for test module visibility (tests use `use super::*;`).
#[cfg(test)]
use crate::clause_arena::ClauseArena;

/// Maximum growth bound for BVE inprocessing.
/// CaDiCaL uses an adaptive bound (0→1→2→4→8→16) for inprocessing,
/// starting conservative and relaxing after successful rounds.
/// `fastelimbound=8` is only for preprocessing; inprocessing uses `elimboundmin=0`.
const BVE_GROWTH_BOUND_MAX: usize = 16;

/// Maximum total occurrences (pos+neg) for a variable to be considered for
/// elimination. Kissat uses `eliminateocclim=2000` applied to the sum of
/// positive and negative occurrences (resolve.c:282-289). CaDiCaL uses
/// `elimocclim=100` applied per-polarity (elim.cpp:698), which is much
/// more restrictive and causes Z4 to miss elimination opportunities on
/// formulas like mp1-klieber where many variables have 100-500 occurrences
/// per polarity but are profitably eliminable. Using Kissat's approach:
/// the resolvent_budget (clause-count bound) already prevents unprofitable
/// elimination, so the occurrence limit is only a pre-filter to avoid
/// wasting resolution effort.
const ELIM_OCC_LIMIT: usize = 2_000;

/// Maximum resolvent size in literals. If any single resolvent exceeds this,
/// the variable elimination is rejected. Matches CaDiCaL `elimclslim=100`
/// (options.hpp:89, elim.cpp:509).
const ELIM_CLAUSE_SIZE_LIMIT: usize = 100;

/// Statistics for BVE operations
#[derive(Debug, Clone, Default)]
#[allow(clippy::upper_case_acronyms)]
#[non_exhaustive]
pub struct BVEStats {
    /// Number of variables eliminated
    pub vars_eliminated: u64,
    /// Number of clauses removed (before resolvents added)
    pub clauses_removed: u64,
    /// Number of resolvents added
    pub resolvents_added: u64,
    /// Number of tautological resolvents skipped
    pub tautologies_skipped: u64,
    /// Resolution pairs where the 64-bit clause signature filter guaranteed
    /// no tautological resolvent, enabling the fast path that skips per-literal
    /// opposite-polarity mark checks (issue #7922).
    pub sig_fast_path: u64,
    /// Number of elimination rounds
    pub rounds: u64,
    /// Number of root-level-false literals pruned from resolvents
    pub root_literals_pruned: u64,
    /// Number of resolution pairs skipped because a parent was satisfied at root level
    pub root_satisfied_parents: u64,
    /// Number of double self-subsuming resolutions (CaDiCaL elim.cpp:413-424)
    pub double_otfs: u64,
    /// Number of single self-subsuming resolutions
    pub single_otfs: u64,
    /// Total literals across all non-unit resolvents (for average resolvent size tracking)
    pub total_resolvent_literals: u64,
    /// Count of non-unit resolvents added (excludes units, empties, OTFS)
    pub non_unit_resolvents: u64,
    /// Maximum resolvent length encountered
    pub max_resolvent_len: u64,
}

/// Outcome of attempting to resolve two clauses during BVE.
///
/// CaDiCaL `elim.cpp:292-359`: resolution checks `val(lit)` for each literal.
/// Root-level-true literals indicate a satisfied parent (garbage-collect it);
/// root-level-false literals are dropped from the resolvent.
pub(crate) enum ResolveOutcome {
    /// Non-tautological resolvent produced.
    /// Second field: variable indices of root-level-false literals pruned from
    /// the resolvent. The caller uses these to look up LRAT proof IDs for the
    /// unit clauses that falsified them (CaDiCaL elim.cpp:303-308).
    Resolvent(Vec<Literal>, Vec<usize>),
    /// Resolvent is tautological (contains both L and ~L).
    Tautology,
    /// A parent clause is satisfied at root level — skip this resolution pair.
    /// CaDiCaL: `elim_update_removed_clause` + `mark_garbage`.
    /// The boolean indicates which parent: `true` = first (positive) parent,
    /// `false` = second (negative) parent.
    ParentSatisfied(bool),
}

/// Result of attempting to eliminate a variable
#[derive(Debug, Clone)]
pub(crate) struct EliminationResult {
    /// The variable that was eliminated
    pub variable: Variable,
    /// Indices of clauses to delete (containing the eliminated variable)
    pub to_delete: Vec<usize>,
    /// Reconstruction witness entries for eliminated clauses.
    ///
    /// Each entry stores the exact witness literal that CaDiCaL would push on
    /// the extension stack for that clause, avoiding polarity inference during
    /// later reconstruction bookkeeping.
    pub witness_entries: Vec<WitnessEntry>,
    /// New resolvents: (lits, pos_ante_idx, neg_ante_idx, pruned_root_var_indices).
    /// The fourth element lists variable indices of root-level-false literals
    /// pruned from the resolvent; the caller maps them to LRAT proof IDs (#5071).
    pub resolvents: Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    /// Parent clauses that can be strengthened in-place (OTFS-style) instead
    /// of adding an equivalent resolvent.
    pub strengthened: Vec<ClauseStrengthening>,
    /// Parent clause indices detected as satisfied at root level during
    /// resolution checking. The caller marks these as garbage immediately
    /// (CaDiCaL elim.cpp:316-325).
    pub satisfied_parents: Vec<usize>,
    /// Whether elimination was performed
    pub eliminated: bool,
    /// Number of actual resolution pair attempts (CaDiCaL elim.cpp:271 parity).
    /// The caller charges this against the BVE resolution budget, NOT the
    /// theoretical pos*neg product.
    pub resolution_attempts: u64,
}

/// Witness metadata for one eliminated clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct WitnessEntry {
    /// Clause index (word offset) in the current ClauseArena.
    pub clause_idx: usize,
    /// Witness literal used to reconstruct this clause.
    pub witness: Literal,
}

/// Planned in-place strengthening for one parent clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClauseStrengthening {
    /// Clause index (word offset) in the current ClauseArena.
    pub clause_idx: usize,
    /// New literal list after removing the pivot from the parent clause.
    pub new_lits: Vec<Literal>,
    /// Antecedent clause indices that justify the strengthening (OTFS).
    /// The resolvent of these two clauses subsumes the original clause.
    /// Used for LRAT hint chain construction (#5149).
    pub pos_ante: usize,
    pub neg_ante: usize,
    /// Variable indices of root-level-false literals pruned from the
    /// resolvent. The LRAT hint chain for the strengthened clause must
    /// include the unit-clause proof IDs for these variables, matching
    /// CaDiCaL's `unit_id(-lit)` calls in `elim.cpp:303-308` (#5026).
    pub pruned_vars: Vec<usize>,
}

impl EliminationResult {
    /// Returns a "not eliminated" result for the given variable.
    fn not_eliminated(var: Variable) -> Self {
        Self {
            variable: var,
            to_delete: Vec::new(),
            witness_entries: Vec::new(),
            resolvents: Vec::new(),
            strengthened: Vec::new(),
            satisfied_parents: Vec::new(),
            eliminated: false,
            resolution_attempts: 0,
        }
    }
}

/// Occurrence list for BVE — uses the shared `OccList` type.
pub(crate) type BVEOccList = OccList;

/// Bounded Variable Elimination engine
#[allow(clippy::upper_case_acronyms)] // -D warnings overrides crate-level #![allow]
pub(crate) struct BVE {
    /// Occurrence lists
    occ: BVEOccList,
    /// Statistics
    stats: BVEStats,
    /// Number of variables
    num_vars: usize,
    /// Variables that have been eliminated (cannot be eliminated again)
    eliminated: Vec<bool>,
    /// Temporary buffer for resolvent computation
    resolvent_buf: Vec<Literal>,
    /// Var indices of root-level-false literals pruned from the last resolvent.
    /// Used by the caller to build LRAT hint chains (#5071).
    pruned_root_vars_buf: Vec<usize>,
    /// Reusable buffer for positive occurrence indices (avoids per-call allocations)
    pos_occ_buf: Vec<usize>,
    /// Reusable buffer for negative occurrence indices (avoids per-call allocations)
    neg_occ_buf: Vec<usize>,
    /// Per-variable score credit for structurally detected gates.
    ///
    /// A credit of `pos_gate * neg_gate` approximates the number of gate×gate
    /// resolution pairs skipped by restricted resolution. The heap subtracts it
    /// from the raw elimination score so gate-defined variables move up in the
    /// schedule without changing pure-literal priority.
    schedule_gate_pair_credit: Vec<u64>,
    /// Dynamic priority-queue schedule: indexed min-heap by elimination cost.
    /// CaDiCaL `heap<elim_more>`: cheapest variables popped first, scores
    /// updated mid-round as clauses are added/removed.
    schedule: ElimHeap,
    /// Pending inprocessing candidates whose occurrence counts changed since
    /// the last completed elimination phase.
    ///
    /// CaDiCaL uses per-variable `flags.elim` marks and only schedules marked
    /// variables in normal elimination rounds (`elim.cpp:830-846`). Without a
    /// similar filter, Z4 rebuilds the heap over all live variables on every
    /// BVE call, wasting the resolution budget on unchanged candidates.
    candidate_dirty: Vec<bool>,
    /// True after `build_schedule()` has been called since the last `rebuild()`.
    /// Prevents infinite re-builds when the heap drains without any successful
    /// elimination (failed variables are not re-inserted). Reset by `rebuild()`.
    schedule_built: bool,
    /// Adaptive growth bound for BVE (CaDiCaL elimboundmin→elimboundmax pattern).
    /// Starts at 0 (net-zero clause growth) and doubles after each successful round.
    growth_bound: usize,
    /// True when running preprocessing fast elimination (CaDiCaL fastelim):
    /// budget = min(growth_bound, clauses_removed).
    /// False in normal inprocessing mode:
    /// budget = clauses_removed + growth_bound.
    fastelim_mode: bool,
}

struct ResolveAcc<'a> {
    clauses_removed: usize,
    resolvents: &'a mut Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    strengthened: &'a mut Vec<ClauseStrengthening>,
    /// Maps clause_idx → index in `strengthened` for O(1) lookup (#5075).
    strengthened_idx: &'a mut DetHashMap<usize, usize>,
    found_empty_resolvent: &'a mut bool,
    /// CaDiCaL fastelim product shortcut (elimfast.cpp:85-88, :239):
    /// when `pos * neg <= budget`, the clause-count bound is trivially
    /// satisfied even if ALL resolvents are non-tautological. The per-pair
    /// clause-count early-abort is skipped, saving comparison overhead.
    clause_count_guaranteed: bool,
    /// Parent clause indices detected as satisfied at root level during
    /// resolution (CaDiCaL elim.cpp:316-325).
    satisfied_parents: &'a mut Vec<usize>,
}

type BoundedElimCheck = (
    bool,
    Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    Vec<ClauseStrengthening>,
    Vec<usize>,
    u64, // resolution_attempts: actual try_resolve_pair calls (CaDiCaL elim.cpp:271)
);

#[derive(Clone, Copy)]
struct ResolveClauseProfile {
    clause_idx: usize,
    signature: ClauseSignature,
    tautological: bool,
}

impl BVE {
    /// Create a new BVE engine for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            occ: BVEOccList::new(num_vars),
            stats: BVEStats::default(),
            num_vars,
            eliminated: vec![false; num_vars],
            resolvent_buf: Vec::new(),
            pruned_root_vars_buf: Vec::new(),
            pos_occ_buf: Vec::new(),
            neg_occ_buf: Vec::new(),
            schedule_gate_pair_credit: vec![0; num_vars],
            schedule: ElimHeap::new(num_vars),
            candidate_dirty: vec![false; num_vars],
            schedule_built: false,
            growth_bound: 0,
            fastelim_mode: false,
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    ///
    /// ENSURES: self.num_vars >= num_vars, eliminated buffer sized accordingly
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        self.occ.ensure_num_vars(num_vars);
        self.schedule.ensure_num_vars(num_vars);
        if self.eliminated.len() < num_vars {
            self.eliminated.resize(num_vars, false);
        }
        if self.schedule_gate_pair_credit.len() < num_vars {
            self.schedule_gate_pair_credit.resize(num_vars, 0);
        }
        if self.candidate_dirty.len() < num_vars {
            self.candidate_dirty.resize(num_vars, false);
        }

        debug_assert!(
            self.eliminated.len() >= num_vars,
            "BUG: ensure_num_vars({num_vars}) failed: eliminated={}",
            self.eliminated.len()
        );
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &BVEStats {
        &self.stats
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the BVE engine via `BVE::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: BVEStats) {
        self.stats = stats;
    }

    /// Whether we're in fastelim (preprocessing) mode.
    /// CaDiCaL parity: fastelim does NOT use gate detection.
    pub(crate) fn is_fastelim_mode(&self) -> bool {
        self.fastelim_mode
    }

    /// Check if a variable has been eliminated
    #[cfg(test)]
    pub(crate) fn is_eliminated(&self, var: Variable) -> bool {
        let idx = var.index();
        idx < self.eliminated.len() && self.eliminated[idx]
    }

    /// Mark a variable as eliminated in BVE's internal tracking, without
    /// performing actual BVE elimination. Called by decompose/sweep when
    /// a variable is substituted, so that subsequent BVE rounds skip it.
    /// Without this, substituted variables leak through next_candidate()
    /// because BVE's eliminated[] flag is not synchronized with var_lifecycle.
    pub(crate) fn mark_removed_external(&mut self, var_idx: usize) {
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = true;
            self.candidate_dirty[var_idx] = false;
        }
    }

    /// Clear the BVE eliminated flag for a variable that is being reactivated.
    /// Called during incremental reset when variables that were eliminated by BVE
    /// need to be restored for the next solve cycle.
    pub(crate) fn clear_removed_external(&mut self, var_idx: usize) {
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = false;
        }
    }

    /// Get occurrence list for a literal.
    pub(crate) fn get_occs(&self, lit: Literal) -> &[usize] {
        self.occ.get(lit)
    }
}

mod eliminate;
mod occs;
mod resolve;
mod schedule;

#[cfg(test)]
mod tests;
