// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Type definitions for the eager DPLL(T) theory extension.
//!
//! Contains the `TheoryExtension` struct, helper types, and the debug
//! formatting utility. Extracted from `mod.rs` (#5970 code-health splits).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use std::cell::Cell;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    BoundRefinementRequest, FarkasAnnotation, TermData, TermId, TermStore, TheorySolver,
};
use z4_sat::Literal;

use crate::diagnostic_trace::DpllDiagnosticWriter;
use crate::executor::BoundRefinementReplayKey;
use crate::proof_tracker::ProofTracker;
use crate::DpllEagerStats;

/// Recursively format a term for debugging (up to `depth` levels).
pub(super) fn format_term_recursive(terms: &TermStore, term: TermId, depth: u32) -> String {
    if depth == 0 {
        return format!("{term:?}");
    }
    match terms.get(term) {
        TermData::Const(c) => format!("{c:?}"),
        TermData::Var(name, _sort) => name.clone(),
        TermData::App(sym, args) => {
            let arg_strs: Vec<String> = args
                .iter()
                .map(|&a| format_term_recursive(terms, a, depth - 1))
                .collect();
            format!("({} {})", sym.name(), arg_strs.join(" "))
        }
        TermData::Not(inner) => {
            format!("(not {})", format_term_recursive(terms, *inner, depth - 1))
        }
        other => format!("{other:?}"),
    }
}

/// Stable key for deduplicating binary bound-ordering axioms across
/// incremental eager-extension iterations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TheoryAxiomKey {
    first: (TermId, bool),
    second: (TermId, bool),
}

impl TheoryAxiomKey {
    pub(crate) fn new(t1: TermId, p1: bool, t2: TermId, p2: bool) -> Self {
        let first = (t1, p1);
        let second = (t2, p2);
        if second < first {
            Self {
                first: second,
                second: first,
            }
        } else {
            Self { first, second }
        }
    }
}

pub(super) enum BoundRefinementHandoff<'a> {
    FinalCheckOnly,
    StopAndReplayInline {
        known_replays: &'a HashSet<BoundRefinementReplayKey>,
    },
}

/// Wrapper that adapts a TheorySolver to the Extension trait for eager DPLL(T)
pub(crate) struct TheoryExtension<'a, T: TheorySolver> {
    /// The theory solver
    pub(super) theory: &'a mut T,
    /// Term store (optional) for semantic verification.
    pub(super) terms: Option<&'a TermStore>,
    /// Mapping from SAT variables to term IDs
    pub(super) var_to_term: &'a HashMap<u32, TermId>,
    /// Mapping from term IDs to SAT variables
    pub(super) term_to_var: &'a HashMap<TermId, u32>,
    /// Theory atoms (terms the theory cares about, stable order + unique)
    pub(super) theory_atoms: &'a [TermId],
    /// Membership set for O(1) theory-atom checks.
    pub(super) theory_atom_set: &'a HashSet<TermId>,
    /// Last trail position we processed
    pub(super) last_trail_pos: usize,
    /// Current theory push level (incremented on each push)
    pub(super) theory_level: u32,
    /// Debug mode
    pub(super) debug: bool,
    /// Optional DPLL(T) diagnostic writer for eager interaction events.
    pub(super) diagnostic_trace: Option<&'a DpllDiagnosticWriter>,
    pub(super) proof: Option<ProofContext<'a>>,
    /// Count of theory conflicts encountered during eager solving (#4705).
    pub(super) theory_conflict_count: u64,
    /// Count of theory propagation clauses added during eager solving (#4705).
    pub(super) theory_propagation_count: u64,
    /// Count of partial clause events where `term_to_literal` dropped terms (#5000).
    pub(super) partial_clause_count: u64,
    /// Pending split/lemma request from the theory solver (#4919).
    /// Stored here instead of panicking so that eager mode can be used with
    /// theories that produce splits at full-model time (LRA, LIA, strings).
    /// The executor retrieves this via `take_pending_split()`.
    pub(super) pending_split: Option<z4_core::TheoryResult>,
    /// Pending bound-refinement requests discovered during final theory check.
    pub(super) pending_bound_refinements: Vec<BoundRefinementRequest>,
    /// Trail positions saved at each push level (#5548).
    /// On backtrack, `last_trail_pos` is restored from this stack instead of
    /// being reset to 0, avoiding O(trail × backtracks) redundant re-assertions.
    pub(super) level_trail_positions: Vec<usize>,
    /// Whether theory.check() has been called at least once (#4919).
    /// The first call must always run to detect initial-state conflicts.
    pub(super) has_checked: bool,
    /// Index into `theory_atoms` for theory-aware branching (#4919).
    /// On each `suggest_decision` call, scan from this index for the first
    /// unassigned theory atom. This ensures theory atoms are decided before
    /// Tseitin encoding variables, matching Z3's `theory_aware_branching`.
    /// Reference: Z3 smt_case_split_queue.cpp:1170-1209.
    pub(super) theory_decision_idx: Cell<usize>,
    /// Bound ordering axiom clauses to inject on the first propagate() call.
    /// Generated from Z3's mk_bound_axioms algorithm: for each pair of
    /// nearest-neighbor bounds on the same variable, add a binary SAT clause
    /// encoding their implication. This moves bound propagation from the theory
    /// solver (O(n) round-trips) to BCP (O(1) unit propagation). (#4919)
    pub(super) pending_axiom_clauses: Vec<Vec<Literal>>,
    /// Term-level representations of pending bound axioms for proof tracking (#6178).
    /// Each entry is `(term1, polarity1, term2, polarity2)` corresponding to
    /// the SAT-level clause in `pending_axiom_clauses` at the same index.
    /// When proof tracking is enabled, these are recorded as `TheoryLemma` steps
    /// before the SAT-level clauses are injected.
    pub(super) pending_axiom_terms: Vec<(TermId, bool, TermId, bool)>,
    /// Farkas certificates for pending bound axioms (#6686).
    pub(super) pending_axiom_farkas: Vec<Option<FarkasAnnotation>>,
    /// Count of times the current expression split has been seen in
    /// propagate() calls within this SAT solve (#4919). Used to detect
    /// oscillation: first occurrence continues search, subsequent ones
    /// trigger the stop signal to hand control to the split loop.
    pub(super) expr_split_seen_count: u32,
    /// Opt-in incremental eager handoff for inline bound-refinement replay.
    pub(super) bound_refinement_handoff: BoundRefinementHandoff<'a>,
    /// #4919 Approach D/G: count of consecutive check() calls that produced
    /// 0 theory propagations. When this exceeds a threshold, the extension
    /// defers subsequent check() calls until more theory atoms accumulate,
    /// batching atoms to help the bound analyzer cross the derivation
    /// threshold (where rows have enough bounded variables for all-but-one
    /// analysis to succeed).
    pub(super) zero_propagation_streak: u32,
    /// #4919: accumulated theory atoms since the last check(). When deferring
    /// checks due to zero-propagation streak, this tracks how many atoms are
    /// waiting to be processed in a batch.
    pub(super) deferred_atom_count: u32,
    /// Deterministic eager-extension counters for batching diagnostics (#6503).
    pub(super) eager_stats: DpllEagerStats,
    /// Expression-split disequality terms that the split-loop pipeline has
    /// already encoded as split clauses in the persistent SAT solver (#6662).
    /// When the theory re-fires NeedExpressionSplit for one of these terms,
    /// the extension suppresses it (treats it as Sat) instead of storing it
    /// in `pending_split` and triggering the stop signal.
    pub(super) processed_expr_splits: Option<&'a HashSet<TermId>>,
    /// Dense bitset indexed by SAT variable ID for O(1) theory-atom membership.
    /// Replaces the double hashmap lookup (var_to_term + theory_atom_set.contains)
    /// in the hot trail-scan loop of propagate_impl(). Built at construction time.
    pub(super) theory_var_bitset: Vec<u64>,
    /// Trail position up to which `can_propagate()` has scanned without finding
    /// theory atoms. Avoids re-scanning the same boolean-only trail entries on
    /// repeated calls. Reset on backtrack. Uses `Cell` for interior mutability
    /// since `can_propagate()` takes `&self`.
    pub(super) can_propagate_scan_pos: Cell<usize>,
    /// Cached `Z4_DISABLE_THEORY_CHECK` env var (read once at construction).
    pub(super) disable_theory_check: bool,
}

pub(super) struct ProofContext<'a> {
    pub(super) tracker: &'a mut ProofTracker,
    pub(super) negations: &'a HashMap<TermId, TermId>,
}
