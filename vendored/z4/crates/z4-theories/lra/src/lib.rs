// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// SAFETY: LraSolver uses a raw pointer to TermStore for persistent solver
// across split-loop iterations (#6590 Packet 2). The pointer is valid only
// within set_terms() / unset_terms() brackets. All unsafe code is confined
// to the terms() accessor and Send/Sync impls.
#![warn(unsafe_code)]

//! Z4 LRA - Linear Real Arithmetic theory solver
//!
//! Implements the dual simplex algorithm for linear arithmetic over reals,
//! following the approach from "A Fast Linear-Arithmetic Solver for DPLL(T)"
//! by Dutertre & de Moura (CAV 2006).
//!
//! ## Algorithm Overview
//!
//! The solver maintains:
//! - A tableau of linear equalities: basic_var = Σ(coeff * nonbasic_var)
//! - Bounds for each variable (lower, upper, or both)
//! - Current assignment satisfying the tableau
//!
//! When bounds change (from theory atom assertions), we use dual simplex
//! to restore feasibility or detect conflicts.

#![warn(missing_docs)]
#![warn(clippy::all)]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

use crate::rational::Rational;
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smallvec::SmallVec;
use std::sync::OnceLock;
use tracing::{debug, info, trace};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use z4_core::{
    BoundRefinementRequest, DiscoveredEquality, DisequalitySplitRequest, EqualityPropagationResult,
    ExpressionSplitRequest, ModelEqualityRequest, Sort, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver,
};

/// #6359: Cached debug flags for LRA solver.
///
/// Environment variables are read once per process via OnceLock, not per
/// solver construction. In DPLL(T) loops where LraSolver is created fresh
/// on each iteration, this eliminates ~8 syscalls per iteration.
struct LraDebugFlags {
    debug_lra: bool,
    debug_lra_bounds: bool,
    debug_lra_assert: bool,
    debug_lra_reset: bool,
    debug_lra_nelson_oppen: bool,
    debug_intern: bool,
}

static LRA_DEBUG_FLAGS: OnceLock<LraDebugFlags> = OnceLock::new();

fn lra_debug_flags() -> &'static LraDebugFlags {
    LRA_DEBUG_FLAGS.get_or_init(|| LraDebugFlags {
        debug_lra: std::env::var("Z4_DEBUG_LRA").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_lra_bounds: std::env::var("Z4_DEBUG_LRA_BOUNDS").is_ok(),
        debug_lra_assert: std::env::var("Z4_DEBUG_LRA_ASSERT").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_lra_reset: std::env::var("Z4_DEBUG_LRA_RESET").is_ok(),
        debug_lra_nelson_oppen: std::env::var("Z4_DEBUG_LRA_NELSON_OPPEN").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_intern: std::env::var("Z4_DEBUG_INTERN").is_ok(),
    })
}

mod atom_assertion;
mod atom_parsing;
mod bound_assertion;
mod bound_axioms;
mod check_atoms;
mod disequality_check;
mod expression_forced;
mod farkas;
mod farkas_collect;
mod gomory;
mod implied_bounds;
mod implied_interval;
mod implied_refinement;
mod implied_row_reasons;
mod implied_row_recursive;
mod infrational;
mod lia_patch;
mod lia_support;
mod lifecycle;
mod lifecycle_scope;
mod linear_expr;
mod lra_model;
mod lra_query;
mod nelson_oppen;
mod optimization;
mod propagation;
pub mod rational;
mod rational_ops;
mod simplex;
mod tableau;
mod theory_solver;
mod types;

#[cfg(test)]
mod rational_tests;

// Explicit re-exports: types used in the public API or by other crates
pub use types::{
    Bound, GcdRowInfo, GomoryCut, LinearExpr, LraModel, OptimizationResult, OptimizationSense,
    VarStatus,
};
// Crate-internal imports
use types::{
    fractional_part, AtomRef, BoundExplanation, BoundType, ErrorKey, ExprInterval, ImpliedBound,
    InfRational, IntervalEndpoint, ParsedAtomInfo, TableauRow, VarInfo,
};

/// Lazy reason token for deferred reason materialization (#4919 Phase E).
///
/// Most bound propagations are never consumed by the SAT solver (filtered by
/// `bound_is_interesting`, already assigned, or subsumed by stronger clauses).
/// Computing `collect_row_reasons_dedup()` for every implied bound wastes
/// O(rows) work per propagation.
///
/// Stores the implied bound whose explanation should be reconstructed when the
/// propagation queue is drained.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DeferredReason {
    /// Internal variable whose bound justified the propagation.
    var: u32,
    /// Which side of the variable bound to explain.
    /// `true` = upper bound, `false` = lower bound.
    need_upper: bool,
    /// Optional single-row fallback used when recursive explanation fails.
    fallback_row_idx: Option<usize>,
}

/// Internal pending propagation with optional deferred reason materialization.
#[derive(Debug, Clone)]
struct PendingPropagation {
    propagation: TheoryPropagation,
    deferred: Option<DeferredReason>,
}

impl PendingPropagation {
    fn eager(literal: TheoryLit, reason: Vec<TheoryLit>) -> Self {
        Self {
            propagation: TheoryPropagation { literal, reason },
            deferred: None,
        }
    }

    fn eager_propagation(propagation: TheoryPropagation) -> Self {
        Self {
            propagation,
            deferred: None,
        }
    }

    fn deferred(literal: TheoryLit, deferred: DeferredReason) -> Self {
        Self {
            propagation: TheoryPropagation {
                literal,
                reason: Vec::new(),
            },
            deferred: Some(deferred),
        }
    }
}

/// Wakeup entry for a compound atom.
///
/// `slack` is the normalized slack variable representing the compound linear
/// expression. The same atom is indexed under each constituent variable and the
/// slack itself so we can wake it both for same-expression slack tightening and
/// for constituent-variable bound changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompoundAtomRef {
    term: TermId,
    slack: u32,
    strict: bool,
}

/// Structural snapshot for transferring LRA theory state across split-loop
/// iterations without re-parsing the term DAG (#6590).
///
/// Contains all fields preserved by `soft_reset()`: tableau structure,
/// variable mappings, atom caches, and indexing structures. Assertion state
/// (bounds, trail, scopes) is NOT included — the importing solver starts
/// with clean assertion state.
///
/// This avoids the 26-33% overhead of re-creating `LraSolver` and
/// re-registering all atoms on every DPLL(T) iteration.
struct LraStructuralSnapshot {
    rows: Vec<TableauRow>,
    vars: Vec<VarInfo>,
    term_to_var: HashMap<TermId, u32>,
    var_to_term: HashMap<u32, TermId>,
    next_var: u32,
    atom_cache: HashMap<TermId, Option<ParsedAtomInfo>>,
    registered_atoms: HashSet<TermId>,
    atom_index: HashMap<u32, Vec<AtomRef>>,
    compound_use_index: HashMap<u32, Vec<CompoundAtomRef>>,
    var_to_atoms: HashMap<u32, Vec<TermId>>,
    atom_slack: HashMap<(TermId, bool), (u32, Rational)>,
    expr_to_slack: HashMap<Vec<(u32, Rational)>, (u32, Rational)>,
    slack_var_set: HashSet<u32>,
    basic_var_to_row: HashMap<u32, usize>,
    col_index: Vec<Vec<usize>>,
    to_int_terms: Vec<(u32, TermId)>,
    unassigned_atom_count: Vec<u32>,
    // Warm-path caches (#6590 Packet 1)
    not_inner_cache: HashMap<TermId, (TermId, bool)>,
    const_bool_cache: HashMap<TermId, Option<bool>>,
    refinement_eligible_cache: HashMap<TermId, bool>,
    is_integer_sort_cache: HashMap<TermId, bool>,
}

/// Linear Real Arithmetic theory solver using dual simplex.
///
/// `LraSolver` is `'static` — it does not hold a borrow on the `TermStore`.
/// Instead, a raw pointer (`terms_ptr`) is set via `set_terms()` before each
/// operation batch (register_atom, check, etc.) and cleared after. This allows
/// the solver to persist across split-loop iterations while the `TermStore` is
/// mutated between iterations (#6590 Packet 2).
pub struct LraSolver {
    /// Raw pointer to the term store. Set via `set_terms()`, read via `terms()`.
    /// Valid only while the caller guarantees the TermStore is alive and not
    /// mutably borrowed. Null when not in an active operation.
    terms_ptr: *const TermStore,
    /// Tableau rows
    rows: Vec<TableauRow>,
    /// Variable information (indexed by internal var id)
    vars: Vec<VarInfo>,
    /// Mapping from term IDs to internal variable IDs
    term_to_var: HashMap<TermId, u32>,
    /// Mapping from internal variable IDs to term IDs
    var_to_term: HashMap<u32, TermId>,
    /// Next fresh variable ID
    next_var: u32,
    /// Trail for backtracking: (var_id, which_bound, old_value).
    /// Only the modified bound is saved (halves Bound clone count).
    trail: Vec<(u32, BoundType, Option<Bound>)>,
    /// Scope markers: (trail_pos, asserted_trail_len)
    scopes: Vec<(usize, usize)>,
    /// Asserted atoms: term_id -> value
    asserted: HashMap<TermId, bool>,
    /// Trail of asserted keys for scope-based undo (#3676).
    asserted_trail: Vec<TermId>,
    /// Cache of parsed atom information to avoid re-parsing
    atom_cache: HashMap<TermId, Option<ParsedAtomInfo>>,
    /// The atom currently being parsed in check(). When parse_linear_expr hits
    /// an unsupported term, this atom is added to persistent_unsupported_atoms.
    /// None when called from non-atom contexts (shared equalities, cross-sort bounds).
    current_parsing_atom: Option<TermId>,
    /// Dirty flag: need to recompute
    dirty: bool,
    /// Discovered equalities for Nelson-Oppen propagation.
    /// These are collected during check() when we detect tight bounds.
    pending_equalities: Vec<DiscoveredEquality>,
    /// Track which equality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// Trivial conflict from a constant constraint that is unsatisfiable.
    /// For example, `0 < 0` or `-1 >= 0`.
    /// Stores ALL reason literals so blocking clauses are complete (#8012).
    trivial_conflict: Option<Vec<TheoryLit>>,
    /// Set of (atom TermId, asserted value) pairs whose bounds have been asserted
    /// into the tableau. Prevents creating duplicate slack variables and tableau
    /// rows when the same atom is re-asserted across check() calls (#4919).
    /// Cleared on pop() since bounds are restored by the trail.
    bound_atoms: HashSet<(TermId, bool)>,
    /// Persistent unsupported atoms (#6167): atoms whose parsing triggered
    /// unsupported sub-expressions and whose bounds are in the tableau.
    /// Scope-tracked: push() saves and pop() restores (#4919).
    persistent_unsupported_atoms: HashSet<TermId>,
    /// Undo trail for persistent_unsupported_atoms. We only append terms when
    /// they are first inserted, so pop() can rewind to a scope mark without
    /// cloning the full set on every push/check (#6362).
    persistent_unsupported_trail: Vec<TermId>,
    /// Scope markers into persistent_unsupported_trail.
    persistent_unsupported_scope_marks: Vec<usize>,
    /// When true, all variables are integers and strict bounds are canonicalized:
    /// `expr < 0` becomes `expr <= -1`, `expr > 0` becomes `expr >= 1`.
    /// Set by the LIA solver wrapper.
    integer_mode: bool,
    /// Simple PRNG state for Gomory cut candidate selection.
    /// Uses xorshift32 seeded from check iteration count.
    /// Reference: Z3 gomory.cpp:408-422 (cubic-bias randomized selection).
    gomory_rng: u32,
    /// Simple PRNG state for pivot tiebreaking (reservoir sampling).
    /// Uses xorshift32. When multiple pivot candidates have equal cost,
    /// one is selected at random to break symmetry and prevent cycling.
    /// Reference: Z3 `select_pivot_core` in simplex_def.h:546-585.
    pivot_rng: u32,
    // Cached env vars (#2673)
    debug_lra: bool,
    debug_lra_bounds: bool,
    debug_lra_assert: bool,
    debug_lra_reset: bool,
    debug_lra_nelson_oppen: bool,
    debug_intern: bool,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    /// Number of check_during_propagate calls where bound propagation was
    /// skipped because conflict_count exceeded the threshold (#7982).
    propagation_throttle_skips: u64,
    /// Number of times the propagation-time simplex budget was exhausted (#8003).
    /// These are deferred to the full check() simplex call.
    propagation_budget_exhaustions: u64,
    /// Number of BCP-time simplex calls skipped after many conflicts (#8901).
    bcp_simplex_skips: u64,
    /// Number of propagated reasons that were already materialized when queued.
    eager_reason_count: u64,
    /// Number of propagated reasons materialized from `DeferredReason` during
    /// `propagate()` queue drain.
    deferred_reason_count: u64,
    /// Number of check() calls where simplex returned SAT (feasible).
    /// When this is 0, the post-simplex compound wakeup path is dead code
    /// and the benchmark is bottlenecked on the lazy DPLL(T) architecture (#6503).
    simplex_sat_count: u64,
    /// Set of atom terms already registered via register_atom (#4919).
    /// Prevents duplicate registration when both atom and NOT(atom) are registered.
    registered_atoms: HashSet<TermId>,
    /// Atoms grouped by their single arithmetic variable, for bound propagation.
    /// Key: internal var id, Value: list of atoms referencing this variable.
    /// Reference: Z3 Component 3 (same-variable chain propagation).
    atom_index: HashMap<u32, Vec<AtomRef>>,
    /// Buffered theory propagations computed during check(), returned by propagate().
    /// Uses `PendingPropagation` to support lazy reason materialization (#4919 Phase E):
    /// implied-bound propagations store a `DeferredReason` token instead of eagerly
    /// computing `collect_row_reasons_dedup()`. Reasons are materialized only when
    /// drained by `propagate()`.
    pending_propagations: Vec<PendingPropagation>,
    /// Buffered requests to create tighter bound atoms from implied bounds (#4919).
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    /// Atoms already propagated in the current scope. Prevents duplicate
    /// propagations. Cleared on pop() alongside bound restoration.
    propagated_atoms: HashSet<(TermId, bool)>,
    /// When true, this solver is embedded inside a combined theory solver
    /// (e.g., UfLra, AufLra, Lira). Unknown function/term catch-all arms
    /// in parse_linear_expr skip marking atoms as unsupported, because
    /// cross-theory terms (select, UF applications) are expected and handled
    /// by the outer Nelson-Oppen loop (#5524).
    combined_theory_mode: bool,
    /// Persistent mapping from (atom TermId, asserted_value) to (slack_var, orig_constant).
    /// Prevents creating duplicate slack variables when the same atom is re-asserted
    /// after push/pop cycles (#4919). The orig_constant is stored so re-assertions
    /// apply constant compensation even when the slack was created via expr_to_slack
    /// for a different atom's expression (#6205).
    /// Not cleared on pop() — the slack variable and row persist in the tableau.
    atom_slack: HashMap<(TermId, bool), (u32, Rational)>,
    /// Expression-keyed slack variable cache for `get_or_create_slack()`.
    /// Maps normalized coefficient vectors (sorted by var id) to (slack variable id, original constant).
    /// The original constant is stored so that when a slack is reused for an expression with
    /// a different constant offset, the bound can be adjusted accordingly (#6193).
    /// Used by `register_atom` to create slack variables at registration time
    /// (before assertion), enabling `atom_index` to cover compound atoms (#4919).
    expr_to_slack: HashMap<Vec<(u32, Rational)>, (u32, Rational)>,
    /// Set of slack variable IDs created for compound atoms (#6242).
    /// Used to skip `propagate_var_atoms` on slack variables, whose bounds
    /// have incomplete reason sets (missing the structural s = expr link).
    slack_var_set: HashSet<u32>,
    /// Implied variable bounds derived from tableau rows after simplex Sat.
    /// For each variable, stores (implied_lower, implied_upper).
    /// Each bound stores value, strict flag, and the derivation row index for
    /// efficient reason reconstruction in `collect_row_reasons_recursive` (#4919).
    /// Recomputed on every Sat check; not part of the backtrack trail.
    implied_bounds: Vec<(Option<ImpliedBound>, Option<ImpliedBound>)>,
    /// Representative fixed term-backed variable keyed by `(value, is_int)`.
    /// Mirrors Z3's `m_fixed_var_table_*` idea without scanning all fixed terms
    /// for every `discover_cheap_equalities_for_check()` call (#6617).
    fixed_term_value_table: HashMap<(BigRational, bool), u32>,
    /// Reverse membership index for `fixed_term_value_table`.
    /// Used to avoid re-registering the same fixed term-backed variable.
    fixed_term_value_members: HashMap<u32, (BigRational, bool)>,
    /// Newly discovered fixed-term equalities awaiting check()-time materialization.
    /// Stores `(new_var, representative_var)` pairs in internal var ids.
    pending_fixed_term_equalities: Vec<(u32, u32)>,
    /// Offset equalities discovered from nf==2 rows (#6617 Packet 1).
    /// Unlike fixed-term equalities, the base variables are NOT fixed — the equality
    /// is derived from row structure. Stores (var1, var2, row_idx1, row_idx2) so that
    /// reasons can be constructed from the fixed columns in both rows.
    pending_offset_equalities: Vec<(u32, u32, usize, usize)>,
    /// Column index: for each variable, the list of row indices that contain it.
    /// Enables O(nnz) pivot substitution instead of O(rows) scan (#4919 Phase 1).
    /// Maintained during row creation and pivot operations.
    col_index: Vec<Vec<usize>>,
    /// Bland mode: when true, use smallest-index pivot selection (anti-cycling).
    /// Activated after `basis_repeat_count` exceeds threshold (#4919 Phase 2).
    bland_mode: bool,
    /// Count of consecutive iterations where the basis set repeated.
    /// When this exceeds BLAND_THRESHOLD, bland_mode is activated.
    basis_repeat_count: u32,
    /// Position in `asserted_trail` up to which atoms have been processed by
    /// `check()`. On the next `check()` call, only atoms from this position
    /// onward need to be evaluated, avoiding the O(n log n) clone+sort of the
    /// full asserted map (#4919 incremental check optimization).
    last_check_trail_pos: usize,
    /// True when the last disequality check in check() found a violation
    /// (returned NeedDisequalitySplit or NeedExpressionSplit). Forces re-checking
    /// disequalities even when model_may_have_changed is false, to prevent
    /// the optimization from suppressing known violations (#4919).
    last_diseq_check_had_violation: bool,
    /// Buffered disequality split requests from batch evaluation (#6259).
    /// When check() finds multiple violated disequalities, the first is returned
    /// as NeedDisequalitySplit and the rest are stored here for batch draining
    /// by the DPLL(T) split loop. This avoids O(N) solver restarts for N violated
    /// disequalities (e.g., TTA Startup benchmarks with 400+ equality atoms).
    pending_diseq_splits: Vec<DisequalitySplitRequest>,
    /// Whether any variable bound was tightened since the last simplex run.
    /// When false and no new tableau rows were added, the current simplex
    /// solution is still feasible and we can skip the simplex call (#4919).
    bounds_tightened_since_simplex: bool,
    /// Whether any direct variable bound has changed since the last
    /// `compute_implied_bounds()` call. When false, the O(num_vars) direct-bound
    /// overlay loop can be skipped because no direct bound has been updated.
    /// Set true by `assert_var_bound` and cleared by `compute_implied_bounds`.
    pub(crate) direct_bounds_changed_since_implied: bool,
    /// Variables whose direct bounds changed since the last
    /// `compute_implied_bounds()` call. Used for incremental overlay.
    direct_bounds_changed_vars: Vec<u32>,
    /// Monotonic generation counter, incremented each time any variable's
    /// implied bound is tightened in `compute_implied_bounds()`. Used with
    /// `var_bound_gen` and `row_computed_gen` to skip rows whose input
    /// bounds have not changed since last computation (#8003).
    bound_generation: u64,
    /// Per-variable generation: set to `bound_generation` when the variable's
    /// implied bound is tightened. Indexed by variable id.
    var_bound_gen: Vec<u64>,
    /// Per-row generation: set to `bound_generation` after the row is fully
    /// processed in `compute_implied_bounds()`. If all variables in the row
    /// have `var_bound_gen <= row_computed_gen[row_idx]`, the row can be
    /// skipped because no input bound has changed since it was last analyzed.
    row_computed_gen: Vec<u64>,
    /// Whether the last simplex run found a feasible assignment (#6256).
    /// When false, the simplex-skip must not return Sat because variable
    /// values are left in an infeasible state. Returns Unknown instead and
    /// keeps dirty=true so the early-return path doesn't trigger Sat either.
    last_simplex_feasible: bool,
    /// Scope stack for last_simplex_feasible across push/pop (#6209).
    last_simplex_feasible_scopes: Vec<bool>,
    /// Number of tableau rows at the start of check(). Used to detect if
    /// new rows were added during atom processing (which requires simplex).
    rows_at_check_start: usize,
    /// Registered `to_int(x)` terms: `(to_int_var_id, inner_arg_term)`.
    /// Collected during `parse_linear_expr`; floor axiom bounds injected
    /// during `check()`. Floor axiom: `to_int(x) <= x < to_int(x) + 1`,
    /// i.e., `x - to_int(x) >= 0` and `x - to_int(x) < 1` (#5944).
    to_int_terms: Vec<(u32, TermId)>,
    /// Already-injected `to_int` axiom var IDs in this scope (avoid
    /// duplicate injection within one check cycle). Cleared on soft_reset
    /// since bounds are cleared.
    injected_to_int_axioms: HashSet<u32>,
    /// Variables whose bounds tightened since the last `propagate()` call.
    /// Used to avoid scanning ALL atoms in the atom cache — only atoms
    /// involving dirty variables need re-checking (#4919 propagation opt).
    propagation_dirty_vars: HashSet<u32>,
    /// Scratch buffer for collecting dirty vars into a Vec for functions that
    /// require `&[u32]`. Reused across calls to avoid per-check allocation (#7719 D3).
    dirty_vars_scratch: Vec<u32>,
    /// Scratch buffer returned by `compute_implied_bounds()` for reuse across
    /// fixpoint iterations, avoiding per-iteration HashSet allocation.
    newly_bounded_scratch: HashSet<u32>,
    /// Dedicated wakeup list for compound atoms. Unlike `atom_index`, entries
    /// here do not imply a direct bound on the key variable; they only mean the
    /// compound atom should be reconsidered when that variable's bound changes.
    /// Keyed by constituent variables and the compound slack var (#4919 Phase 5).
    compound_use_index: HashMap<u32, Vec<CompoundAtomRef>>,
    /// Reverse index: for each internal variable ID, the list of atom TermIds
    /// whose expression references that variable. Built during `register_atom()`.
    /// Kept as a generic fallback/recount structure; compound propagation now
    /// uses `compound_use_index` as its primary wakeup path (#4919 Phase 5).
    var_to_atoms: HashMap<u32, Vec<TermId>>,
    /// Number of compound propagations queued during the most recent `check()`.
    /// Logged alongside `atom_index` stats to distinguish direct-bound coverage
    /// from compound wakeup coverage (#4919 Phase 5).
    last_compound_propagations_queued: usize,
    /// Number of dirty vars whose key existed in `compound_use_index` (#6579).
    last_compound_wake_dirty_hits: usize,
    /// Number of distinct compound atoms reached from dirty vars before
    /// `try_queue_compound_propagation()` filtering (#6579).
    last_compound_wake_candidates: usize,
    /// O(1) lookup from basic variable ID to its row index in `self.rows`.
    /// Replaces the O(rows) linear scan `self.rows.iter().find(|r| r.basic_var == var)`.
    /// Maintained on row push, pivot, pop, and clear (#4919 Phase B).
    basic_var_to_row: HashMap<u32, usize>,
    /// Rows whose variables had a bound tightened since the last `compute_implied_bounds()`.
    /// Enables skipping untouched rows in the first fixpoint iteration (#4919 Phase A, Gap 2).
    /// Populated from `col_index` when `assert_var_bound` tightens a bound.
    /// Reset after `compute_implied_bounds` completes.
    touched_rows: HashSet<usize>,
    /// True when `touched_rows` contains fresh rows from direct bound assertions
    /// that should be analyzed immediately in `propagate()`.
    ///
    /// `compute_implied_bounds()` also reseeds `touched_rows` with cascade rows
    /// from newly-derived implied bounds. Those rows stay queued for the next
    /// `check()` batch pass instead of retriggering propagate-time row scans on
    /// every `propagate()` call (#6617).
    propagate_direct_touched_rows_pending: bool,
    /// Incrementally-tracked disequality atoms: (term, expr, asserted_value).
    /// Avoids the O(trail) scan on every check() call by recording disequalities
    /// when they are first asserted. Managed via push/pop for backtracking (#4919).
    disequality_trail: Vec<(TermId, LinearExpr, bool)>,
    /// Position in `disequality_trail` at each push scope, for backtracking.
    disequality_trail_scopes: Vec<usize>,
    /// Shared disequalities from Nelson-Oppen: (expr, reason_lits, eq_term) (#5228).
    /// These are disequalities forwarded from other theories (e.g., negated UF-equalities).
    /// Unlike `disequality_trail`, reasons are TheoryLit vectors rather than a single atom.
    /// The optional `TermId` is the original equality term, used to make split clauses
    /// conditional (#6131): `term OR (x < c) OR (x > c)` instead of unconditional.
    shared_disequality_trail: Vec<(LinearExpr, Vec<TheoryLit>, Option<TermId>)>,
    /// Position in `shared_disequality_trail` at each push scope.
    shared_disequality_trail_scopes: Vec<usize>,
    /// Per-variable count of unassigned single-variable bound atoms.
    /// Used to skip rows in `compute_implied_bounds` where no variable has pending atoms,
    /// since bound derivations for those rows cannot produce any propagation (#4919 Phase A, Gap 1).
    /// Indexed by internal var ID. Incremented in `register_atom`, decremented when atom asserted.
    unassigned_atom_count: Vec<u32>,
    /// Max-heap of infeasible basic variables keyed by bound violation magnitude (#4919).
    /// Greatest-error pivot: extracts the variable with the largest bound violation first.
    /// In bland_mode, the heap is rebuilt with error=0 so smallest-var-index wins (anti-cycling).
    /// Reference: Z3 `select_greatest_error_var()` in `theory_arith_core.h:2270-2300`.
    infeasible_heap: std::collections::BinaryHeap<ErrorKey>,
    /// Membership bitset for infeasible_heap: `in_infeasible_heap[var] == true` iff
    /// var is currently in the heap. Prevents duplicate insertion (O(1) check).
    in_infeasible_heap: Vec<bool>,
    /// When true, the infeasible heap needs a full rebuild before simplex.
    /// Set to true by lifecycle methods (pop, reset, soft_reset) and row additions.
    /// Set to false after `rebuild_infeasible_heap()`. When false, incremental
    /// `track_var_feasibility()` calls keep the heap current (#8782).
    heap_stale: bool,
    /// Reusable buffer for `collect_row_reasons_recursive` seen set (#6364).
    /// Avoids allocating a fresh HashSet on every `queue_bound_refinement_request` call.
    /// Cleared before each use, but capacity is preserved across calls.
    reason_seen_buf: HashSet<(TermId, bool)>,
    /// NOT-unwrap cache (#6590 Packet 1): maps literal TermId to (inner_term, negated).
    /// For NOT(inner), stores (inner, true). For bare atoms, stores (atom, false).
    /// Eliminates `self.terms().get()` in `assert_literal`'s hot path.
    not_inner_cache: HashMap<TermId, (TermId, bool)>,
    /// Constant-Bool cache (#6590 Packet 1): maps atom TermId to Some(bool_value)
    /// if the term is a constant Bool, None otherwise. Eliminates `self.terms().get()`
    /// in `check()`'s per-atom constant-Bool detection.
    const_bool_cache: HashMap<TermId, Option<bool>>,
    /// Per-term refinement eligibility cache (#6590 Packet 1): maps TermId to whether
    /// `term_supports_bound_refinement` returns true. Eliminates `self.terms().get()`
    /// in the bound refinement warm path.
    refinement_eligible_cache: HashMap<TermId, bool>,
    /// Per-term integer-sort cache (#6590 Packet 1): maps TermId to whether
    /// `self.terms().sort(term) == Sort::Int`. Eliminates `self.terms().sort()` in
    /// the bound refinement warm path.
    is_integer_sort_cache: HashMap<TermId, bool>,
}

// SAFETY: LraSolver's raw pointer `terms_ptr` is only dereferenced within
// scoped `set_terms()` / `unset_terms()` brackets where the TermStore is
// guaranteed alive. The pointer is never dereferenced concurrently.
#[allow(unsafe_code)]
unsafe impl Send for LraSolver {}
#[allow(unsafe_code)]
unsafe impl Sync for LraSolver {}

#[cfg(kani)]
impl LraSolver {
    /// Kani-only constructor: initializes only the pointer field, avoids
    /// `TermStore::new()` and `lra_debug_flags()` which trigger deep
    /// BTree/HashMap symbolic exploration that CBMC cannot handle (#6612).
    #[cfg(kani)]
    fn new_kani_minimal(ptr: *const TermStore) -> Self {
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
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::new(),
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
            reason_seen_buf: HashSet::new(),
            not_inner_cache: HashMap::new(),
            const_bool_cache: HashMap::new(),
            refinement_eligible_cache: HashMap::new(),
            is_integer_sort_cache: HashMap::new(),
        }
    }
}

// ============================================================================
// Kani Verification Harnesses
// ============================================================================
//
// These proofs verify the core invariants of the LRA (Linear Real Arithmetic) solver:
// 1. LinearExpr operations: term combining, scaling, negation
// 2. Bounds consistency: lower <= upper implies feasibility
// 3. Tableau invariants: pivot operations preserve structure
// 4. Push/pop state consistency


#[cfg(test)]
mod empty_conflict_tests;
#[cfg(test)]
mod issue_6586_tests;
#[cfg(test)]
mod issue_6588_tests;
#[cfg(test)]
mod issue_6612_tests;
#[cfg(test)]
mod issue_6617_fixed_term_table_tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
#[cfg(test)]
mod types_tests;
