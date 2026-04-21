// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental SAT context for PDKind.
//!
//! Split into submodules:
//! - `bv`: BV bitblasting for incremental contexts
//! - `solve`: DPLL(T) loop and theory conflict handling
//! - `model`: SAT model extraction and verification

mod bv;
mod model;
mod solve;

use super::context::SmtContext;
use super::types::SmtValue;
use crate::ChcExpr;
#[cfg(not(kani))]
use hashbrown::{HashMap as HbHashMap, HashSet as HbHashSet};
use rustc_hash::FxHashMap;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HbHashMap, DetHashSet as HbHashSet};
use z4_core::TermId;

/// Incremental SAT context that keeps a persistent SAT solver across queries.
///
/// Unlike `SmtContext::check_sat()` which rebuilds the entire SAT solver per call,
/// this struct pre-encodes background formulas (e.g. the transition relation) once
/// and uses z4-sat push/pop to scope per-query assertions. This eliminates redundant
/// Tseitin encoding and SAT solver construction on repeated queries with the same
/// background — the dominant cost in PDKind k-induction checks.
///
/// # Usage pattern (PDKind push())
///
/// ```text
/// let mut ctx = IncrementalSatContext::new();
/// ctx.assert_background(&transition_relation, &mut smt_ctx);
/// ctx.finalize_background();
///
/// // Per-obligation queries:
/// ctx.push();
/// let result = ctx.check_sat_incremental(&[lemma, neg_property], &mut smt_ctx);
/// ctx.pop();
/// ```
///
/// # Design
///
/// - Background formulas are encoded once via `Tseitin::encode_and_assert()` and added
///   as global clauses to the SAT solver.
/// - The Tseitin state is saved after background encoding so per-query encoding reuses
///   the same variable assignments.
/// - Per-query formulas use `Tseitin::encode_assertion()` and pass roots as SAT assumptions
///   (temporary per solve call, no clause insertion needed).
/// - Theory checking (LIA) runs fresh per DPLL(T) iteration since LiaSolver is stateless.
///
/// Reference: Golem's `kinductionChecker` pattern in `PDKind.cc` uses push/pop with
/// persistent transition encoding.
pub(crate) struct IncrementalSatContext {
    /// Persistent SAT solver.
    sat: z4_sat::Solver,
    /// Mapping from term IDs to CNF variables.
    term_to_var: HbHashMap<TermId, u32>,
    /// Mapping from CNF variables to term IDs.
    var_to_term: HbHashMap<u32, TermId>,
    /// Number of CNF variables allocated.
    num_vars: u32,
    /// Saved Tseitin state after background encoding (for restoring per query).
    tseitin_state: Option<z4_core::TseitinState>,
    /// Variable map for model extraction (sort-qualified name → TermId).
    var_map: FxHashMap<String, TermId>,
    /// Reverse mapping: sort-qualified → original CHC name (#6100).
    var_original_names: FxHashMap<String, String>,
    /// Original background formulas for SAT-model validation in debug builds.
    pub(super) background_exprs: Vec<ChcExpr>,
    /// Whether the background has been finalized.
    finalized: bool,
    /// Sticky flag set when background expression conversion exceeds the budget.
    ///
    /// In this state, queries conservatively return `Unknown` instead of using a
    /// partially converted background, which would be unsound.
    background_conversion_budget_exceeded: bool,
    /// Fixed offset for BV variables in the SAT solver's variable space (#5122).
    /// Set once on first BV encounter; all BV variables use this base offset.
    bv_var_offset: Option<i32>,
    /// BV term-to-bits mapping, persists across calls for stable variable assignments.
    bv_term_to_bits: HbHashMap<TermId, Vec<i32>>,
    /// BV predicate-to-var mapping, cached for stable connections.
    bv_predicate_to_var: HbHashMap<TermId, i32>,
    /// BV bool-to-var mapping for Bool terms inside BV expressions.
    bv_bool_to_var: HbHashMap<TermId, i32>,
    /// Next BV variable index (1-based, in BV-local space).
    bv_next_var: u32,
    /// Tseitin vars already connected to BV predicates (avoid duplicate connections).
    bv_connected_tseitin_vars: HbHashSet<u32>,
    /// BV AND gate cache, persisted across BvSolver rebuilds (#5877).
    bv_and_cache: HbHashMap<(i32, i32), i32>,
    /// BV OR gate cache, persisted across BvSolver rebuilds (#5877).
    bv_or_cache: HbHashMap<(i32, i32), i32>,
    /// BV XOR gate cache, persisted across BvSolver rebuilds (#5877).
    bv_xor_cache: HbHashMap<(i32, i32), i32>,
    /// BV unsigned division cache, persisted across BvSolver rebuilds (#5877).
    bv_unsigned_div_cache: HbHashMap<(TermId, TermId), (Vec<i32>, Vec<i32>)>,
    /// BV signed division cache, persisted across BvSolver rebuilds (#5877).
    bv_signed_div_cache: HbHashMap<(TermId, TermId), (Vec<i32>, Vec<i32>, i32, i32)>,
    /// Caller-selected solving strategy (#6692).
    plan: IncrementalPlan,
}

/// Caller-selected solving strategy for an `IncrementalSatContext` (#6692).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IncrementalPlan {
    /// Use the persistent incremental solver (default).
    PreferIncremental,
    /// Always use fresh non-incremental solving from background_exprs.
    FreshOnly(FreshOnlyReason),
}

/// Why a context was created in fresh-only mode (#6692).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FreshOnlyReason {
    /// BV bitblast state corruption (#5877).
    BitVectorStateUnsupported,
}

/// Diagnostic record for a false-UNSAT detection (#6692).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CorruptionEvent {
    pub site: &'static str,
    pub background_count: usize,
    pub assumption_count: usize,
}

/// Result of an incremental SAT check (simplified for PDKind needs).
#[derive(Debug)]
pub(crate) enum IncrementalCheckResult {
    Sat(FxHashMap<String, SmtValue>),
    Unsat,
    Unknown,
    /// The persistent solver is quarantined; caller should retry with a fresh query (#6692).
    /// Currently not constructed (all corruption paths fall through to `Unknown`), but
    /// match arms exist in 40+ call sites. Kept to avoid a large cross-crate refactor.
    #[allow(dead_code)]
    RetryFresh(CorruptionEvent),
}

impl IncrementalSatContext {
    /// Create a new incremental SAT context with the default `PreferIncremental` plan.
    pub(crate) fn new() -> Self {
        Self::new_with_plan(IncrementalPlan::PreferIncremental)
    }

    /// Create a new incremental SAT context with an explicit solving plan (#6692).
    pub(crate) fn new_with_plan(plan: IncrementalPlan) -> Self {
        Self {
            sat: z4_sat::Solver::new(0),
            term_to_var: HbHashMap::new(),
            var_to_term: HbHashMap::new(),
            num_vars: 0,
            tseitin_state: None,
            var_map: FxHashMap::default(),
            var_original_names: FxHashMap::default(),
            background_exprs: Vec::new(),
            finalized: false,
            background_conversion_budget_exceeded: false,
            bv_var_offset: None,
            bv_term_to_bits: HbHashMap::new(),
            bv_predicate_to_var: HbHashMap::new(),
            bv_bool_to_var: HbHashMap::new(),
            bv_next_var: 1,
            bv_connected_tseitin_vars: HbHashSet::new(),
            bv_and_cache: HbHashMap::new(),
            bv_or_cache: HbHashMap::new(),
            bv_xor_cache: HbHashMap::new(),
            bv_unsigned_div_cache: HbHashMap::new(),
            bv_signed_div_cache: HbHashMap::new(),
            plan,
        }
    }

    /// Assert a background formula that persists across all queries.
    ///
    /// Must be called before `finalize_background()`. The formula is preprocessed,
    /// converted to a TermId, and encoded via Tseitin into permanent SAT clauses.
    pub(crate) fn assert_background(&mut self, expr: &ChcExpr, smt: &mut SmtContext) {
        debug_assert!(!self.finalized, "cannot assert background after finalize");
        if self.background_conversion_budget_exceeded {
            return;
        }

        // #6692: Skip SAT solver encoding when using fresh-only plan or
        // when the persistent solver is quarantined. The fresh query path
        // rebuilds everything from background_exprs.
        if self.uses_fresh_solving() {
            self.background_exprs.push(expr.clone());
            return;
        }

        // Preprocess the expression.
        // Use the lighter pipeline that skips propagate_constants() to preserve
        // equality constraints as theory atoms (e.g., x=0 must not simplify to true).
        let namespace = format!("bg{}", self.term_to_var.len());
        let normalized = SmtContext::preprocess_incremental_assumption(expr, &namespace);

        // Convert to term in our shared term store, using smt's convert_expr
        // but we need the term in our own store. We share smt's terms.
        smt.reset_conversion_budget();
        let term = smt.convert_expr(&normalized);
        if smt.conversion_budget_exceeded() {
            self.background_conversion_budget_exceeded = true;
            return;
        }

        // Encode via Tseitin into the SAT solver
        let mut tseitin = if let Some(state) = self.tseitin_state.take() {
            z4_core::Tseitin::from_state(&smt.terms, state)
        } else {
            z4_core::Tseitin::new(&smt.terms)
        };

        let _root = tseitin.encode_and_assert(term);
        let new_clauses = tseitin.take_new_clauses();

        // Grow SAT solver to accommodate new variables
        self.sat.ensure_num_vars(tseitin.num_vars() as usize);

        // Add all new clauses as global (permanent)
        for clause in &new_clauses {
            let lits: Vec<z4_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| z4_sat::Literal::from_dimacs(lit))
                .collect();
            self.sat.add_clause_global(lits);
        }

        // Update mappings
        self.term_to_var = tseitin
            .term_to_var()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.var_to_term = tseitin
            .var_to_term()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.num_vars = tseitin.num_vars();

        self.tseitin_state = Some(tseitin.into_state());

        // Bit-blast any new BV predicates (#5122).
        self.bitblast_new_bv_predicates(&smt.terms, true);

        self.background_exprs.push(expr.clone());
    }

    /// Assert a permanent formula after finalization.
    ///
    /// Like `assert_background`, this encodes `expr` via Tseitin into permanent
    /// SAT clauses. Unlike `assert_background`, it may be called *after*
    /// `finalize_background()` — enabling monotonic background growth patterns
    /// such as TRL's incremental depth encoding.
    pub(crate) fn assert_permanent(&mut self, expr: &ChcExpr, smt: &mut SmtContext) {
        if self.background_conversion_budget_exceeded {
            return;
        }

        // #6692: Skip SAT solver encoding when using fresh-only plan or
        // when quarantined. The fresh query path rebuilds from background_exprs.
        if self.uses_fresh_solving() {
            self.background_exprs.push(expr.clone());
            return;
        }

        let namespace = format!("perm{}", self.background_exprs.len());
        let normalized = SmtContext::preprocess_incremental_assumption(expr, &namespace);

        smt.reset_conversion_budget();
        let term = smt.convert_expr(&normalized);
        if smt.conversion_budget_exceeded() {
            self.background_conversion_budget_exceeded = true;
            return;
        }

        let mut tseitin = if let Some(state) = self.tseitin_state.take() {
            z4_core::Tseitin::from_state(&smt.terms, state)
        } else {
            z4_core::Tseitin::new(&smt.terms)
        };

        let _root = tseitin.encode_and_assert(term);
        let new_clauses = tseitin.take_new_clauses();

        self.sat.ensure_num_vars(tseitin.num_vars() as usize);

        for clause in &new_clauses {
            let lits: Vec<z4_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| z4_sat::Literal::from_dimacs(lit))
                .collect();
            self.sat.add_clause_global(lits);
        }

        self.term_to_var = tseitin
            .term_to_var()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.var_to_term = tseitin
            .var_to_term()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.num_vars = tseitin.num_vars();

        self.tseitin_state = Some(tseitin.into_state());

        // Bit-blast any new BV predicates (#5122).
        self.bitblast_new_bv_predicates(&smt.terms, true);

        self.background_exprs.push(expr.clone());
    }

    /// Finalize background encoding. After this, `push()`/`check_sat_incremental()`/`pop()`
    /// can be called (`push`/`pop` are compatibility no-ops in this assumptions-based path).
    pub(crate) fn finalize_background(&mut self, smt: &SmtContext) {
        self.finalized = true;
        // Snapshot the variable map and original names for model extraction
        self.var_map = smt.var_map().clone();
        self.var_original_names = smt.var_original_names.clone();
    }

    /// Refresh the variable map from the SmtContext after `assert_permanent()` calls.
    ///
    /// `assert_permanent()` introduces new variables via `smt.convert_expr()` that
    /// are added to `smt.var_map()` but not to `self.var_map`. This method syncs
    /// the incremental context's var_map so model extraction can find all variables.
    /// Used by BMC which adds level constraints incrementally after finalization.
    pub(crate) fn refresh_var_map(&mut self, smt: &SmtContext) {
        self.var_map = smt.var_map().clone();
        self.var_original_names = smt.var_original_names.clone();
    }

    /// Push a new assertion scope on the SAT solver.
    pub(crate) fn push(&mut self) {
        debug_assert!(self.finalized, "must finalize before push");
        // IncrementalSatContext uses SAT assumptions for per-query assertions.
        // Keep API compatibility with callers that pair push/check/pop, but avoid
        // SAT scope selectors in this path (selector learning can leak across queries).
    }

    /// Pop the most recent assertion scope.
    pub(crate) fn pop(&mut self) {
        // See push(): no-op compatibility shim for assumptions-based incremental checks.
    }

    /// Whether this context uses fresh solving for every query (#6692).
    ///
    /// True when the plan is `FreshOnly`.
    fn uses_fresh_solving(&self) -> bool {
        matches!(self.plan, IncrementalPlan::FreshOnly(_))
    }

    /// Run a fresh non-incremental query from background_exprs + assumptions (#6692).
    pub(crate) fn check_sat_fresh_query(
        &self,
        assumptions: &[ChcExpr],
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        tracing::debug!(
            background_count = self.background_exprs.len(),
            assumption_count = assumptions.len(),
            "fresh query (#6692)"
        );
        let mut conjuncts = self.background_exprs.clone();
        conjuncts.extend(assumptions.iter().cloned());
        if conjuncts.is_empty() {
            return IncrementalCheckResult::Unknown;
        }
        let combined = ChcExpr::and_all(conjuncts);
        let mut fresh_smt = SmtContext::new();
        let fresh_result = if let Some(t) = timeout {
            fresh_smt.check_sat_with_timeout(&combined, t)
        } else {
            fresh_smt.check_sat(&combined)
        };
        match fresh_result {
            super::types::SmtResult::Sat(model) => IncrementalCheckResult::Sat(model),
            result if result.is_unsat() => IncrementalCheckResult::Unsat,
            _ => IncrementalCheckResult::Unknown,
        }
    }

    /// Test accessor: check whether the context is quarantined (#6692).
    /// Always false — Quarantined variant was never constructed and has been removed.
    #[cfg(test)]
    pub(crate) fn is_quarantined(&self) -> bool {
        false
    }

    /// Test accessor: check whether the context uses fresh-only plan (#6692).
    #[cfg(test)]
    pub(crate) fn is_fresh_only(&self) -> bool {
        matches!(self.plan, IncrementalPlan::FreshOnly(_))
    }
}

/// Strip the namespace suffix (`__bgN`, `__qN`, `__permN`) from an auxiliary
/// variable name. Returns the base name if the variable is a namespaced
/// internal aux var (ITE/mod/div), or `None` if no namespace suffix is found.
///
/// The namespace suffixes are added by `SmtContext::rename_internal_aux_vars`
/// during `preprocess_incremental_assumption`. The original expressions in
/// `background_exprs` reference the un-namespaced names, but the SAT/LIA
/// model uses the namespaced versions. This function enables reverse mapping.
pub(crate) fn strip_namespace_suffix(name: &str) -> Option<&str> {
    // Only process internal auxiliary variable names (ITE/mod/div elimination).
    let is_aux = name.starts_with("_ite_")
        || name.starts_with("_mod_q_")
        || name.starts_with("_mod_r_")
        || name.starts_with("_div_q_")
        || name.starts_with("_div_r_");
    if !is_aux {
        return None;
    }
    // Namespace suffixes follow the pattern `__<prefix><digits>`.
    // Find the last `__` that introduces a namespace.
    if let Some(idx) = name.rfind("__") {
        let suffix = &name[idx + 2..];
        if suffix.starts_with("bg") || suffix.starts_with('q') || suffix.starts_with("perm") {
            return Some(&name[..idx]);
        }
    }
    None
}
