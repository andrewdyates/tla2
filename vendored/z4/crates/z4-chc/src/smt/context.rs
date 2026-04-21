// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core SMT context definition and lifecycle methods.

use super::types::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, PredicateId};
#[cfg(not(kani))]
use hashbrown::{HashMap as HbHashMap, HashSet as HbHashSet};
use rustc_hash::FxHashMap;
#[cfg(test)]
use std::collections::VecDeque;
use std::sync::Arc;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HbHashMap, DetHashSet as HbHashSet};
use z4_core::term::TermData;
use z4_core::{CnfClause, TermId, TermStore};

type CachedBvBits = Vec<i32>;
type CachedBvTermMap<T> = HbHashMap<String, T>;
type CachedBvDivKey = (String, String);

#[derive(Default)]
pub(super) struct PersistentBvCache {
    pub(super) signature: Vec<String>,
    pub(super) clauses: Vec<CnfClause>,
    pub(super) next_var: u32,
    pub(super) term_to_bits: CachedBvTermMap<CachedBvBits>,
    pub(super) predicate_to_var: CachedBvTermMap<i32>,
    pub(super) bool_to_var: CachedBvTermMap<i32>,
    pub(super) ite_conditions: HbHashSet<String>,
    pub(super) and_cache: HbHashMap<(i32, i32), i32>,
    pub(super) or_cache: HbHashMap<(i32, i32), i32>,
    pub(super) xor_cache: HbHashMap<(i32, i32), i32>,
    pub(super) unsigned_div_cache: HbHashMap<CachedBvDivKey, (CachedBvBits, CachedBvBits)>,
    pub(super) signed_div_cache: HbHashMap<CachedBvDivKey, (CachedBvBits, CachedBvBits, i32, i32)>,
}

/// SMT context for CHC solving
///
/// Converts CHC expressions to z4-core terms and provides satisfiability checking.
pub struct SmtContext {
    /// Term store for z4-core terms
    pub(crate) terms: TermStore,
    /// Mapping from sort-qualified variable names to z4-core term IDs.
    ///
    /// Keys are always sort-qualified (`{name}_{sort}`) to ensure deterministic
    /// TermId assignment regardless of variable encounter order (#6100).
    pub(super) var_map: FxHashMap<String, TermId>,
    /// Reverse mapping from sort-qualified var_map keys to original CHC variable
    /// names. Used by model extraction to emit original names that downstream
    /// code (cube extraction, MBP, etc.) can look up via `v.name` (#6100).
    pub(super) var_original_names: FxHashMap<String, String>,
    /// Mapping from predicate applications to boolean term IDs
    /// Key is (predicate_id, serialized args) for uniqueness
    pub(super) pred_app_map: FxHashMap<(PredicateId, Vec<String>), TermId>,
    /// Counter for generating unique predicate application names
    pub(super) pred_app_counter: u32,
    /// Optional wall-clock timeout for a single `check_sat` call.
    ///
    /// This is intended for best-effort, auxiliary queries (e.g. invariant discovery).
    pub(super) check_timeout: std::rc::Rc<std::cell::Cell<Option<std::time::Duration>>>,
    /// Per-check expression conversion node counter (#2771).
    pub(super) conversion_node_count: usize,
    /// Set when `conversion_node_count` exceeds the budget during `convert_expr`.
    pub(super) conversion_budget_exceeded: bool,
    /// Count of consecutive `check_sat` calls that exceeded the conversion budget (#2472).
    pub(super) conversion_budget_strikes: u32,
    /// Count of ill-typed BV operations encountered during conversion (#6047).
    /// When > 0, `conversion_budget_exceeded` is set so check_sat returns Unknown
    /// rather than injecting `false` (which is unsound in predecessor/inductiveness
    /// queries — same pattern as #5508 Bool ordering bug).
    pub(super) ill_typed_bv_count: u32,
    /// Optional seed model used to bias SAT branch polarity during `check_sat`.
    ///
    /// This is a best-effort steering hint used by PDR predecessor queries to
    /// improve model stability across iterations. The seed never changes solver
    /// soundness: it only affects phase preference for split literals.
    pub(super) phase_seed_model: Option<FxHashMap<String, SmtValue>>,
    /// Reusable scratch buffer for building sort-qualified variable names (#6363).
    ///
    /// `get_or_create_var` needs the key `{name}_{sort}` for `var_map` lookups.
    /// Previously, every lookup allocated a fresh `String` via `format!()`.
    /// This buffer is cleared and reused on each call, eliminating allocation
    /// on cache hits entirely and reducing allocation on cache misses to the
    /// insert path only.
    pub(super) qualified_name_buf: String,
    /// Persistent BV bit-blast state reused across `reset()` boundaries (#5877).
    ///
    /// The cache is keyed by canonical term fingerprints rather than `TermId`
    /// so it remains valid after `reset()` replaces the query-local term graph.
    pub(super) persistent_bv_cache: PersistentBvCache,
    /// Count of executor fallback attempts in the current solve (#7109 regression fix).
    /// Capped at MAX_EXECUTOR_FALLBACKS to prevent timeout exhaustion on benchmarks
    /// where the internal solver returns Unknown hundreds of times.
    pub(super) executor_fallback_count: u32,
    /// Datatype definitions from the CHC problem (#7016).
    /// When non-empty, queries with UF apps are routed through the executor
    /// adapter which emits declare-datatype commands before the formula.
    pub(super) datatype_defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    /// Test-only queue of forced `check_sat_with_timeout` results.
    ///
    /// This survives `reset()` so verification tests can inject a synthetic
    /// solver answer into code paths that internally reset the SMT context
    /// before querying.
    #[cfg(test)]
    pub(crate) forced_check_sat_results: VecDeque<SmtResult>,
}

pub(crate) struct SmtCheckTimeoutGuard {
    pub(super) cell: std::rc::Rc<std::cell::Cell<Option<std::time::Duration>>>,
    pub(super) prev: Option<std::time::Duration>,
}

impl Drop for SmtCheckTimeoutGuard {
    fn drop(&mut self) {
        self.cell.set(self.prev);
    }
}

impl Default for SmtContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Maximum number of expression nodes that `convert_expr` will process per
/// `check_sat` call before returning a budget-exceeded sentinel (#2771).
pub(super) const MAX_CONVERSION_NODES: usize = 1_000_000;

/// Number of consecutive budget-exceeded `check_sat` calls before
/// short-circuiting to `Unknown` permanently (#2472).
pub(super) const MAX_CONVERSION_STRIKES: u32 = 3;

/// Maximum executor fallback attempts per SmtContext lifetime.
/// 10 attempts × ~30ms each = ~300ms max overhead. Enough to resolve
/// the 2-4 high-disequality queries on half_true_modif_m while preventing
/// the 334-attempt overhead on dillig02_m.
pub(super) const MAX_EXECUTOR_FALLBACKS: u32 = 10;

impl SmtContext {
    fn term_is_bv_cacheable(&self, term: TermId, memo: &mut FxHashMap<TermId, bool>) -> bool {
        if let Some(&cached) = memo.get(&term) {
            return cached;
        }

        let cacheable = match self.terms.get(term) {
            TermData::Const(_) => true,
            TermData::Var(name, _) => self.var_original_names.contains_key(name),
            TermData::Not(inner) => self.term_is_bv_cacheable(*inner, memo),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_is_bv_cacheable(*cond, memo)
                    && self.term_is_bv_cacheable(*then_term, memo)
                    && self.term_is_bv_cacheable(*else_term, memo)
            }
            TermData::Let(_, body) => self.term_is_bv_cacheable(*body, memo),
            TermData::Forall(..) | TermData::Exists(..) => false,
            TermData::App(_, args) => args.iter().all(|&arg| self.term_is_bv_cacheable(arg, memo)),
            _ => false,
        };
        memo.insert(term, cacheable);
        cacheable
    }

    fn is_internal_aux_var_name(name: &str) -> bool {
        name.starts_with("_ite_")
            || name.starts_with("_mod_q_")
            || name.starts_with("_mod_r_")
            || name.starts_with("_div_q_")
            || name.starts_with("_div_r_")
    }

    /// Rename internal auxiliary variables with a namespace suffix.
    ///
    /// Uses a node budget (#2771) to prevent unbounded heap allocation.
    ///
    /// **Soundness note:** On budget exhaustion, returns `None` to signal
    /// that renaming is incomplete. Partial renaming is unsound because
    /// ITE/mod/div elimination uses local counters (starting at 0) — if two
    /// obligations both produce `_ite_0` and only one gets renamed, they
    /// collide in the shared `var_map`, merging distinct mathematical variables.
    /// Callers must treat `None` as an indication that this expression cannot
    /// be safely used in a multi-obligation context.
    fn rename_internal_aux_vars(expr: &ChcExpr, namespace: &str) -> Option<ChcExpr> {
        use std::cell::Cell;

        let budget = Cell::new(crate::expr::MAX_PREPROCESSING_NODES);

        fn rename_inner(expr: &ChcExpr, namespace: &str, budget: &Cell<usize>) -> Option<ChcExpr> {
            crate::expr::maybe_grow_expr_stack(|| {
                crate::expr::ExprDepthGuard::check()?;
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::ConstArrayMarker(_)
                    | ChcExpr::IsTesterMarker(_) => expr.clone(),
                    ChcExpr::Var(v) => {
                        if !SmtContext::is_internal_aux_var_name(&v.name) {
                            return Some(expr.clone());
                        }
                        let mut renamed = v.clone();
                        renamed.name = format!("{}__{}", renamed.name, namespace);
                        ChcExpr::Var(renamed)
                    }
                    ChcExpr::Op(op, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::Op(op.clone(), rewritten)
                    }
                    ChcExpr::PredicateApp(name, id, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::PredicateApp(name.clone(), *id, rewritten)
                    }
                    ChcExpr::FuncApp(name, sort, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::FuncApp(name.clone(), sort.clone(), rewritten)
                    }
                    ChcExpr::ConstArray(ks, val) => ChcExpr::ConstArray(
                        ks.clone(),
                        Arc::new(rename_inner(val.as_ref(), namespace, budget)?),
                    ),
                })
            })
        }

        rename_inner(expr, namespace, &budget)
    }

    /// Preprocessing for solver assumptions and interpolation atom classification.
    ///
    /// Skips `propagate_constants()` which extracts `var = const` equalities and
    /// substitutes them, potentially eliminating the constraint entirely (e.g.,
    /// `x = 0` becomes `true`). When a background is present, such constraints
    /// must be preserved for the theory solver to detect conflicts.
    ///
    /// Both the solver (check_sat_with_assumption_conjuncts) and the interpolation
    /// classifier (compute_interpolant_from_smt_farkas_history) must use this same
    /// pipeline so that TermIds match for A/B partition classification (#2930).
    pub(crate) fn preprocess_incremental_assumption(expr: &ChcExpr, namespace: &str) -> ChcExpr {
        // #6360: Single-pass feature scan replaces 5 individual `contains_*` walks.
        let features = expr.scan_features();

        // #6358 performance: Skip normalization for pure LIA assumptions (no ITE,
        // mod/div, mixed-sort eq, negation, strict int comparison). The scan_features
        // walk is still needed, but we avoid 3-4 additional tree walks for
        // normalization passes that would be identity functions.
        if !features.needs_normalization() {
            let renamed =
                Self::rename_internal_aux_vars(expr, namespace).unwrap_or_else(|| expr.clone());
            return renamed.simplify_constants();
        }

        // #6360: shared core normalization phase 1 (mixed-sort eq → ITE → mod).
        let after_mod = features.core_normalize_pre_rename(expr.clone());
        // If rename budget is exhausted, fall back to original expression.
        // Partial renaming is unsound (see rename_internal_aux_vars doc), but the
        // original expression has no aux vars and is safe to use as-is. The solver
        // will handle ITE/mod natively (possibly returning Unknown).
        let renamed =
            Self::rename_internal_aux_vars(&after_mod, namespace).unwrap_or_else(|| expr.clone());
        // #6360: shared core normalization phase 2 (negation → strict comparison).
        features
            .core_normalize_post_rename(renamed)
            .simplify_constants()
    }

    /// Create a new SMT context
    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            var_map: FxHashMap::default(),
            var_original_names: FxHashMap::default(),
            pred_app_map: FxHashMap::default(),
            pred_app_counter: 0,
            check_timeout: std::rc::Rc::new(std::cell::Cell::new(None)),
            conversion_node_count: 0,
            conversion_budget_exceeded: false,
            conversion_budget_strikes: 0,
            ill_typed_bv_count: 0,
            phase_seed_model: None,
            qualified_name_buf: String::with_capacity(64),
            persistent_bv_cache: PersistentBvCache::default(),
            executor_fallback_count: 0,
            datatype_defs: FxHashMap::default(),
            #[cfg(test)]
            forced_check_sat_results: VecDeque::new(),
        }
    }

    /// Reset the context
    pub fn reset(&mut self) {
        self.terms = TermStore::new();
        self.var_map.clear();
        self.var_original_names.clear();
        self.pred_app_map.clear();
        self.pred_app_counter = 0;
        self.conversion_node_count = 0;
        self.conversion_budget_exceeded = false;
        self.conversion_budget_strikes = 0;
        self.ill_typed_bv_count = 0;
        self.phase_seed_model = None;
        self.executor_fallback_count = 0;
        // Preserve `check_timeout` across reset so callers can enforce per-check timeouts
        // even when helper routines (e.g., ITE case-splitting) reset the context.
        // Preserve `datatype_defs` across reset — they're problem-level metadata (#7016).
        // Preserve `forced_check_sat_results` across reset in tests so verification
        // harnesses can synthesize a solver answer for the next query.
    }

    /// Set datatype definitions from the CHC problem (#7016).
    /// When set, queries containing UF apps are routed through the executor
    /// adapter to get full DT theory support (constructor/selector/tester axioms).
    pub fn set_datatype_defs(
        &mut self,
        defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    ) {
        self.datatype_defs = defs;
    }

    /// Reconstruct a full CHC datatype sort from `self.datatype_defs`.
    fn datatype_sort_from_defs(&self, dt_name: &str) -> Option<ChcSort> {
        let ctors = self.datatype_defs.get(dt_name)?;
        Some(ChcSort::Datatype {
            name: dt_name.to_string(),
            constructors: Arc::new(
                ctors
                    .iter()
                    .map(|(ctor_name, fields)| crate::ChcDtConstructor {
                        name: ctor_name.clone(),
                        selectors: fields
                            .iter()
                            .map(|(sel_name, sel_sort)| crate::ChcDtSelector {
                                name: sel_name.clone(),
                                sort: sel_sort.clone(),
                            })
                            .collect(),
                    })
                    .collect(),
            ),
        })
    }

    /// Try to convert a z4-core App to a CHC DT expression (#7016).
    ///
    /// Checks if `name` matches a known DT constructor, selector, or tester
    /// from `self.datatype_defs`. Returns `Some(ChcExpr)` on match, `None` otherwise.
    pub(super) fn try_dt_app_to_chc_expr(
        &self,
        name: &str,
        args: &[TermId],
        mut convert_arg: impl FnMut(TermId) -> Option<ChcExpr>,
    ) -> Option<ChcExpr> {
        for (dt_name, ctors) in &self.datatype_defs {
            for (ctor_name, fields) in ctors {
                // Constructor match: name == ctor_name, args.len() == fields.len()
                if name == ctor_name && args.len() == fields.len() {
                    let field_exprs: Option<Vec<Arc<ChcExpr>>> =
                        args.iter().map(|&a| convert_arg(a).map(Arc::new)).collect();
                    let result_sort = self
                        .datatype_sort_from_defs(dt_name)
                        .unwrap_or_else(|| ChcSort::Uninterpreted(dt_name.clone()));
                    return Some(ChcExpr::FuncApp(
                        ctor_name.clone(),
                        result_sort,
                        field_exprs?,
                    ));
                }
                // Selector match: name == field.0, single arg
                for (sel_name, sel_sort) in fields {
                    if name == sel_name && args.len() == 1 {
                        let arg_expr = convert_arg(args[0])?;
                        return Some(ChcExpr::FuncApp(
                            sel_name.clone(),
                            sel_sort.clone(),
                            vec![Arc::new(arg_expr)],
                        ));
                    }
                }
            }
            // Tester match: name == "is-{ctor_name}", single arg
            for (ctor_name, _) in ctors {
                let tester_name = format!("is-{ctor_name}");
                if name == tester_name && args.len() == 1 {
                    let arg_expr = convert_arg(args[0])?;
                    return Some(ChcExpr::FuncApp(
                        tester_name,
                        ChcSort::Bool,
                        vec![Arc::new(arg_expr)],
                    ));
                }
            }
        }
        None
    }

    pub(super) fn bv_cache_key(
        &self,
        term: TermId,
        memo: &mut FxHashMap<TermId, Option<String>>,
    ) -> Option<String> {
        if let Some(cached) = memo.get(&term) {
            return cached.clone();
        }
        let mut cacheable_memo = FxHashMap::default();
        if !self.term_is_bv_cacheable(term, &mut cacheable_memo) {
            memo.insert(term, None);
            return None;
        }
        let key = self.term_to_chc_expr(term).map(|expr| {
            let expr_key = crate::InvariantModel::expr_to_smtlib(&expr);
            format!("{:?}::{expr_key}", self.terms.sort(term))
        });
        memo.insert(term, key.clone());
        key
    }

    pub(super) fn bv_cache_signature(
        &self,
        terms: impl IntoIterator<Item = TermId>,
        memo: &mut FxHashMap<TermId, Option<String>>,
    ) -> Vec<String> {
        let mut signature: Vec<String> = terms
            .into_iter()
            .filter_map(|term| self.bv_cache_key(term, memo))
            .collect();
        signature.sort_unstable();
        signature.dedup();
        signature
    }

    /// Temporarily install a SAT phase-seed model for the duration of `f`.
    ///
    /// The previous seed (if any) is restored even when `f` early-returns.
    pub(crate) fn with_phase_seed_model<R>(
        &mut self,
        seed_model: Option<&FxHashMap<String, SmtValue>>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.phase_seed_model.take();
        self.phase_seed_model = seed_model.cloned();
        let result = f(self);
        self.phase_seed_model = prev;
        result
    }

    pub(crate) fn scoped_check_timeout(
        &mut self,
        timeout: Option<std::time::Duration>,
    ) -> SmtCheckTimeoutGuard {
        let prev = self.check_timeout.get();
        self.check_timeout.set(timeout);
        SmtCheckTimeoutGuard {
            cell: std::rc::Rc::clone(&self.check_timeout),
            prev,
        }
    }

    /// Returns true if a per-check timeout is currently active.
    ///
    /// Used by verbose logging to indicate when Unknown results may be due to timeout.
    pub(crate) fn has_active_timeout(&self) -> bool {
        self.check_timeout.get().is_some()
    }

    /// Return the currently-scoped per-check timeout, if any.
    pub(crate) fn current_timeout(&self) -> Option<std::time::Duration> {
        self.check_timeout.get()
    }

    /// Access the sort-qualified variable name → TermId mapping.
    pub(crate) fn var_map(&self) -> &FxHashMap<String, TermId> {
        &self.var_map
    }

    /// Get the original (unqualified) CHC variable name for a sort-qualified
    /// var_map key. Returns the key itself if no mapping exists (defensive
    /// fallback for predicate-app variables or other non-CHC-variable terms).
    pub(crate) fn original_var_name<'a>(&'a self, qualified: &'a str) -> &'a str {
        self.var_original_names
            .get(qualified)
            .map(String::as_str)
            .unwrap_or(qualified)
    }

    #[cfg(test)]
    pub(crate) fn push_forced_check_sat_result_for_tests(&mut self, result: SmtResult) {
        self.forced_check_sat_results.push_back(result);
    }

    /// Run a satisfiability check with a wall-clock timeout.
    ///
    /// On timeout, returns `SmtResult::Unknown`.
    pub fn check_sat_with_timeout(
        &mut self,
        expr: &ChcExpr,
        timeout: std::time::Duration,
    ) -> SmtResult {
        #[cfg(test)]
        if let Some(result) = self.forced_check_sat_results.pop_front() {
            return result;
        }
        let prev = self.check_timeout.replace(Some(timeout));
        let result = self.check_sat(expr);
        self.check_timeout.set(prev);
        result
    }

    /// Like [`check_sat_with_executor_fallback`] but with an explicit timeout.
    pub fn check_sat_with_executor_fallback_timeout(
        &mut self,
        expr: &ChcExpr,
        timeout: std::time::Duration,
    ) -> SmtResult {
        let prev = self.check_timeout.replace(Some(timeout));
        let result = self.check_sat_with_executor_fallback(expr);
        self.check_timeout.set(prev);
        result
    }
}
