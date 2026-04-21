// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main check_sat implementation (DPLL(T) loop).

mod bitblast;
mod cnf;
mod preprocess;
mod support;
mod term_growth;
mod theory_loop;
mod theory_model;

use super::context::SmtContext;
use super::model_verify::verify_sat_model_strict_with_mod_retry;
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::ChcExpr;
#[cfg(not(kani))]
use hashbrown::HashMap as HbHashMap;
use rustc_hash::FxHashMap;
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HbHashMap;
use z4_core::TermId;

enum TermGrowthAction {
    Split {
        split: z4_core::SplitRequest,
    },
    DisequalitySplit {
        model: Vec<bool>,
        split: z4_core::DisequalitySplitRequest,
    },
    ExpressionSplit {
        split: z4_core::ExpressionSplitRequest,
    },
}

/// Preprocessed query state produced by `prepare_check_sat_query`.
///
/// Bundles the results of feature scanning, constant propagation,
/// normalization, bound promotion, and conjunction flattening so that
/// later pipeline stages (CNF, bitblast, theory loop) receive a
/// single coherent input instead of many loose locals.
pub(super) struct PreparedQuery {
    pub(super) features: crate::expr::ExprFeatures,
    pub(super) normalized: ChcExpr,
    pub(super) propagated_model: FxHashMap<String, SmtValue>,
    pub(super) top_conjuncts: Vec<ChcExpr>,
    pub(super) needs_euf: bool,
    // Retained in the bundle so future executor routing can reuse preprocess output.
    pub(super) _needs_executor: bool,
}

/// CNF encoding state produced by `build_check_sat_cnf`.
///
/// Bundles the SAT solver, Tseitin variable mappings, and optional
/// assumption tracking. BV fields are populated by `attach_bv_bitblasting`.
pub(super) struct CnfState {
    pub(super) term_to_var: std::collections::BTreeMap<TermId, u32>,
    pub(super) var_to_term: std::collections::BTreeMap<u32, TermId>,
    pub(super) num_vars: u32,
    pub(super) sat: z4_sat::Solver,
    pub(super) assumptions: Option<Vec<z4_sat::Literal>>,
    pub(super) assumption_map: Option<FxHashMap<z4_sat::Literal, ChcExpr>>,
    pub(super) bv_var_offset: i32,
    pub(super) bv_term_to_bits: HbHashMap<TermId, Vec<i32>>,
}

#[cfg(test)]
static THEORY_SOLVER_BUILD_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static SAT_MODEL_ITERATION_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static BV_BITBLAST_BUILD_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static BV_NEW_CLAUSE_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
fn record_theory_solver_build_for_tests() {
    THEORY_SOLVER_BUILD_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_sat_model_iteration_for_tests() {
    SAT_MODEL_ITERATION_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_bv_bitblast_for_tests() {
    BV_BITBLAST_BUILD_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_bv_new_clauses_for_tests(count: usize) {
    BV_NEW_CLAUSE_COUNT.fetch_add(count, Ordering::Relaxed);
}

#[cfg(test)]
pub(super) fn reset_reuse_counters_for_tests() {
    THEORY_SOLVER_BUILD_COUNT.store(0, Ordering::Relaxed);
    SAT_MODEL_ITERATION_COUNT.store(0, Ordering::Relaxed);
    BV_BITBLAST_BUILD_COUNT.store(0, Ordering::Relaxed);
    BV_NEW_CLAUSE_COUNT.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(super) fn reuse_counters_for_tests() -> (usize, usize) {
    (
        THEORY_SOLVER_BUILD_COUNT.load(Ordering::Relaxed),
        SAT_MODEL_ITERATION_COUNT.load(Ordering::Relaxed),
    )
}

#[cfg(test)]
pub(super) fn bv_new_clause_count_for_tests() -> usize {
    BV_NEW_CLAUSE_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(super) fn bv_bitblast_count_for_tests() -> usize {
    BV_BITBLAST_BUILD_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(super) fn cached_bv_clause_count_for_tests(ctx: &SmtContext) -> usize {
    ctx.persistent_bv_cache.clauses.len()
}

impl SmtContext {
    /// Verify a SAT model against the original expression and return
    /// `Sat(model)` or `Unknown` depending on the verification result.
    ///
    /// Shared by `prepare_check_sat_query` (early exits) and the theory
    /// loop (final model assembly).
    pub(super) fn sat_or_unknown(
        expr: &ChcExpr,
        model: FxHashMap<String, SmtValue>,
        source: &'static str,
    ) -> SmtResult {
        let verify_result = verify_sat_model_strict_with_mod_retry(expr, &model);
        if matches!(verify_result, ModelVerifyResult::Invalid) {
            tracing::warn!(
                "SAT model from {source} violates original expression; returning Unknown"
            );
            return SmtResult::Unknown;
        }
        if matches!(verify_result, ModelVerifyResult::Indeterminate) {
            tracing::debug!("SAT model verification indeterminate in {source}; accepting as Sat");
        }
        SmtResult::Sat(model)
    }

    pub fn check_sat(&mut self, expr: &ChcExpr) -> SmtResult {
        let start = std::time::Instant::now();
        let result = self.check_sat_internal(expr);

        // Executor fallback for UNKNOWN on non-trivial queries.
        // The internal DPLL(T) lacks theory propagation and is incomplete
        // on QF_LIA queries with many disequalities (#2477). Route through
        // the full z4-dpll Executor which has LRA bound propagation + CEGQI.
        // #7027: Only fall back for theory-incomplete Unknown, NOT budget/timeout.
        // Budget-exceeded expressions (>1M AST nodes) should not be re-solved
        // through the executor — that defeats the OOM protection mechanism.
        //
        // Overhead guard (#7109 regression fix): Cap executor fallback to 10
        // attempts (MAX_EXECUTOR_FALLBACKS) to prevent cumulative overhead from
        // hundreds of Unknown results exhausting the 15s budget. Also skip fallback
        // when the internal solver took >=2s (query is genuinely hard, not just
        // theory-incomplete — a fast Unknown signals incomplete theory propagation
        // on disequalities). Default per-attempt timeout is 5s (generous for
        // fallback; the 10-attempt cap provides primary overhead protection).
        let internal_elapsed = start.elapsed();
        if matches!(result, SmtResult::Unknown)
            && !self.conversion_budget_exceeded
            && self.conversion_budget_strikes < super::context::MAX_CONVERSION_STRIKES
            && self.executor_fallback_count < super::context::MAX_EXECUTOR_FALLBACKS
            && internal_elapsed < std::time::Duration::from_secs(2)
        {
            let check_timeout = self.check_timeout.get();
            let timeout = match check_timeout {
                Some(t) => t
                    .checked_sub(internal_elapsed)
                    .unwrap_or(std::time::Duration::ZERO),
                None => std::time::Duration::from_secs(5),
            };
            if !timeout.is_zero() {
                self.executor_fallback_count += 1;
                let propagated_model = FxHashMap::default();
                let fallback = self.check_sat_via_executor(expr, &propagated_model, timeout);
                if !matches!(fallback, SmtResult::Unknown) {
                    return fallback;
                }
            }
        }

        result
    }

    /// Executor-fallback check_sat for verification queries (#7109).
    ///
    /// First tries the internal DPLL(T) loop. If it returns Unknown (incomplete
    /// on QF_LIA queries with many disequalities, #2477), falls back to the
    /// full z4-dpll Executor which has theory propagation + CEGQI.
    ///
    /// Use this instead of `check_sat` for PDR verification queries where
    /// completeness matters. Regular check_sat callers (equality discovery,
    /// parity discovery, entry value inference) should NOT use this — they
    /// rely on Unknown to signal graceful degradation.
    pub fn check_sat_with_executor_fallback(&mut self, expr: &ChcExpr) -> SmtResult {
        let start = std::time::Instant::now();
        let result = self.check_sat_internal(expr);

        if matches!(result, SmtResult::Unknown) {
            let timeout = self
                .check_timeout
                .get()
                .and_then(|t| t.checked_sub(start.elapsed()))
                .unwrap_or(std::time::Duration::from_secs(5));
            if !timeout.is_zero() {
                let propagated_model = FxHashMap::default();
                let fallback = self.check_sat_via_executor(expr, &propagated_model, timeout);
                if !matches!(fallback, SmtResult::Unknown) {
                    return fallback;
                }
            }
        }

        result
    }

    fn check_sat_internal(&mut self, expr: &ChcExpr) -> SmtResult {
        let start = std::time::Instant::now();
        let timeout = self.check_timeout.get();

        let prepared = match self.prepare_check_sat_query(expr, start, timeout) {
            Ok(p) => p,
            Err(result) => return result,
        };

        // Build CNF via Tseitin transformation.
        let mut cnf_state = match self.build_check_sat_cnf(&prepared, start, timeout) {
            Ok(s) => s,
            Err(result) => return result,
        };

        // Attach BV bit-blasting if the formula contains BV operations.
        self.attach_bv_bitblasting(&prepared.features, &mut cnf_state);

        // #5877: Check timeout after BV bit-blasting.
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return SmtResult::Unknown;
            }
        }

        let mut split_state = term_growth::SplitState::new();
        self.run_check_sat_theory_loop(expr, prepared, cnf_state, &mut split_state, start, timeout)
    }
}
