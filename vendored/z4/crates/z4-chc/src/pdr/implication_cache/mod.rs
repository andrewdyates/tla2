// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-guided implication caching for PDR push phase.
//!
//! This module implements the LAWI-style implication checking pattern from Golem's
//! ImplicationChecker class. The key insight is that counterexample models from
//! failed implication checks can be cached and reused to quickly reject future
//! implication queries without solver calls.
//!
//! ## Algorithm
//!
//! When checking whether antecedent implies consequent:
//! 1. Fast path: Check if any cached model satisfying antecedent falsifies consequent.
//!    If so, the implication is invalid (O-1 model evaluation vs O-expensive SAT).
//! 2. Slow path: Call SMT solver. If SAT (counterexample found), cache the model.
//!
//! ## Reference
//!
//! Golem LAWI engine: reference/golem/src/engine/Lawi.cc:199-272
//!
//! ## Related Issues
//!
//! - #2126: Model-guided implication caching (this implementation)
//! - #428: Full LAWI engine
//! - #1178: Spacer lemma clustering

use crate::{ChcExpr, ChcOp, SmtValue};
use rustc_hash::FxHashMap;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

/// Result of an implication check.
///
/// Part of the full LAWI-style API (check_with_hints, record_result).
/// The blocking-focused API uses the simpler blocking_rejected_by_cache which returns bool.
/// Production integration tracked in #428 (full LAWI engine).
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ImplicationResult {
    /// The implication holds (antecedent implies consequent is valid).
    Valid,
    /// The implication does not hold (there exists a model satisfying antecedent but not consequent).
    Invalid,
}

/// A compact model representation for fast evaluation.
///
/// Uses variable names as keys and integer/boolean values.
/// More memory-efficient than storing full ChcExpr models.
#[derive(Debug, Clone)]
pub(crate) struct SmallModel {
    /// Variable name to integer value assignments.
    int_assignments: FxHashMap<String, i64>,
    /// Variable name to boolean value assignments.
    bool_assignments: FxHashMap<String, bool>,
}

impl SmallModel {
    /// Create a SmallModel from an SMT solver model.
    pub(crate) fn from_smt_model(model: &FxHashMap<String, SmtValue>) -> Self {
        let mut int_assignments = FxHashMap::default();
        let mut bool_assignments = FxHashMap::default();

        for (name, value) in model {
            match value {
                SmtValue::Int(n) => {
                    int_assignments.insert(name.clone(), *n);
                }
                SmtValue::Bool(b) => {
                    bool_assignments.insert(name.clone(), *b);
                }
                SmtValue::Real(r) => {
                    // Convert rational to integer if denominator is 1.
                    use num_traits::{One, ToPrimitive};
                    if r.denom().is_one() {
                        if let Some(n) = r.numer().to_i64() {
                            int_assignments.insert(name.clone(), n);
                        }
                    }
                }
                SmtValue::BitVec(n, _width) => {
                    // Convert bitvector to integer for evaluation purposes.
                    if let Ok(int_val) = i64::try_from(*n) {
                        int_assignments.insert(name.clone(), int_val);
                    }
                }
                // Array/DT values have no scalar representation
                SmtValue::Opaque(_)
                | SmtValue::ConstArray(_)
                | SmtValue::ArrayMap { .. }
                | SmtValue::Datatype(..) => {}
            }
        }

        Self {
            int_assignments,
            bool_assignments,
        }
    }

    /// Evaluate a boolean expression under this model.
    pub(crate) fn evaluate(&self, expr: &ChcExpr) -> Option<bool> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(b) => Some(*b),

            ChcExpr::Var(v) => self.bool_assignments.get(&v.name).copied(),

            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => self.evaluate(&args[0]).map(|b| !b),

            ChcExpr::Op(ChcOp::And, args) => {
                // Short-circuit evaluation with single pass (O(N) not O(2N))
                let mut all_determined = true;
                for arg in args {
                    match self.evaluate(arg) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all_determined = false,
                    }
                }
                if all_determined {
                    Some(true)
                } else {
                    None
                }
            }

            ChcExpr::Op(ChcOp::Or, args) => {
                // Short-circuit evaluation with single pass (O(N) not O(2N))
                let mut all_determined = true;
                for arg in args {
                    match self.evaluate(arg) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => all_determined = false,
                    }
                }
                if all_determined {
                    Some(false)
                } else {
                    None
                }
            }

            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                match (self.evaluate(&args[0]), self.evaluate(&args[1])) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }

            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                self.compare_values(&args[0], &args[1], |a, b| a == b)
            }

            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                self.compare_values(&args[0], &args[1], |a, b| a != b)
            }

            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a < b)
            }

            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a <= b)
            }

            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a > b)
            }

            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a >= b)
            }

            _ => None,
        })
    }

    fn evaluate_int(&self, expr: &ChcExpr) -> Option<i64> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => Some(*n),
            // #5523: Treat BV constants as integers for cache evaluation.
            ChcExpr::BitVec(v, _w) => i64::try_from(*v).ok(),
            ChcExpr::Var(v) => self.int_assignments.get(&v.name).copied(),
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum: i64 = 0;
                for arg in args {
                    sum = sum.checked_add(self.evaluate_int(arg)?)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = self.evaluate_int(&args[0])?;
                if args.len() == 1 {
                    return first.checked_neg();
                }
                let mut result = first;
                for arg in &args[1..] {
                    result = result.checked_sub(self.evaluate_int(arg)?)?;
                }
                Some(result)
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product: i64 = 1;
                for arg in args {
                    product = product.checked_mul(self.evaluate_int(arg)?)?;
                }
                Some(product)
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                self.evaluate_int(&args[0])?.checked_neg()
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                let a = self.evaluate_int(&args[0])?;
                let b = self.evaluate_int(&args[1])?;
                if b == 0 {
                    None
                } else {
                    // SMT-LIB div is Euclidean (remainder always non-negative), not truncation
                    a.checked_div_euclid(b)
                }
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                let a = self.evaluate_int(&args[0])?;
                let b = self.evaluate_int(&args[1])?;
                if b == 0 {
                    None
                } else {
                    a.checked_rem_euclid(b)
                }
            }
            _ => None,
        })
    }

    fn compare_ints<F>(&self, a: &ChcExpr, b: &ChcExpr, cmp: F) -> Option<bool>
    where
        F: Fn(i64, i64) -> bool,
    {
        Some(cmp(self.evaluate_int(a)?, self.evaluate_int(b)?))
    }

    fn compare_values<F>(&self, a: &ChcExpr, b: &ChcExpr, cmp: F) -> Option<bool>
    where
        F: Fn(i64, i64) -> bool,
    {
        if let (Some(a_val), Some(b_val)) = (self.evaluate_int(a), self.evaluate_int(b)) {
            return Some(cmp(a_val, b_val));
        }
        if let (Some(a_val), Some(b_val)) = (self.evaluate(a), self.evaluate(b)) {
            return Some(if cmp(1, 1) {
                a_val == b_val
            } else {
                a_val != b_val
            });
        }
        None
    }
}

/// Maximum distinct (predicate, level) keys before eviction (#3077 finding 4).
/// With P predicates and L levels, worst case is P*L*8 SmallModels. Cap total
/// keys to bound memory. When exceeded, clear and start fresh (same pattern as
/// bounded_cache_insert in core.rs).
const MAX_BLOCKING_COUNTERMODEL_KEYS: usize = 10_000;

/// Cache for implication checking with model-guided fast rejection.
pub(crate) struct ImplicationCache {
    /// LAWI-style result cache. Production integration tracked in #428.
    #[cfg(test)]
    result_cache: FxHashMap<(u64, u64), ImplicationResult>,
    /// LAWI-style implication countermodels. Production integration tracked in #428.
    #[cfg(test)]
    implication_countermodels: FxHashMap<u64, Vec<SmallModel>>,
    blocking_countermodels: FxHashMap<(usize, usize), Vec<SmallModel>>,
    max_models_per_key: usize,
    pub(crate) cache_hits: usize,
    pub(crate) model_rejections: usize,
    pub(crate) solver_calls: usize,
}

impl Default for ImplicationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ImplicationCache {
    pub(crate) fn new() -> Self {
        Self {
            #[cfg(test)]
            result_cache: FxHashMap::default(),
            #[cfg(test)]
            implication_countermodels: FxHashMap::default(),
            blocking_countermodels: FxHashMap::default(),
            max_models_per_key: 8,
            cache_hits: 0,
            model_rejections: 0,
            solver_calls: 0,
        }
    }

    /// Check if any cached countermodel for (predicate, level) satisfies the blocking formula.
    /// Returns true if blocking_formula is satisfied by a cached model (lemma is NOT inductive).
    pub(crate) fn blocking_rejected_by_cache(
        &mut self,
        predicate_idx: usize,
        level: usize,
        blocking_formula: &ChcExpr,
    ) -> bool {
        let key = (predicate_idx, level);
        if let Some(models) = self.blocking_countermodels.get(&key) {
            for model in models {
                if model.evaluate(blocking_formula) == Some(true) {
                    self.model_rejections += 1;
                    return true;
                }
            }
        }
        false
    }

    /// Record a countermodel for (predicate, level) from a SAT result.
    /// Evicts all entries when key count exceeds cap (#3077 finding 4).
    pub(crate) fn record_blocking_countermodel(
        &mut self,
        predicate_idx: usize,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
    ) {
        let key = (predicate_idx, level);
        // Evict when key count exceeds cap (same pattern as bounded_cache_insert)
        if self.blocking_countermodels.len() >= MAX_BLOCKING_COUNTERMODEL_KEYS
            && !self.blocking_countermodels.contains_key(&key)
        {
            self.blocking_countermodels.clear();
        }
        let models = self.blocking_countermodels.entry(key).or_default();
        if models.len() < self.max_models_per_key {
            models.push(SmallModel::from_smt_model(model));
        }
        self.solver_calls += 1;
    }
}

/// LAWI-style implication API — test-only until #428 (full LAWI engine) is integrated.
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct ImplicationCacheStats {
    pub(crate) countermodel_count: usize,
    pub(crate) cache_hits: usize,
    pub(crate) model_rejections: usize,
    pub(crate) solver_calls: usize,
}

#[cfg(test)]
impl ImplicationCache {
    /// Create cache with custom model limit.
    pub(crate) fn with_max_models(max_models: usize) -> Self {
        Self {
            max_models_per_key: max_models,
            ..Self::new()
        }
    }

    /// Check if implication is cached or rejected by a cached model.
    /// Returns None if solver call is needed.
    pub(crate) fn check_with_hints(
        &mut self,
        antecedent: &ChcExpr,
        consequent: &ChcExpr,
    ) -> Option<ImplicationResult> {
        let ant_hash = antecedent.structural_hash();
        let cons_hash = consequent.structural_hash();
        if let Some(&result) = self.result_cache.get(&(ant_hash, cons_hash)) {
            self.cache_hits += 1;
            return Some(result);
        }
        if let Some(models) = self.implication_countermodels.get(&ant_hash) {
            for model in models {
                if model.evaluate(consequent) == Some(false) {
                    self.model_rejections += 1;
                    self.result_cache
                        .insert((ant_hash, cons_hash), ImplicationResult::Invalid);
                    return Some(ImplicationResult::Invalid);
                }
            }
        }
        None
    }

    /// Record implication result and optionally cache countermodel.
    pub(crate) fn record_result(
        &mut self,
        antecedent: &ChcExpr,
        consequent: &ChcExpr,
        result: ImplicationResult,
        countermodel: Option<&FxHashMap<String, SmtValue>>,
    ) {
        let ant_hash = antecedent.structural_hash();
        let cons_hash = consequent.structural_hash();
        self.solver_calls += 1;
        self.result_cache.insert((ant_hash, cons_hash), result);
        if result == ImplicationResult::Invalid {
            if let Some(model) = countermodel {
                let models = self.implication_countermodels.entry(ant_hash).or_default();
                if models.len() < self.max_models_per_key {
                    models.push(SmallModel::from_smt_model(model));
                }
            }
        }
    }

    /// Clear all cached results and models.
    pub(crate) fn clear(&mut self) {
        self.result_cache.clear();
        self.implication_countermodels.clear();
        self.blocking_countermodels.clear();
    }

    pub(crate) fn stats(&self) -> ImplicationCacheStats {
        let implication_countermodel_count: usize =
            self.implication_countermodels.values().map(Vec::len).sum();
        let blocking_countermodel_count: usize =
            self.blocking_countermodels.values().map(Vec::len).sum();

        ImplicationCacheStats {
            countermodel_count: implication_countermodel_count + blocking_countermodel_count,
            cache_hits: self.cache_hits,
            model_rejections: self.model_rejections,
            solver_calls: self.solver_calls,
        }
    }
}
