// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer and Real objective optimization for SMT solving.
//!
//! Implements `(maximize ...)` and `(minimize ...)` directives via
//! exponential-search + binary-search using `check-sat-assuming`.
//! Supports both Int (BigInt) and Real (BigRational) objectives.
//!
//! Extracted from `executor.rs` as part of the executor.rs decomposition
//! design (designs/2026-03-01-executor-rs-split.md, Split 2).

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::Symbol;
use z4_core::{Sort, TermId};
use z4_frontend::ObjectiveDirection;

use super::model::Model;
use super::Executor;
use crate::executor_types::{ExecutorError, Result, SolveResult, UnknownReason};

impl Executor {
    /// Run optimization if objectives are set, otherwise delegate to check_sat_internal.
    ///
    /// Supports lexicographic multi-objective optimization (#4128 Phase 2):
    /// objectives are optimized in declaration order. After finding the optimal
    /// value for objective i, that value is committed as a hard constraint
    /// before optimizing objective i+1.
    pub(in crate::executor) fn optimize_check_sat(&mut self) -> Result<SolveResult> {
        if self.ctx.objectives().is_empty() {
            return self.check_sat_internal();
        }

        let objectives = self.ctx.objectives().to_vec();
        for obj in &objectives {
            let obj_sort = self.ctx.terms.sort(obj.term).clone();
            if !matches!(obj_sort, Sort::Int | Sort::Real) {
                return Err(ExecutorError::UnsupportedOptimization(format!(
                    "unsupported objective sort: {obj_sort:?}"
                )));
            }
        }

        let base_result = self.check_sat_internal()?;
        if base_result != SolveResult::Sat {
            return Ok(base_result);
        }

        // Lexicographic optimization: optimize each objective in order,
        // committing optimal values as hard constraints between objectives.
        for obj in &objectives {
            let obj_sort = self.ctx.terms.sort(obj.term).clone();

            // Get current model for this objective's initial value.
            let best_model = self.last_model.clone().unwrap_or_else(|| Model {
                sat_model: Vec::new(),
                term_to_var: HashMap::new(),
                euf_model: None,
                array_model: None,
                lra_model: None,
                lia_model: None,
                bv_model: None,
                fp_model: None,
                string_model: None,
                seq_model: None,
            });

            let optimized = match obj_sort {
                Sort::Int => {
                    let best_value = self.evaluate_int_term(&best_model, obj.term)?;
                    match obj.direction {
                        ObjectiveDirection::Maximize => {
                            self.maximize_int_objective(obj.term, best_model, best_value)?
                        }
                        ObjectiveDirection::Minimize => {
                            self.minimize_int_objective(obj.term, best_model, best_value)?
                        }
                    }
                    .map(|(m, v)| (m, BigRational::from(v)))
                }
                Sort::Real => {
                    let best_value = self.evaluate_real_term(&best_model, obj.term)?;
                    match obj.direction {
                        ObjectiveDirection::Maximize => {
                            self.maximize_real_objective(obj.term, best_model, best_value)?
                        }
                        ObjectiveDirection::Minimize => {
                            self.minimize_real_objective(obj.term, best_model, best_value)?
                        }
                    }
                }
                _ => unreachable!(),
            };

            match optimized {
                Some((model, value)) => {
                    self.last_model = Some(model);
                    // Commit this objective's optimal value as a hard constraint
                    // so subsequent objectives optimize under this constraint.
                    if objectives.len() > 1 {
                        let commit = match obj.direction {
                            ObjectiveDirection::Maximize => {
                                self.mk_commit_ge(obj.term, &value, &obj_sort)
                            }
                            ObjectiveDirection::Minimize => {
                                self.mk_commit_le(obj.term, &value, &obj_sort)
                            }
                        };
                        self.ctx.assertions.push(commit);
                    }
                }
                None => {
                    // Optimization was inconclusive for this objective.
                    self.last_assumptions = None;
                    self.last_assumption_core = None;
                    if self.last_unknown_reason.is_none() {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                    self.last_model = None;
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // Internal optimization uses the assumption API; hide it from user-facing state.
        self.last_assumptions = None;
        self.last_assumption_core = None;

        // All objectives optimized successfully.
        self.last_result = Some(SolveResult::Sat);
        self.last_unknown_reason = None;
        // Run model validation on the optimized model (#4642 D5).
        self.finalize_sat_model_validation()
    }

    /// Create `lhs >= value` for committing an optimal value as a hard constraint.
    fn mk_commit_ge(&mut self, lhs: TermId, value: &BigRational, sort: &Sort) -> TermId {
        match sort {
            Sort::Int => self.mk_int_ge(lhs, &value.to_integer()),
            Sort::Real => self.mk_real_ge(lhs, value),
            _ => unreachable!(),
        }
    }

    /// Create `lhs <= value` for committing an optimal value as a hard constraint.
    fn mk_commit_le(&mut self, lhs: TermId, value: &BigRational, sort: &Sort) -> TermId {
        match sort {
            Sort::Int => self.mk_int_le(lhs, &value.to_integer()),
            Sort::Real => self.mk_real_le(lhs, value),
            _ => unreachable!(),
        }
    }

    fn maximize_int_objective(
        &mut self,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigInt,
    ) -> Result<Option<(Model, BigInt)>> {
        let max_rounds: usize = 128;
        let mut lo = best_value.clone();
        let mut hi: Option<BigInt> = None;
        let mut delta = BigInt::one();

        // Find an infeasible upper bound with exponential search.
        for _ in 0..max_rounds {
            let candidate = &lo + &delta;
            let ge = self.mk_int_ge(objective, &candidate);
            match self.check_sat_assuming(&[ge])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    if value < candidate {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "objective did not satisfy bound: got {value}, expected >= {candidate}"
                        )));
                    }
                    best_model = model;
                    best_value = value.clone();
                    lo = value;
                    delta <<= 1;
                }
                SolveResult::Unsat => {
                    hi = Some(candidate);
                    break;
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        let Some(mut hi) = hi else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(None);
        };

        // Binary search between lo (feasible) and hi (infeasible).
        while hi > &lo + BigInt::one() {
            let mid = (&lo + &hi) / BigInt::from(2);
            let ge = self.mk_int_ge(objective, &mid);
            match self.check_sat_assuming(&[ge])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    best_model = model;
                    best_value = value.clone();
                    lo = value;
                }
                SolveResult::Unsat => {
                    hi = mid;
                }
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        Ok(Some((best_model, best_value)))
    }

    fn minimize_int_objective(
        &mut self,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigInt,
    ) -> Result<Option<(Model, BigInt)>> {
        let max_rounds: usize = 128;
        let mut hi = best_value.clone();
        let mut lo: Option<BigInt> = None;
        let mut delta = BigInt::one();

        // Find an infeasible lower bound with exponential search.
        for _ in 0..max_rounds {
            let candidate = &hi - &delta;
            let le = self.mk_int_le(objective, &candidate);
            match self.check_sat_assuming(&[le])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    if value > candidate {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "objective did not satisfy bound: got {value}, expected <= {candidate}"
                        )));
                    }
                    best_model = model;
                    best_value = value.clone();
                    hi = value;
                    delta <<= 1;
                }
                SolveResult::Unsat => {
                    lo = Some(candidate);
                    break;
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        let Some(mut lo) = lo else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(None);
        };

        // Binary search between lo (infeasible) and hi (feasible).
        while hi > &lo + BigInt::one() {
            let mid = (&lo + &hi) / BigInt::from(2);
            let le = self.mk_int_le(objective, &mid);
            match self.check_sat_assuming(&[le])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    best_model = model;
                    best_value = value.clone();
                    hi = value;
                }
                SolveResult::Unsat => {
                    lo = mid;
                }
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        Ok(Some((best_model, best_value)))
    }

    fn mk_int_ge(&mut self, lhs: TermId, rhs: &BigInt) -> TermId {
        let rhs = self.ctx.terms.mk_int(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named(">="), vec![lhs, rhs], Sort::Bool)
    }

    fn mk_int_le(&mut self, lhs: TermId, rhs: &BigInt) -> TermId {
        let rhs = self.ctx.terms.mk_int(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named("<="), vec![lhs, rhs], Sort::Bool)
    }

    // --- Real (BigRational) objective optimization ---

    /// Evaluate a term that should return a rational value.
    fn evaluate_real_term(&self, model: &Model, term: TermId) -> Result<BigRational> {
        use super::model::EvalValue;
        match self.evaluate_term(model, term) {
            EvalValue::Rational(r) => Ok(r),
            EvalValue::Unknown => Err(ExecutorError::UnsupportedOptimization(
                "Real objective could not be evaluated".to_string(),
            )),
            _ => Err(ExecutorError::UnsupportedOptimization(
                "Real objective did not evaluate to a number".to_string(),
            )),
        }
    }

    /// Maximize a Real objective using iterative strict improvement.
    ///
    /// For QF_LRA, the simplex solver produces exact vertex values, so
    /// asserting `obj > best` converges in very few iterations.
    fn maximize_real_objective(
        &mut self,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigRational,
    ) -> Result<Option<(Model, BigRational)>> {
        let max_rounds: usize = 128;

        for _ in 0..max_rounds {
            // Assert strict improvement: obj > best_value
            let gt = self.mk_real_gt(objective, &best_value);
            match self.check_sat_assuming(&[gt])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_real_term(&model, objective)?;
                    if value <= best_value {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "Real objective did not strictly improve: got {value}, expected > {best_value}"
                        )));
                    }
                    best_model = model;
                    best_value = value;
                }
                SolveResult::Unsat => {
                    // best_value is optimal — no strictly better value exists.
                    return Ok(Some((best_model, best_value)));
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        // Ran out of rounds; return best found so far.
        Ok(Some((best_model, best_value)))
    }

    /// Minimize a Real objective using iterative strict improvement.
    fn minimize_real_objective(
        &mut self,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigRational,
    ) -> Result<Option<(Model, BigRational)>> {
        let max_rounds: usize = 128;

        for _ in 0..max_rounds {
            // Assert strict improvement: obj < best_value
            let lt = self.mk_real_lt(objective, &best_value);
            match self.check_sat_assuming(&[lt])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_real_term(&model, objective)?;
                    if value >= best_value {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "Real objective did not strictly improve: got {value}, expected < {best_value}"
                        )));
                    }
                    best_model = model;
                    best_value = value;
                }
                SolveResult::Unsat => {
                    // best_value is optimal — no strictly better value exists.
                    return Ok(Some((best_model, best_value)));
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        // Ran out of rounds; return best found so far.
        Ok(Some((best_model, best_value)))
    }

    /// Create `lhs > rhs` for Real values: `(not (<= lhs rhs))`.
    fn mk_real_gt(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let le = self.mk_real_le(lhs, rhs);
        self.ctx.terms.mk_not(le)
    }

    /// Create `lhs < rhs` for Real values: `(not (>= lhs rhs))`.
    fn mk_real_lt(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let ge = self.mk_real_ge(lhs, rhs);
        self.ctx.terms.mk_not(ge)
    }

    fn mk_real_ge(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let rhs = self.ctx.terms.mk_rational(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named(">="), vec![lhs, rhs], Sort::Bool)
    }

    fn mk_real_le(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let rhs = self.ctx.terms.mk_rational(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named("<="), vec![lhs, rhs], Sort::Bool)
    }
}
