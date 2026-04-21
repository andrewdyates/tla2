// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LP optimization (simplex-based objective minimization/maximization).
//!
//! Expression analysis and linear equality assertion live in sibling
//! `expression_forced.rs`.

use std::sync::OnceLock;

use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::rational::Rational;
use z4_core::{TheoryResult, TheorySolver};

use crate::types::InfRational;
use crate::{
    LinearExpr, LraSolver, OptimizationResult, OptimizationSense, TableauRow, VarInfo, VarStatus,
};

/// Cached `Z4_DEBUG_LRA` env var (checked once per process).
fn debug_lra() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_LRA").is_ok())
}

impl LraSolver {
    /// Optimize a linear expression subject to the currently asserted constraints.
    ///
    /// This method first ensures the constraint system is feasible, then uses
    /// primal simplex to find the optimal value of the given objective.
    ///
    /// # Arguments
    /// * `objective` - The linear expression to optimize
    /// * `sense` - Whether to minimize or maximize
    ///
    /// # Returns
    /// * `OptimizationResult::Optimal(value)` - The optimal value found
    /// * `OptimizationResult::Unbounded` - The objective is unbounded
    /// * `OptimizationResult::Infeasible` - The constraints are unsatisfiable
    /// * `OptimizationResult::Unknown` - Iteration limit reached without conclusion
    ///
    /// # Example
    /// ```
    /// use z4_lra::{LraSolver, LinearExpr, OptimizationSense, OptimizationResult};
    /// use z4_core::{Sort, TermStore, TheoryResult, TheorySolver};
    /// use num_bigint::BigInt;
    /// use num_rational::BigRational;
    ///
    /// let mut terms = TermStore::new();
    /// let x = terms.mk_var("x", Sort::Real);
    /// let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    /// let le_5 = terms.mk_le(x, five); // x <= 5
    ///
    /// let mut solver = LraSolver::new(&terms);
    /// solver.assert_literal(le_5, true);
    ///
    /// // Register variables and parse asserted constraints.
    /// assert!(matches!(solver.check(), TheoryResult::Sat));
    ///
    /// let x_var = *solver.term_to_var().get(&x).expect("x should be interned");
    /// let objective = LinearExpr::var(x_var);
    ///
    /// // Maximize x subject to x <= 5 => optimal = 5.
    /// let result = solver.optimize(&objective, OptimizationSense::Maximize);
    /// assert!(matches!(
    ///     result,
    ///     OptimizationResult::Optimal(val) if val == BigRational::from(BigInt::from(5))
    /// ));
    /// ```
    pub fn optimize(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
    ) -> OptimizationResult {
        self.optimize_with_max_iters(objective, sense, 10_000)
    }

    /// Like [`optimize`], but with a configurable iteration limit for testing.
    pub(crate) fn optimize_with_max_iters(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
        max_iters: usize,
    ) -> OptimizationResult {
        let debug = debug_lra();

        if debug {
            safe_eprintln!(
                "[LRA] optimize() called, sense={:?}, objective vars={}",
                sense,
                objective.coeffs.len()
            );
        }

        // First, check feasibility (this parses atoms and sets bounds)
        let feasibility = self.check();
        match feasibility {
            TheoryResult::Sat => {
                // Continue to optimization
            }
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                return OptimizationResult::Infeasible;
            }
            TheoryResult::Unknown
            | TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_) => {
                // #6166: These indicate incomplete feasibility checking, NOT infeasibility.
                // Unknown means the theory solver cannot determine satisfiability (e.g.,
                // unsupported atoms with ITE, non-linear terms, or variable-divisor div/mod).
                // NeedSplit variants mean the DPLL(T) loop needs case splits to determine SAT.
                return OptimizationResult::Unknown;
            }
            _ => unreachable!("unexpected TheoryResult variant"),
        }

        // If the objective is constant, return it directly
        if objective.coeffs.is_empty() {
            return OptimizationResult::Optimal(objective.constant.to_big());
        }

        // For maximization, negate the objective (minimize -f(x) == maximize f(x))
        let mut obj = objective.clone();
        if sense == OptimizationSense::Maximize {
            obj.negate();
        }

        // Create a fresh variable for the objective: obj_var = objective_expr
        // This allows us to apply bounds and pivoting to minimize obj_var
        let obj_var = self.next_var;
        self.next_var += 1;
        while self.vars.len() <= obj_var as usize {
            self.vars.push(VarInfo::default());
        }

        // Compute the initial value of the objective from current assignment
        let mut obj_value = obj.constant.to_big();
        for &(var, ref coeff) in &obj.coeffs {
            if (var as usize) < self.vars.len() {
                obj_value += coeff.mul_bigrational(&self.vars[var as usize].value.rational());
            }
        }
        self.vars[obj_var as usize].value = InfRational::from_rational(obj_value);
        self.vars[obj_var as usize].status = Some(VarStatus::Basic(self.rows.len()));

        // Substitute basic variables in the objective expression (#4842).
        let mut new_obj_coeffs: Vec<(u32, Rational)> = Vec::new();
        let mut new_obj_constant = obj.constant.clone();
        for &(v, ref c) in &obj.coeffs {
            if let Some(VarStatus::Basic(basic_row_idx)) =
                self.vars.get(v as usize).and_then(|info| info.status)
            {
                let basic_row = &self.rows[basic_row_idx];
                for &(rv, ref rc) in &basic_row.coeffs {
                    crate::types::add_sparse_term_rat(&mut new_obj_coeffs, rv, c * rc);
                }
                new_obj_constant = &new_obj_constant + &(c * &basic_row.constant);
            } else {
                crate::types::add_sparse_term_rat(&mut new_obj_coeffs, v, c.clone());
            }
        }
        let obj_row = TableauRow::new_rat(obj_var, new_obj_coeffs, new_obj_constant);
        let obj_row_idx_for_col = self.rows.len();
        self.rows.push(obj_row);
        self.heap_stale = true; // #8782: new row → full heap rebuild needed

        // Register objective row in column index (#4919 Phase 1)
        {
            let obj_vars: Vec<u32> = self.rows[obj_row_idx_for_col]
                .coeffs
                .iter()
                .map(|&(v, _)| v)
                .collect();
            for v in obj_vars {
                self.col_index_add(v, obj_row_idx_for_col);
            }
        }

        // Primal simplex: minimize obj_var
        // At each iteration, find a non-basic variable that can reduce obj_var
        for iter in 0..max_iters {
            if debug && iter < 20 {
                safe_eprintln!(
                    "[LRA] primal simplex iter {}, obj_var={}, obj_value={}",
                    iter,
                    obj_var,
                    self.vars[obj_var as usize].value
                );
            }

            // Find the objective row
            let obj_row_idx = self.rows.len() - 1;
            let obj_row = &self.rows[obj_row_idx];

            // For minimization: look for a non-basic variable x_j with positive coefficient
            // (increasing x_j would increase obj, so we want to decrease x_j if possible)
            // Or a non-basic variable with negative coefficient that we can increase
            //
            // Standard primal: look for a variable that can reduce the objective
            let mut best_pivot: Option<(u32, bool)> = None; // (var, increase)

            for &(var, ref coeff) in &obj_row.coeffs {
                if matches!(
                    self.vars.get(var as usize).and_then(|v| v.status.as_ref()),
                    Some(VarStatus::NonBasic)
                ) {
                    let info = &self.vars[var as usize];

                    // Positive coeff in objective row: decreasing var reduces objective
                    // But can only decrease if var > lower_bound (or has no lower bound and can go to -inf)
                    if coeff.is_positive() {
                        // Want to decrease var
                        let can_decrease = info
                            .lower
                            .as_ref()
                            .is_none_or(|lb| info.value.rational() > lb.value.to_big());
                        if can_decrease {
                            best_pivot = Some((var, false)); // false = decrease
                            break;
                        }
                    }
                    // Negative coeff: increasing var reduces objective
                    else if coeff.is_negative() {
                        // Want to increase var
                        let can_increase = info
                            .upper
                            .as_ref()
                            .is_none_or(|ub| info.value.rational() < ub.value.to_big());
                        if can_increase {
                            best_pivot = Some((var, true)); // true = increase
                            break;
                        }
                    }
                }
            }

            let Some((pivot_var, increase)) = best_pivot else {
                // No improving pivot found - we're at optimum
                let opt_value = self.vars[obj_var as usize].value.rational();

                // Clean up: remove the objective row
                self.pop_row_with_col_cleanup();
                self.vars[obj_var as usize].status = None;

                // If we were maximizing, negate the result
                let final_value = if sense == OptimizationSense::Maximize {
                    -opt_value
                } else {
                    opt_value
                };

                if debug {
                    safe_eprintln!("[LRA] Found optimal: {}", final_value);
                }

                return OptimizationResult::Optimal(final_value);
            };

            // Determine how far we can move pivot_var
            let info = &self.vars[pivot_var as usize];
            let current_val = info.value.rational();

            // Check if unbounded
            let target_val = if increase {
                // Increasing: target is upper bound
                match &info.upper {
                    Some(ub) => ub.value.to_big(),
                    None => {
                        // No upper bound - check if objective can go to -infinity
                        // Need to check if any basic variable would block us
                        let blocked = self.would_unbounded_move_violate_basic(pivot_var, true);
                        if !blocked {
                            // Clean up
                            self.pop_row_with_col_cleanup();
                            self.vars[obj_var as usize].status = None;
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Unbounded (increasing pivot_var {})",
                                    pivot_var
                                );
                            }
                            return OptimizationResult::Unbounded;
                        }
                        // Find the limiting basic variable and pivot
                        let limit = self.find_pivot_limit(pivot_var, true);
                        current_val.clone() + &limit
                    }
                }
            } else {
                // Decreasing: target is lower bound
                match &info.lower {
                    Some(lb) => lb.value.to_big(),
                    None => {
                        let blocked = self.would_unbounded_move_violate_basic(pivot_var, false);
                        if !blocked {
                            // Clean up
                            self.pop_row_with_col_cleanup();
                            self.vars[obj_var as usize].status = None;
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Unbounded (decreasing pivot_var {})",
                                    pivot_var
                                );
                            }
                            return OptimizationResult::Unbounded;
                        }
                        let limit = self.find_pivot_limit(pivot_var, false);
                        current_val.clone() - &limit
                    }
                }
            };

            // Update pivot_var to target, updating all basic variables accordingly
            let delta = &target_val - &current_val;
            self.vars[pivot_var as usize].value = InfRational::from_rational(target_val);

            // Update all basic variables that depend on pivot_var
            for row in &self.rows {
                let coeff = row.coeff_big(pivot_var);
                if !coeff.is_zero() {
                    let basic_info = &mut self.vars[row.basic_var as usize];
                    basic_info.value += &coeff * &delta;
                }
            }

            // Check if we need to pivot (basic variable hit bound)
            // Find the basic variable that's now at its bound and should become non-basic
            let mut pivot_basic = None;
            for row in &self.rows {
                if row.basic_var == obj_var {
                    continue; // Don't pivot out the objective
                }
                let basic_info = &self.vars[row.basic_var as usize];
                if let Some(lb) = &basic_info.lower {
                    if basic_info.value.rational() <= lb.value.to_big() {
                        pivot_basic = Some(row.basic_var);
                        break;
                    }
                }
                if let Some(ub) = &basic_info.upper {
                    if basic_info.value.rational() >= ub.value.to_big() {
                        pivot_basic = Some(row.basic_var);
                        break;
                    }
                }
            }

            if let Some(leaving_var) = pivot_basic {
                // Find the row with this basic variable — O(1) via HashMap
                if let Some(&row_idx) = self.basic_var_to_row.get(&leaving_var) {
                    if !self.rows[row_idx].coeff(pivot_var).is_zero() {
                        self.pivot(row_idx, pivot_var);
                    }
                }
            }
        }

        // Hit iteration limit — cannot determine result
        self.pop_row_with_col_cleanup();
        self.vars[obj_var as usize].status = None;

        if debug {
            safe_eprintln!("[LRA] Hit iteration limit, returning Unknown");
        }

        OptimizationResult::Unknown
    }

    /// Check if moving a non-basic variable unboundedly would violate any basic variable's bounds
    fn would_unbounded_move_violate_basic(&self, var: u32, increase: bool) -> bool {
        for row in &self.rows {
            let coeff = row.coeff(var);
            if coeff.is_zero() {
                continue;
            }

            let basic_info = &self.vars[row.basic_var as usize];

            // If we increase var by Δ, basic_var changes by coeff * Δ
            // Check if basic_var has a bound in the direction it would move
            if increase {
                if coeff.is_positive() {
                    // basic_var increases - check upper bound
                    if basic_info.upper.is_some() {
                        return true;
                    }
                } else {
                    // basic_var decreases - check lower bound
                    if basic_info.lower.is_some() {
                        return true;
                    }
                }
            } else if coeff.is_positive() {
                // basic_var decreases - check lower bound
                if basic_info.lower.is_some() {
                    return true;
                }
            } else {
                // basic_var increases - check upper bound
                if basic_info.upper.is_some() {
                    return true;
                }
            }
        }
        false
    }

    /// Find how far we can move a non-basic variable before a basic variable hits its bound
    fn find_pivot_limit(&self, var: u32, increase: bool) -> BigRational {
        let mut min_delta = None;

        for row in &self.rows {
            let coeff = row.coeff_big(var);
            if coeff.is_zero() {
                continue;
            }

            let basic_info = &self.vars[row.basic_var as usize];
            let basic_val = basic_info.value.rational();

            // Calculate how much delta in var would cause basic_var to hit its bound
            let delta = if increase {
                if coeff.is_positive() {
                    // basic increases - check distance to upper bound
                    basic_info
                        .upper
                        .as_ref()
                        .map(|ub| (&ub.value_big() - &basic_val) / &coeff)
                } else {
                    // basic decreases - check distance to lower bound
                    basic_info
                        .lower
                        .as_ref()
                        .map(|lb| (&basic_val - &lb.value_big()) / (-&coeff))
                }
            } else if coeff.is_positive() {
                // basic decreases - check distance to lower bound
                basic_info
                    .lower
                    .as_ref()
                    .map(|lb| (&basic_val - &lb.value_big()) / &coeff)
            } else {
                // basic increases - check distance to upper bound
                basic_info
                    .upper
                    .as_ref()
                    .map(|ub| (&ub.value_big() - &basic_val) / (-&coeff))
            };

            if let Some(d) = delta {
                if d >= BigRational::zero() {
                    match &min_delta {
                        None => min_delta = Some(d),
                        Some(m) if d < *m => min_delta = Some(d),
                        _ => {}
                    }
                }
            }
        }

        min_delta.unwrap_or_else(BigRational::zero)
    }
}
