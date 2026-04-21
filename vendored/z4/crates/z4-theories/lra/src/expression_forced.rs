// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression analysis and linear equality assertion.
//!
//! Contains `is_expression_forced_to_value` (check if tableau constraints
//! pin a linear expression to a specific value) and `assert_linear_equality*`
//! (receive equalities from Nelson-Oppen combination).
//!
//! Split from `optimization.rs` for code health (#5970).

use std::sync::OnceLock;

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_rational::BigRational;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermId;
use z4_core::TheoryLit;

use crate::{BoundType, LinearExpr, LraSolver};

/// Cached `Z4_DEBUG_LRA_FORCED` env var (checked once per process).
fn debug_lra_forced() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_LRA_FORCED").is_ok())
}

impl LraSolver {
    /// Check if a linear expression is forced to a specific value by equality constraints.
    ///
    /// When an equality like `A = B` is asserted, we add bounds `A - B <= 0` and `A - B >= 0`,
    /// which forces the expression `A - B` to be exactly 0. This creates slack variables
    /// in the tableau with tight bounds.
    ///
    /// Returns `Some((conflict_reasons, true))` if the expression is forced to `target_value`.
    pub(crate) fn is_expression_forced_to_value(
        &self,
        expr: &LinearExpr,
        target_value: &BigRational,
    ) -> Option<(Vec<TheoryLit>, bool)> {
        let debug = debug_lra_forced();

        // Case 1: Expression is constant - it's forced to that constant value
        if expr.coeffs.is_empty() {
            return Some((Vec::new(), expr.constant == *target_value));
        }

        // Case 2: Single variable expression - check if that variable is pinned
        if expr.coeffs.len() == 1 {
            let (var, coeff) = &expr.coeffs[0];
            if let Some(info) = self.vars.get(*var as usize) {
                // Expression value = coeff * var + constant
                // For it to be forced to target_value: coeff * var + constant = target_value
                // So var must be forced to (target_value - constant) / coeff
                let required_var_value = (target_value - expr.constant.to_big()) / coeff.to_big();

                if debug {
                    safe_eprintln!("[LRA_FORCED] Single-var expr: var={}, coeff={}, const={}, target={}, required={}",
                        var, coeff, expr.constant, target_value, required_var_value);
                    safe_eprintln!(
                        "[LRA_FORCED]   var info: lower={:?}, upper={:?}, value={}",
                        info.lower.as_ref().map(|b| (&b.value, b.strict)),
                        info.upper.as_ref().map(|b| (&b.value, b.strict)),
                        info.value
                    );
                }

                // Check if var is pinned to required_var_value
                let is_pinned = info
                    .lower
                    .as_ref()
                    .is_some_and(|lb| lb.value == required_var_value && !lb.strict)
                    && info
                        .upper
                        .as_ref()
                        .is_some_and(|ub| ub.value == required_var_value && !ub.strict);

                if debug {
                    safe_eprintln!("[LRA_FORCED]   is_pinned={}", is_pinned);
                }

                if is_pinned {
                    let mut reasons = Vec::new();
                    if let Some(ref lb) = info.lower {
                        for (r, v) in lb.reasons.iter().zip(&lb.reason_values) {
                            if !r.is_sentinel() {
                                reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                    if let Some(ref ub) = info.upper {
                        for (r, v) in ub.reasons.iter().zip(&ub.reason_values) {
                            if !r.is_sentinel() && !reasons.iter().any(|x| x.term == *r) {
                                reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                    return Some((reasons, true));
                }
            }
            return None;
        }

        // Case 3: Multi-variable expression - look for tableau rows that match this expression.
        // When we assert `A = B`, we create slack variables with rows `s1 = A - B` (s1 <= 0)
        // and `s2 = A - B` (s2 >= 0). Together these pin the expression to 0.
        //
        // We collect all matching rows and combine their bounds to determine if the expression
        // is forced to the target value.
        //
        // SEMANTIC MATCHING (#794): We normalize both expressions before comparison so that
        // `(A+1) - (B+1)` matches `A - B` even if they have different coefficient orderings.
        let mut matching_slack_vars: Vec<(u32, BigRational)> = Vec::new();
        let mut all_reasons: Vec<TheoryLit> = Vec::new();

        // Normalize the input expression for semantic comparison
        let normalized_expr = expr.normalize();

        for row in &self.rows {
            // Check if this row's expression matches our expression.
            // Row represents: basic_var = Σ(row_coeff * var) + row_constant
            // Our expression: Σ(expr_coeff * var) + expr_constant
            //
            // For a match, we need: normalized expr_coeffs == normalized row_coeffs
            // (same variables, same coefficients - ignoring constant term)

            // Normalize the row expression
            let row_constant_big = row.constant.to_big();
            let row_expr = LinearExpr {
                coeffs: row.coeffs.clone(),
                constant: row.constant.clone(),
            };
            let normalized_row = row_expr.normalize();

            // Use semantic coefficient comparison: exact match first,
            // then proportional match (e.g., 4294967296*(A-B) vs (A-B)).
            if normalized_expr.same_coefficients(&normalized_row) {
                // Exact match: expr = row_expr + (expr_constant - row_constant)
                // For expr to be forced to target_value:
                // basic_var must be at target_value - expr_constant + row_constant
                let required_basic_value = target_value - expr.constant.to_big() + &row_constant_big;
                matching_slack_vars.push((row.basic_var, required_basic_value));
            } else if let Some(k) = normalized_expr.proportional_coefficient_ratio(&normalized_row)
            {
                // Proportional match: expr_coeffs = k * row_coeffs.
                // expr = k * (basic_var - row_constant) + expr_constant
                //      = k * basic_var + (expr_constant - k * row_constant)
                // For expr = target_value:
                // basic_var = (target_value - expr_constant + k * row_constant) / k
                let required_basic_value =
                    (target_value - expr.constant.to_big() + &k * &row_constant_big) / &k;
                matching_slack_vars.push((row.basic_var, required_basic_value));
            } else {
                continue;
            }
        }

        if matching_slack_vars.is_empty() {
            return None;
        }

        // Check if the combined bounds from all matching slack variables pin the expression.
        // We need: for each matching slack variable, its value must be at the required value
        // AND collectively there must be both a lower and upper bound constraining to that value.
        let mut has_lower_bound_at_target = false;
        let mut has_upper_bound_at_target = false;

        for (slack_var, required_value) in &matching_slack_vars {
            if let Some(info) = self.vars.get(*slack_var as usize) {
                // Check if this variable's value is at the required value
                if info.value.rational() != *required_value {
                    continue;
                }

                // Collect bounds that pin this value
                if let Some(ref lb) = info.lower {
                    if lb.value == *required_value && !lb.strict {
                        has_lower_bound_at_target = true;
                        for (r, v) in lb.reasons.iter().zip(&lb.reason_values) {
                            if !r.is_sentinel() && !all_reasons.iter().any(|x| x.term == *r) {
                                all_reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                }
                if let Some(ref ub) = info.upper {
                    if ub.value == *required_value && !ub.strict {
                        has_upper_bound_at_target = true;
                        for (r, v) in ub.reasons.iter().zip(&ub.reason_values) {
                            if !r.is_sentinel() && !all_reasons.iter().any(|x| x.term == *r) {
                                all_reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                }
            }
        }

        // Expression is forced if we have both lower and upper bounds pinning to target
        if has_lower_bound_at_target && has_upper_bound_at_target {
            return Some((all_reasons, true));
        }

        None
    }

    /// Assert a linear equality constraint: Σ(coeff * var) = value
    ///
    /// Used by Nelson-Oppen combination to receive equalities from other theories.
    /// The coefficients map term IDs to their coefficients in the linear expression.
    /// The value is the RHS of the equation.
    ///
    /// This adds two bounds: expr <= value AND expr >= value, effectively expr = value.
    pub fn assert_linear_equality(
        &mut self,
        coeffs: &HashMap<TermId, BigRational>,
        value: &BigRational,
        reason_term: TermId,
        reason_value: bool,
    ) {
        let single_reason = [(reason_term, reason_value)];
        self.assert_linear_equality_with_reasons(coeffs, value, &single_reason);
    }

    /// Assert a linear equality constraint with multiple reason literals.
    ///
    /// Passes all reason literals through to the bound assertions so conflict
    /// explanations are complete (#4891).
    pub fn assert_linear_equality_with_reasons(
        &mut self,
        coeffs: &HashMap<TermId, BigRational>,
        value: &BigRational,
        reasons: &[(TermId, bool)],
    ) {
        // Build a linear expression from coefficients
        // Sort by TermId for deterministic variable registration order (#2681)
        let mut sorted_coeffs: Vec<_> = coeffs.iter().collect();
        sorted_coeffs.sort_by_key(|(&term, _)| term);
        let mut expr = LinearExpr::zero();
        for (&term, coeff) in sorted_coeffs {
            let var = self.ensure_var_registered(term);
            expr.add_term(var, coeff.clone());
        }

        // Add dual bounds: expr <= value AND expr >= value
        // These together enforce expr = value
        self.assert_bound_with_reasons(
            expr.clone(),
            value.clone(),
            BoundType::Upper,
            false,
            reasons,
            None,
        );
        self.assert_bound_with_reasons(expr, value.clone(), BoundType::Lower, false, reasons, None);
        self.dirty = true;
    }
}
