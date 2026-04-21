// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::super::debug::debug_liveness_formula;
use super::super::debug::liveness_profile;
use super::super::{
    check_error_to_result, AstToLive, CheckResult, Expr, LiveExpr, LivenessChecker, ModelChecker,
    Spanned,
};
use crate::checker_ops::is_trivially_unsatisfiable;
use crate::liveness::GroupedLivenessPlan;
use crate::LivenessCheckError;

impl ModelChecker<'_> {
    /// Build grouped liveness plans from formula construction.
    ///
    /// Converts fairness constraints and the property to `LiveExpr`, negates,
    /// checks for tautology, builds DNF grouped plans.
    ///
    /// Returns `Ok((plans, max_fairness_tag))` on success, or
    /// `Err(CheckResult)` if an error should be propagated to the caller.
    pub(super) fn build_grouped_plans_for_property(
        &mut self,
        prop_name: &str,
        liveness_expr: &Spanned<Expr>,
    ) -> Result<(Vec<GroupedLivenessPlan>, u32), CheckResult> {
        // Part of #3065: Convert fairness FIRST so fairness-derived tags (ENABLED,
        // StateChanged) are always 1..F regardless of property formula complexity.
        // This enables cross-property caching of check results — the same fairness
        // check evaluated against the same state always has the same cache key.
        let convert_start = if liveness_profile() {
            eprintln!("[liveness] converting fairness + property to LiveExpr...");
            Some(std::time::Instant::now())
        } else {
            None
        };
        let converter = AstToLive::new().with_location_module_name(self.module.root_name.as_str());

        // Convert fairness constraints first (tags 1..F)
        let fairness_start = if liveness_profile() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        let mut fairness_exprs: Vec<LiveExpr> = Vec::new();
        for constraint in &self.liveness_cache.fairness {
            match self.fairness_to_live_expr(constraint, &converter) {
                Ok(expr) => fairness_exprs.push(expr),
                Err(e) => {
                    return Err(check_error_to_result(
                        self.check_error_for_fairness_to_live_expr_error(prop_name, e),
                        &self.stats,
                    ));
                }
            }
        }
        let max_fairness_tag = converter.next_tag().saturating_sub(1);

        let prop_live = match converter.convert(&self.ctx, liveness_expr) {
            Ok(live) => live,
            Err(e) => {
                return Err(check_error_to_result(
                    self.check_error_for_liveness_convert_error(prop_name, e),
                    &self.stats,
                ));
            }
        };

        if let Some(start) = convert_start {
            eprintln!(
                "[liveness] converted in {:.3}s ({} fairness, max_fairness_tag={})",
                start.elapsed().as_secs_f64(),
                self.liveness_cache.fairness.len(),
                max_fairness_tag,
            );
        }
        // Part of #3223: >63 tags are handled gracefully by the inline_fairness
        // fallback path (inline_fairness.rs:400 warns and disables bitmask caching).
        // The core liveness checker uses multi-word CheckMask and eval-based
        // checking, so no hard limit is needed here.

        let negated_prop = LiveExpr::not(prop_live).push_negation();

        if is_trivially_unsatisfiable(&negated_prop) {
            return Err(check_error_to_result(
                LivenessCheckError::FormulaTautology {
                    property: prop_name.to_string(),
                }
                .into(),
                &self.stats,
            ));
        }

        let formula = if fairness_exprs.is_empty() {
            negated_prop
        } else {
            fairness_exprs.push(negated_prop);
            LiveExpr::and(fairness_exprs).push_negation()
        };
        if let Some(start) = fairness_start {
            eprintln!(
                "[liveness] fairness + formula built in {:.3}s",
                start.elapsed().as_secs_f64(),
            );
        }

        debug_eprintln!(
            debug_liveness_formula(),
            "[DEBUG FORMULA] Final formula: {}",
            formula
        );
        let dnf_start = if liveness_profile() {
            eprintln!("[liveness] creating grouped plans (DNF)...");
            Some(std::time::Instant::now())
        } else {
            None
        };
        let grouped_plans = match LivenessChecker::from_formula_grouped(&formula) {
            Ok(plans) => plans,
            Err(e) => {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create liveness checker for '{prop_name}': {e}"
                    ))
                    .into(),
                    &self.stats,
                ));
            }
        };

        if liveness_profile() {
            if let Some(start) = dnf_start {
                eprintln!(
                    "[liveness] DNF grouped plans created in {:.3}s",
                    start.elapsed().as_secs_f64(),
                );
            }
            let dnf_clause_count: usize = grouped_plans.iter().map(|p| p.pems.len()).sum();
            eprintln!(
                "[liveness] {} groups, {} DNF clauses total",
                grouped_plans.len(),
                dnf_clause_count
            );
        }
        debug_block!(debug_liveness_formula(), {
            let dnf_clause_count: usize = grouped_plans.iter().map(|p| p.pems.len()).sum();
            eprintln!(
                "[DEBUG FORMULA] Created {} grouped plans from {} DNF clauses (TLC-style grouping)",
                grouped_plans.len(),
                dnf_clause_count,
            );
            for (i, plan) in grouped_plans.iter().enumerate() {
                eprintln!(
                    "[DEBUG FORMULA] Group {}: tf={}, pems={}, check_state={}, check_action={}",
                    i,
                    plan.tf,
                    plan.pems.len(),
                    plan.check_state.len(),
                    plan.check_action.len(),
                );
            }
        });

        Ok((grouped_plans, max_fairness_tag))
    }
}
