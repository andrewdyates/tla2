// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Init-state invariant pre-checking: streaming scan and prechecked bulk paths.
//!
//! Groups `InitCheckConfig`, `precheck_streamed_initial_values`,
//! `scan_init_invariants_streaming`, and `solve_predicate_for_states_to_bulk_prechecked`.

use super::super::super::{
    check_error_to_result, BulkStateStorage, CheckResult, ModelChecker, Trace, Value,
};
use super::{BulkInitStates, EvalCheckError};
use crate::enumerate::{
    enumerate_constraints_to_bulk_with_stats_filter_error, eval_filter_expr,
    BulkConstraintEnumerationError,
};
use crate::state::states_to_trace_value;

/// Bundled configuration for init-state invariant pre-checking.
///
/// Groups the check parameters passed through to [`precheck_streamed_initial_values`],
/// reducing its signature from 10 to 3 arguments.
///
/// Part of #3308: argument count reduction.
struct InitCheckConfig<'a> {
    registry: &'a crate::var_index::VarRegistry,
    constraints: &'a [String],
    invariants: &'a [String],
    eval_state_invariants: &'a [(String, tla_core::Spanned<tla_core::ast::Expr>)],
    property_init_predicates: &'a [(String, tla_core::Spanned<tla_core::ast::Expr>)],
    state_property_violation_names: &'a [String],
    uses_trace: bool,
    stats: &'a crate::check::CheckStats,
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    spec_may_produce_lazy: bool,
}

#[allow(clippy::result_large_err)]
fn precheck_streamed_initial_values(
    ctx: &mut crate::eval::EvalCtx,
    values: &[Value],
    config: &InitCheckConfig<'_>,
) -> Result<bool, CheckResult> {
    use crate::state::ArrayState;

    let mut arr = ArrayState::from_values(values.to_vec());

    match crate::checker_ops::check_state_constraints_array(ctx, config.constraints, &arr) {
        Ok(true) => {}
        Ok(false) => return Ok(false),
        Err(error) => return Err(check_error_to_result(error, config.stats)),
    }

    if let Err(error) = crate::materialize::materialize_array_state(ctx, &mut arr, config.spec_may_produce_lazy) {
        return Err(check_error_to_result(
            EvalCheckError::Eval(error).into(),
            config.stats,
        ));
    }

    let trace_state = if config.uses_trace {
        let state = arr.to_state(config.registry);
        ctx.set_tlc_trace_value(Some(states_to_trace_value(std::slice::from_ref(&state))));
        Some(state)
    } else {
        None
    };

    let invariant_result =
        crate::checker_ops::check_invariants_array_state(ctx, config.invariants, &arr);
    if config.uses_trace {
        ctx.set_tlc_trace_value(None);
    }

    match invariant_result {
        Ok(Some(invariant)) => {
            let trace = Trace::from_states(vec![
                trace_state.unwrap_or_else(|| arr.to_state(config.registry))
            ]);
            return Err(
                if config.state_property_violation_names.contains(&invariant) {
                    CheckResult::PropertyViolation {
                        property: invariant,
                        kind: crate::check::PropertyViolationKind::StateLevel,
                        trace,
                        stats: config.stats.clone(),
                    }
                } else {
                    CheckResult::InvariantViolation {
                        invariant,
                        trace,
                        stats: config.stats.clone(),
                    }
                },
            );
        }
        Ok(None) => {}
        Err(error) => return Err(check_error_to_result(error, config.stats)),
    }

    match crate::checker_ops::check_eval_state_invariants(ctx, config.eval_state_invariants, &arr) {
        Ok(Some(property)) => {
            return Err(CheckResult::PropertyViolation {
                property,
                kind: crate::check::PropertyViolationKind::StateLevel,
                trace: Trace::from_states(vec![arr.to_state(config.registry)]),
                stats: config.stats.clone(),
            });
        }
        Ok(None) => {}
        Err(error) => return Err(check_error_to_result(error, config.stats)),
    }

    match crate::checker_ops::check_property_init_predicates(
        ctx,
        config.property_init_predicates,
        &arr,
    ) {
        Ok(Some(property)) => Err(CheckResult::PropertyViolation {
            property,
            kind: crate::check::PropertyViolationKind::StateLevel,
            trace: Trace::from_states(vec![arr.to_state(config.registry)]),
            stats: config.stats.clone(),
        }),
        Ok(None) => Ok(true),
        Err(error) => Err(check_error_to_result(error, config.stats)),
    }
}

impl<'a> ModelChecker<'a> {
    /// Streaming invariant scan over init states without storing values.
    ///
    /// Part of #3305: For specs like Einstein with huge init spaces (~199M states)
    /// and invariant violations during Init, this avoids materializing all states
    /// before finding the violation. Uses O(1) memory per state — each state is
    /// checked inline and discarded.
    ///
    /// Returns `Ok(())` if all init states pass invariant checking (caller should
    /// then proceed to the full storage-based init path for BFS).
    /// Returns `Err(CheckResult)` if an invariant/property violation is found.
    ///
    /// Same guard conditions as the prechecked path: bails out when continue_on_error
    /// is active, TIR parity shadow-checking is running, or no init-time
    /// invariant/property checks are configured (config invariants, compiled
    /// invariants, eval-based state invariants, or init predicates).
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn scan_init_invariants_streaming(
        &mut self,
        pred_name: &str,
    ) -> Result<(), CheckResult> {
        // Same guard conditions as prechecked path — only run when there are
        // init-time invariants or properties to check and we can short-circuit
        // on violation.
        let has_init_checks = !self.config.invariants.is_empty()
            || !self.compiled.eval_state_invariants.is_empty()
            || !self.compiled.property_init_predicates.is_empty();
        let parity_shadow_active = self
            .tir_parity
            .as_ref()
            .is_some_and(|tir| tir.is_parity_mode());
        if self.exploration.continue_on_error || parity_shadow_active || !has_init_checks {
            return Ok(());
        }

        let resolved = self
            .resolve_init_predicate(pred_name)
            .map_err(|error| check_error_to_result(error, &self.stats))?;

        let check_config = InitCheckConfig {
            registry: &self.ctx.var_registry().clone(),
            constraints: &self.config.constraints,
            invariants: &self.config.invariants,
            eval_state_invariants: &self.compiled.eval_state_invariants,
            property_init_predicates: &self.compiled.property_init_predicates,
            state_property_violation_names: &self.compiled.state_property_violation_names,
            uses_trace: self.compiled.uses_trace,
            stats: &self.stats.clone(),
            spec_may_produce_lazy: self.compiled.spec_may_produce_lazy,
        };

        // The scan filter checks invariants but always returns Ok(false) to skip
        // storage. If an invariant is violated, the error propagates up immediately
        // and stops enumeration.
        let mut scan_filter = |values: &[Value], ctx: &mut crate::eval::EvalCtx| {
            precheck_streamed_initial_values(ctx, values, &check_config)?;
            // State passed invariants — don't store it, just move on.
            Ok(false)
        };

        self.ctx.set_tlc_level(1);

        // Direct constraint enumeration path.
        if let Some(branches) = &resolved.extracted_branches {
            if resolved.unconstrained_vars.is_empty() {
                let vars_len = self.ctx.var_registry().len();
                // Capacity 0: no states will be stored since the filter always rejects.
                let mut storage = BulkStateStorage::new(vars_len, 0);
                let result = enumerate_constraints_to_bulk_with_stats_filter_error(
                    &mut self.ctx,
                    &self.module.vars,
                    branches,
                    &mut storage,
                    &mut scan_filter,
                );
                return match result {
                    Ok(_) => Ok(()),
                    Err(BulkConstraintEnumerationError::Eval(error)) => Err(check_error_to_result(
                        EvalCheckError::Eval(error).into(),
                        &self.stats,
                    )),
                    Err(BulkConstraintEnumerationError::Filter(result)) => Err(result),
                };
            }
        }

        // Fallback: enumerate from a type predicate with canonical AST filtering.
        let pred_body = &self.module.op_defs[&resolved.resolved_name].body;
        let candidates = self.find_type_candidates(pred_name);
        for cand_name in candidates {
            let Some(branches) = self.candidate_branches(&cand_name) else {
                continue;
            };
            let filter_expr = self.candidate_remainder_filter_expr(pred_body, &cand_name);

            let vars_len = self.ctx.var_registry().len();
            let mut storage = BulkStateStorage::new(vars_len, 0);
            let result = enumerate_constraints_to_bulk_with_stats_filter_error(
                &mut self.ctx,
                &self.module.vars,
                &branches,
                &mut storage,
                |values, ctx| {
                    let keep = match filter_expr.as_ref() {
                        Some(expr) => eval_filter_expr(ctx, expr).map_err(|error| {
                            check_error_to_result(
                                EvalCheckError::Eval(error).into(),
                                check_config.stats,
                            )
                        })?,
                        None => true,
                    };
                    if keep {
                        scan_filter(values, ctx)
                    } else {
                        Ok(false)
                    }
                },
            );
            match result {
                Ok(_) => return Ok(()),
                Err(BulkConstraintEnumerationError::Eval(error)) => {
                    return Err(check_error_to_result(
                        EvalCheckError::Eval(error).into(),
                        &self.stats,
                    ));
                }
                Err(BulkConstraintEnumerationError::Filter(result)) => return Err(result),
            }
        }

        // Streaming scan couldn't enumerate (same as prechecked returning None).
        Ok(())
    }

    /// Solve a predicate and stream results to bulk storage while pre-checking init admissions.
    ///
    /// This sequential-only path is used to stop enumeration as soon as an initial
    /// state violates an invariant/property, avoiding materializing huge init spaces
    /// like Einstein before the checker can terminate.
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn solve_predicate_for_states_to_bulk_prechecked(
        &mut self,
        pred_name: &str,
    ) -> Result<Option<BulkInitStates>, CheckResult> {
        let has_init_checks = !self.config.invariants.is_empty()
            || !self.compiled.eval_state_invariants.is_empty()
            || !self.compiled.property_init_predicates.is_empty();
        let parity_shadow_active = self
            .tir_parity
            .as_ref()
            .is_some_and(|tir| tir.is_parity_mode());
        if self.exploration.continue_on_error || parity_shadow_active || !has_init_checks {
            return Ok(None);
        }

        let resolved = self
            .resolve_init_predicate(pred_name)
            .map_err(|error| check_error_to_result(error, &self.stats))?;

        let check_config = InitCheckConfig {
            registry: &self.ctx.var_registry().clone(),
            constraints: &self.config.constraints,
            invariants: &self.config.invariants,
            eval_state_invariants: &self.compiled.eval_state_invariants,
            property_init_predicates: &self.compiled.property_init_predicates,
            state_property_violation_names: &self.compiled.state_property_violation_names,
            uses_trace: self.compiled.uses_trace,
            stats: &self.stats.clone(),
            spec_may_produce_lazy: self.compiled.spec_may_produce_lazy,
        };

        let mut precheck_filter = |values: &[Value], ctx: &mut crate::eval::EvalCtx| {
            precheck_streamed_initial_values(ctx, values, &check_config)
        };

        self.ctx.set_tlc_level(1);

        if let Some(branches) = &resolved.extracted_branches {
            if resolved.unconstrained_vars.is_empty() {
                let vars_len = self.ctx.var_registry().len();
                let mut storage = BulkStateStorage::new(vars_len, 1000);
                let count = enumerate_constraints_to_bulk_with_stats_filter_error(
                    &mut self.ctx,
                    &self.module.vars,
                    branches,
                    &mut storage,
                    &mut precheck_filter,
                );
                return match count {
                    Ok(Some(enumeration)) => Ok(Some(BulkInitStates {
                        storage,
                        enumeration,
                    })),
                    Ok(None) => Ok(None),
                    Err(BulkConstraintEnumerationError::Eval(error)) => Err(check_error_to_result(
                        EvalCheckError::Eval(error).into(),
                        &self.stats,
                    )),
                    Err(BulkConstraintEnumerationError::Filter(result)) => Err(result),
                };
            }
        }

        let pred_body = &self.module.op_defs[&resolved.resolved_name].body;
        let candidates = self.find_type_candidates(pred_name);
        for cand_name in candidates {
            let Some(branches) = self.candidate_branches(&cand_name) else {
                continue;
            };
            let filter_expr = self.candidate_remainder_filter_expr(pred_body, &cand_name);

            let vars_len = self.ctx.var_registry().len();
            let mut storage = BulkStateStorage::new(vars_len, 1000);
            let count = enumerate_constraints_to_bulk_with_stats_filter_error(
                &mut self.ctx,
                &self.module.vars,
                &branches,
                &mut storage,
                |values, ctx| {
                    let keep = match filter_expr.as_ref() {
                        Some(expr) => eval_filter_expr(ctx, expr).map_err(|error| {
                            check_error_to_result(
                                EvalCheckError::Eval(error).into(),
                                check_config.stats,
                            )
                        })?,
                        None => true,
                    };
                    if keep {
                        precheck_filter(values, ctx)
                    } else {
                        Ok(false)
                    }
                },
            );
            match count {
                Ok(Some(enumeration)) => {
                    return Ok(Some(BulkInitStates {
                        storage,
                        enumeration,
                    }));
                }
                Ok(None) => {}
                Err(BulkConstraintEnumerationError::Eval(error)) => {
                    return Err(check_error_to_result(
                        EvalCheckError::Eval(error).into(),
                        &self.stats,
                    ));
                }
                Err(BulkConstraintEnumerationError::Filter(result)) => return Err(result),
            }
        }

        Ok(None)
    }
}
