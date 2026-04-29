// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-BFS liveness checking for the parallel checker.
//!
//! Part of #2740: After parallel BFS completes and all workers are joined,
//! runs single-threaded liveness checking using the existing Tableau + SCC
//! infrastructure. Graph data extraction is in `liveness_graph.rs`.

pub(super) use super::liveness_graph::LivenessGraphData;
use super::*;

use crate::check::debug::skip_liveness;
use crate::checker_ops::{is_trivially_unsatisfiable, PlannedPropertyTerm};
use crate::liveness::{AstToLive, LiveExpr, LivenessChecker};
use crate::{ConfigCheckError, LivenessCheckError};
use tla_core::ast::Expr;
use tla_core::Spanned;

pub(in crate::parallel::checker) struct PlannedPropertyExecution {
    pub(in crate::parallel::checker) init_terms: Vec<Spanned<Expr>>,
    pub(in crate::parallel::checker) always_state_terms: Vec<Spanned<Expr>>,
    pub(in crate::parallel::checker) always_action_terms: Vec<Spanned<Expr>>,
    pub(in crate::parallel::checker) liveness_expr: Option<Spanned<Expr>>,
}

impl ParallelChecker {
    pub(super) fn check_error_for_liveness_convert_error(
        &self,
        root_name: &str,
        prop_name: &str,
        err: crate::liveness::ConvertError,
    ) -> crate::CheckError {
        match err {
            crate::liveness::ConvertError::CannotHandleFormula {
                original, reason, ..
            } => LivenessCheckError::CannotHandleFormula {
                location: crate::check::format_span_location(&original.span, root_name),
                reason,
            }
            .into(),
            crate::liveness::ConvertError::EvalFailed { source, .. } => {
                crate::EvalCheckError::Eval(source).into()
            }
            other => LivenessCheckError::Generic(format!(
                "Failed to convert property '{prop_name}' to liveness formula: {other}"
            ))
            .into(),
        }
    }

    pub(super) fn check_error_for_fairness_to_live_expr_error(
        &self,
        root_name: &str,
        prop_name: &str,
        err: crate::checker_ops::FairnessToLiveExprError,
    ) -> crate::CheckError {
        match err {
            crate::checker_ops::FairnessToLiveExprError::Convert(detail) => match detail.error {
                crate::liveness::ConvertError::CannotHandleFormula {
                    original, reason, ..
                } => LivenessCheckError::CannotHandleFormula {
                    location: crate::check::format_span_location(&original.span, root_name),
                    reason,
                }
                .into(),
                crate::liveness::ConvertError::EvalFailed { source, .. } => {
                    crate::EvalCheckError::Eval(source).into()
                }
                other => LivenessCheckError::Generic(format!(
                    "Failed to process fairness for property '{prop_name}': {}: {other}",
                    detail.context
                ))
                .into(),
            },
            crate::checker_ops::FairnessToLiveExprError::Other(msg) => LivenessCheckError::Generic(
                format!("Failed to process fairness for property '{prop_name}': {msg}"),
            )
            .into(),
        }
    }

    fn run_liveness(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        promoted_properties: &[String],
        partial_graph: bool,
    ) -> Option<CheckResult> {
        if self.config.properties.is_empty() || skip_liveness() {
            return None;
        }

        // Part of #3175/#3210: fp-only liveness now reconstructs concrete
        // states from the cached fingerprint graph on the cold post-BFS path
        // instead of retaining every explored state in `seen`.

        // Part of #2227: Only warn for genuine temporal properties, not pure safety.
        // Matches sequential checker's classification-based warning at run_prepare.rs.
        if self.config.symmetry.is_some()
            && crate::checker_ops::any_property_requires_liveness_checker(
                ctx,
                &self.op_defs,
                &self.config.properties,
            )
        {
            eprintln!(
                "Warning: Declaring symmetry during liveness checking is dangerous. \
                 Please check liveness without symmetry defined."
            );
        }

        let root_name = self.module.name.node.as_str();
        if self.config.liveness_execution.uses_on_the_fly() {
            return self.run_on_the_fly_liveness(
                ctx,
                stats,
                promoted_properties,
                partial_graph,
                root_name,
            );
        }

        // Part of #3801: For periodic liveness during BFS, use a lightweight graph
        // builder that skips the expensive `build_full_state_liveness_cache()` call.
        // DashMap iteration is weakly consistent — even with workers suspended,
        // `build_full_state_liveness_cache` can miss entries, producing an incomplete
        // snapshot. The lightweight builder avoids this by leaving `state_cache` empty;
        // safety-temporal checks read state data from `self.seen` directly via
        // `get_array_state_for_fp` (which is per-key, not iteration-based, and thus
        // strongly consistent). Temporal properties are already skipped for partial
        // graphs (checked in `check_single_property`).
        let graph = if partial_graph {
            self.build_periodic_liveness_graph_data()
        } else {
            match self.build_liveness_graph_data(stats, partial_graph) {
                Ok(g) => g,
                Err(result) => return Some(result),
            }
        };
        crate::eval::clear_for_phase_boundary();
        let mut materialized_state_cache: Option<Arc<FxHashMap<Fingerprint, State>>> = None;

        // Part of #3174: Cross-property per-tag caches removed.
        // Bitmask-only mode handles all cache operations.
        for prop_name in &self.config.properties {
            // Part of #2740: Skip properties fully promoted to BFS checking (#2332, #2670).
            // Matches sequential checker's skip logic at run_liveness_checking lines 806-822.
            if promoted_properties.contains(prop_name) {
                continue;
            }
            if let Some(result) = self.check_single_property(
                ctx,
                stats,
                &graph,
                &mut materialized_state_cache,
                root_name,
                prop_name,
                partial_graph,
            ) {
                return Some(result);
            }
        }

        None
    }

    /// Run liveness checking after parallel BFS completes.
    ///
    /// Returns `Some(CheckResult)` on violation or error, `None` if all
    /// properties are satisfied (or there are no liveness properties).
    ///
    /// `promoted_properties` lists property names that were fully promoted to
    /// BFS-phase checking (state-level invariants or action-level implied actions).
    /// These are skipped here because all their terms were already verified during BFS.
    /// Part of #2740: parity with sequential checker's promoted property skip logic.
    pub(super) fn run_post_bfs_liveness(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        promoted_properties: &[String],
    ) -> Option<CheckResult> {
        self.run_liveness(ctx, stats, promoted_properties, false)
    }

    pub(super) fn run_periodic_liveness(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        promoted_properties: &[String],
    ) -> Option<CheckResult> {
        self.run_liveness(ctx, stats, promoted_properties, true)
    }

    fn conjoin_liveness_terms(
        body: &Spanned<Expr>,
        liveness_terms: Vec<Spanned<Expr>>,
    ) -> Option<Spanned<Expr>> {
        let mut iter = liveness_terms.into_iter();
        let mut result = iter.next()?;
        for term in iter {
            result = Spanned {
                node: Expr::And(Box::new(result), Box::new(term)),
                span: body.span,
            };
        }
        Some(result)
    }

    pub(in crate::parallel::checker) fn split_property_terms_for_liveness(
        &self,
        ctx: &EvalCtx,
        stats: &CheckStats,
        prop_name: &str,
    ) -> Result<PlannedPropertyExecution, CheckResult> {
        let def = self.op_defs.get(prop_name).ok_or_else(|| {
            check_error_to_result(
                ConfigCheckError::MissingProperty(prop_name.to_string()).into(),
                stats,
            )
        })?;

        let Some(plan) = crate::checker_ops::plan_property_terms(ctx, &self.op_defs, prop_name)
        else {
            return Ok(PlannedPropertyExecution {
                init_terms: Vec::new(),
                always_state_terms: Vec::new(),
                always_action_terms: Vec::new(),
                liveness_expr: Some(def.body.clone()),
            });
        };

        let mut init_terms = Vec::new();
        let mut always_state_terms = Vec::new();
        let mut always_action_terms = Vec::new();
        let mut liveness_terms = Vec::new();
        for term in plan.terms {
            match term {
                PlannedPropertyTerm::Init(body) => init_terms.push(body),
                PlannedPropertyTerm::StateCompiled(body) | PlannedPropertyTerm::StateEval(body) => {
                    always_state_terms.push(body)
                }
                PlannedPropertyTerm::ActionCompiled(body)
                | PlannedPropertyTerm::ActionEval(body) => always_action_terms.push(body),
                PlannedPropertyTerm::Liveness(body) => liveness_terms.push(body),
            }
        }

        let liveness_expr = if liveness_terms.is_empty() {
            None
        } else if matches!(&def.body.node, Expr::ModuleRef(_, _, _)) {
            // Preserve the original instance-rooted property for temporal conversion.
            // Inlining a named-instance body here loses the outer instance scope for
            // nested relative refs such as `stagesInstance!primerDepleted`, whose
            // body contains `cleanInstance!primerDepleted`.
            Some(def.body.clone())
        } else {
            Self::conjoin_liveness_terms(&def.body, liveness_terms)
        };

        Ok(PlannedPropertyExecution {
            init_terms,
            always_state_terms,
            always_action_terms,
            liveness_expr,
        })
    }

    /// Check a single temporal property, trying the safety-temporal fast path first.
    ///
    /// Part of #2892: For `[]P` properties where P is non-temporal, checks the
    /// property by iterating the state graph directly (O(|V|) or O(|E|)) instead
    /// of building the expensive Tableau + behavior graph + SCC cross-product.
    #[allow(clippy::too_many_arguments)]
    /// Part of #3174: Simplified — no cross-property per-tag caches.
    fn check_single_property(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        graph: &LivenessGraphData,
        materialized_state_cache: &mut Option<Arc<FxHashMap<Fingerprint, State>>>,
        root_name: &str,
        prop_name: &str,
        partial_graph: bool,
    ) -> Option<CheckResult> {
        crate::liveness::clear_enabled_cache();

        let planned = match self.split_property_terms_for_liveness(ctx, stats, prop_name) {
            Ok(planned) => planned,
            Err(result) => return Some(result),
        };
        if let Some(result) = self.check_safety_temporal_terms(
            ctx,
            stats,
            graph,
            prop_name,
            &planned.init_terms,
            &planned.always_state_terms,
            &planned.always_action_terms,
        ) {
            return Some(result);
        }
        let Some(liveness_expr) = planned.liveness_expr else {
            return None;
        };
        if partial_graph {
            if crate::check::debug::liveness_profile() {
                eprintln!(
                    "  [periodic-liveness] Skipping non-safety-temporal property {prop_name} (partial graph)"
                );
            }
            return None;
        }

        // Part of #3065: Fresh converter per property so fairness tags are stable
        // (1..F) regardless of which property we're checking. Matches sequential
        // checker at liveness.rs:309 which creates converter inside check_liveness_property.
        let converter = AstToLive::new().with_location_module_name(root_name);

        // Part of #3065: Convert fairness FIRST so fairness-derived tags (ENABLED,
        // StateChanged) are always 1..F regardless of property formula complexity.
        // This enables cross-property caching of check results — the same fairness
        // check evaluated against the same state always has the same cache key.
        // Matches sequential checker at liveness.rs:317-328.
        let mut fairness_exprs: Vec<LiveExpr> = Vec::new();
        for constraint in &self.fairness {
            match crate::checker_ops::fairness_to_live_expr(
                constraint,
                &self.op_defs,
                ctx,
                &converter,
            ) {
                Ok(expr) => fairness_exprs.push(expr),
                Err(error) => {
                    return Some(check_error_to_result(
                        self.check_error_for_fairness_to_live_expr_error(
                            root_name, prop_name, error,
                        ),
                        stats,
                    ));
                }
            }
        }
        // Part of #3065: Record max fairness tag. Tags ≤ this value are fairness-
        // derived and safe to cache across properties (same tag = same expression).
        // Matches sequential checker at liveness.rs:331.
        let max_fairness_tag = converter.next_tag().saturating_sub(1);

        // Convert the liveness-only remainder of the property (tags F+1..).
        let prop_live = match converter.convert(ctx, &liveness_expr) {
            Ok(live) => live,
            Err(error) => {
                return Some(check_error_to_result(
                    self.check_error_for_liveness_convert_error(root_name, prop_name, error),
                    stats,
                ));
            }
        };

        let negated = LiveExpr::not(prop_live).push_negation();

        if is_trivially_unsatisfiable(&negated) {
            return Some(check_error_to_result(
                LivenessCheckError::FormulaTautology {
                    property: prop_name.to_string(),
                }
                .into(),
                stats,
            ));
        }

        // Part of #2740: Conjoin fairness constraints with negated property.
        // Matches sequential checker's formula construction (liveness.rs lines 364-370):
        // formula = fairness1 /\ fairness2 /\ ... /\ ~property
        let formula = if fairness_exprs.is_empty() {
            negated
        } else {
            // Conjoin all fairness with negated property, then normalize
            fairness_exprs.push(negated);
            LiveExpr::and(fairness_exprs).push_negation()
        };

        let grouped_plans = match LivenessChecker::from_formula_grouped(&formula) {
            Ok(plans) => plans,
            Err(e) => {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create liveness checker for '{prop_name}': {e}"
                    ))
                    .into(),
                    stats,
                ));
            }
        };

        let state_cache = materialized_state_cache
            .get_or_insert_with(|| self.materialize_liveness_state_cache(&graph.state_cache));

        for plan in &grouped_plans {
            if let Some(result) = self.run_plan_group(
                ctx,
                stats,
                graph,
                state_cache,
                prop_name,
                plan,
                max_fairness_tag,
            ) {
                return Some(result);
            }
        }

        None
    }

    // run_plan_group and materialize_liveness_state_cache moved to
    // liveness_execution.rs (Part of #3535).
}

// Part of #2740: is_trivially_unsatisfiable moved to checker_ops.rs to prevent
// parity drift between sequential and parallel checker paths.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::test_support::parse_module;
    use crate::CheckError;
    use crate::Value;

    fn seed_self_loop(checker: &ParallelChecker, x: i64) {
        let mut state = ArrayState::from_values(vec![Value::int(x)]);
        let fp = state.fingerprint(&checker.var_registry);
        checker.seen.insert(fp, state.clone());
        checker.depths.insert(fp, 0);
        let _ = checker.seen_fps.insert_checked(fp);
        checker
            .successors
            .as_ref()
            .expect("liveness-enabled checker should allocate successors")
            .insert(fp, vec![fp]);
        // Part of #4067: Also register as initial state for liveness graph
        // construction. Without this, build_full_state_liveness_cache returns
        // empty init_fps, preventing liveness violation detection.
        checker.liveness_init_states.insert(fp, state);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn periodic_liveness_skips_non_safety_temporal_properties_on_partial_graph() {
        let src = r#"
---- MODULE EventuallyOne ----
VARIABLE x
Init == x = 0
Next == x' = x
P == <>(x = 1)
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            properties: vec!["P".to_string()],
            ..Default::default()
        };

        let checker = ParallelChecker::new(&module, &config, 1);
        seed_self_loop(&checker, 0);

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        ctx.register_vars(checker.vars.iter().cloned());
        ctx.resolve_state_vars_in_loaded_ops();
        let stats = CheckStats::default();

        assert!(
            checker
                .run_periodic_liveness(&mut ctx, &stats, &[])
                .is_none(),
            "mid-BFS partial-graph checks must skip non-safety-temporal properties"
        );

        match checker.run_post_bfs_liveness(&mut ctx, &stats, &[]) {
            Some(CheckResult::LivenessViolation { property, .. }) => {
                assert_eq!(property, "P");
            }
            other => panic!("expected post-BFS liveness violation, got: {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn parallel_liveness_handles_nested_instance_property_refs() {
        let _serial = crate::test_utils::acquire_interner_lock();

        let clean = parse_module(
            r#"
---- MODULE Clean ----
VARIABLE x
EventuallyOne == <>(x = 1)
===="#,
        );
        let stages = parse_module(
            r#"
---- MODULE Stages ----
VARIABLE x
C == INSTANCE Clean WITH x <- x
EventuallyOne == C!EventuallyOne
===="#,
        );
        let product = parse_module(
            r#"
---- MODULE Product ----
VARIABLE x
Init == x = 0
Next == IF x = 0 THEN x' = 1 ELSE x' = x
S == INSTANCE Stages WITH x <- x
EventuallyOne == S!EventuallyOne
===="#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            properties: vec!["EventuallyOne".to_string()],
            ..Default::default()
        };

        let checker = ParallelChecker::new_with_extends(&product, &[&stages, &clean], &config, 2);
        match checker.check() {
            CheckResult::Success(_) | CheckResult::LivenessViolation { .. } => {}
            CheckResult::Error {
                error:
                    CheckError::Liveness(LivenessCheckError::RuntimeFailure(message)),
                ..
            } => {
                panic!(
                    "nested instance liveness property should not fail conversion, got runtime failure: {message}"
                );
            }
            other => panic!(
                "expected nested instance liveness property to finish without a conversion failure, got: {other:?}"
            ),
        }
    }
}
