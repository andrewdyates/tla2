// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Static analysis of ACTION_CONSTRAINT expressions.
//!
//! Pre-analyzes each ACTION_CONSTRAINT at setup time to determine which
//! state variables it references (both primed and unprimed). During BFS,
//! the checker uses this analysis to skip constraint evaluation when none
//! of the referenced variables changed between the current and successor
//! states.
//!
//! This optimization is sound because:
//! - If an ACTION_CONSTRAINT references variables x, y (unprimed) and x', y'
//!   (primed), and none of {x, y} changed between states, then the unprimed
//!   references see the same values and the primed references also see the
//!   same values (since the successor variable values are identical to the
//!   current state for those slots). The constraint will evaluate to the
//!   same result as for a stuttering step on those variables.
//!
//! - More precisely: if the set of changed variables is disjoint from the
//!   set of variables referenced by the constraint (in either primed or
//!   unprimed form), the constraint evaluates identically to the previous
//!   evaluation with the same variable values. Since ACTION_CONSTRAINTs are
//!   pure boolean functions of state variables, the result is deterministic.
//!
//! However, we must be conservative: if the constraint references operators
//! that we cannot fully expand (e.g., recursive operators, or operators with
//! side effects like TLCGet), we mark the constraint as non-skippable.

use rustc_hash::FxHashSet;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::por::{extract_dependencies_ast_expr, ActionDependencies};
use crate::state::ArrayState;
use crate::var_index::VarIndex;
use tla_core::ast::Expr;

use crate::enumerate::expand_operators_with_primes;
use tla_eval::EvalCtx;

/// Pre-computed analysis for a single ACTION_CONSTRAINT.
// Fields `name`, `reads`, `writes` are retained for diagnostics and tests.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) struct ConstraintVarDeps {
    /// The constraint operator name.
    pub(crate) name: String,
    /// VarIndex values that appear unprimed (current state reads).
    pub(crate) reads: FxHashSet<VarIndex>,
    /// VarIndex values that appear primed (next state reads, recorded as writes
    /// by the POR dependency extractor).
    pub(crate) writes: FxHashSet<VarIndex>,
    /// Union of reads and writes as a sorted Vec for fast iteration.
    /// This is the set of variable indices that must be checked for changes.
    pub(crate) all_vars: Vec<VarIndex>,
    /// If true, the constraint references constructs we cannot statically
    /// analyze (e.g., TLCGet, recursive ops), so it must always be evaluated.
    pub(crate) must_always_eval: bool,
}

/// Pre-computed analysis for all ACTION_CONSTRAINTs in a spec.
#[derive(Debug)]
pub(crate) struct ActionConstraintAnalysis {
    /// Per-constraint dependency information.
    pub(crate) constraints: Vec<ConstraintVarDeps>,
    /// Metrics: how many constraint evaluations were skipped.
    pub(crate) skipped: AtomicU64,
    /// Metrics: how many constraint evaluations were performed.
    pub(crate) evaluated: AtomicU64,
}

impl ActionConstraintAnalysis {
    /// Build analysis for all configured ACTION_CONSTRAINTs.
    ///
    /// Resolves each constraint operator name, expands the body through
    /// operator references, and extracts variable dependencies.
    pub(crate) fn build(ctx: &EvalCtx, constraint_names: &[String]) -> Self {
        let mut constraints = Vec::with_capacity(constraint_names.len());
        for name in constraint_names {
            constraints.push(analyze_one_constraint(ctx, name));
        }
        ActionConstraintAnalysis {
            constraints,
            skipped: AtomicU64::new(0),
            evaluated: AtomicU64::new(0),
        }
    }

    /// Check if a constraint can be skipped for a given transition.
    ///
    /// Returns `true` if none of the constraint's referenced variables changed
    /// between `current` and `succ`, meaning the constraint result is the same
    /// as for a stuttering step and can be skipped.
    ///
    /// DISABLED: The skip optimization is unsound for constraints that fail on
    /// stuttering steps. For example, `x' = x + 1` requires the successor to
    /// differ from the current state — when x' == x (no change), the constraint
    /// should FAIL, but the skip optimization assumed it passes. Similarly for
    /// `x' > x`, `x' /= x`, etc. The optimization would need to cache the
    /// result of evaluating the constraint on a stuttering step and only skip
    /// when that cached result is `true`. Until that is implemented, always
    /// evaluate the constraint.
    #[inline]
    pub(crate) fn can_skip_constraint(
        &self,
        _idx: usize,
        _current: &ArrayState,
        _succ: &ArrayState,
    ) -> bool {
        false
    }

    /// Record a skip event.
    #[inline]
    pub(crate) fn record_skip(&self) {
        self.skipped.fetch_add(1, Ordering::Relaxed);
    }

    /// Record an evaluation event.
    #[inline]
    pub(crate) fn record_eval(&self) {
        self.evaluated.fetch_add(1, Ordering::Relaxed);
    }

    /// Get skip count.
    #[allow(dead_code)] // Used in tests; retained for diagnostics
    pub(crate) fn skip_count(&self) -> u64 {
        self.skipped.load(Ordering::Relaxed)
    }

    /// Get evaluation count.
    #[allow(dead_code)] // Retained for diagnostics
    pub(crate) fn eval_count(&self) -> u64 {
        self.evaluated.load(Ordering::Relaxed)
    }

    /// Returns true if there are no analyzable constraints (nothing to optimize).
    #[allow(dead_code)] // Retained for diagnostics
    pub(crate) fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }
}

/// Analyze a single constraint operator to extract variable dependencies.
fn analyze_one_constraint(ctx: &EvalCtx, name: &str) -> ConstraintVarDeps {
    let resolved_name = ctx.resolve_op_name(name);
    let def = ctx.get_op(resolved_name);

    let Some(def) = def else {
        // Cannot resolve operator — must always evaluate.
        return ConstraintVarDeps {
            name: name.to_string(),
            reads: FxHashSet::default(),
            writes: FxHashSet::default(),
            all_vars: Vec::new(),
            must_always_eval: true,
        };
    };

    // Expand operator references so we can see through wrapper ops
    // to the underlying state variable references.
    let expanded = expand_operators_with_primes(ctx, &def.body);

    // Check for constructs that prevent static analysis.
    let must_always_eval = contains_non_analyzable(&expanded.node);

    // Extract variable dependencies using the POR infrastructure.
    let mut deps = ActionDependencies::new();
    extract_dependencies_ast_expr(&expanded.node, &mut deps);

    let mut all_vars: FxHashSet<VarIndex> = FxHashSet::default();
    all_vars.extend(&deps.reads);
    all_vars.extend(&deps.writes);
    let mut all_vars_sorted: Vec<VarIndex> = all_vars.into_iter().collect();
    all_vars_sorted.sort();

    ConstraintVarDeps {
        name: name.to_string(),
        reads: deps.reads,
        writes: deps.writes,
        all_vars: all_vars_sorted,
        must_always_eval,
    }
}

/// Check if an expression contains constructs that prevent static analysis.
///
/// Returns true if the expression uses TLCGet, Print, or other
/// non-deterministic/side-effecting operations that depend on evaluation
/// context beyond just state variable values.
fn contains_non_analyzable(expr: &Expr) -> bool {
    use crate::check::expr_contains;
    use crate::check::ScanDecision;

    expr_contains(expr, &|e| match e {
        // TLCGet("level") or other TLC runtime queries depend on BFS context,
        // not just state variables. Must always evaluate.
        Expr::Apply(op, _) => {
            if let Expr::Ident(name, _) = &op.node {
                if name == "TLCGet" || name == "Print" || name == "PrintT" || name == "Assert" {
                    return ScanDecision::Found;
                }
            }
            ScanDecision::Continue
        }
        _ => ScanDecision::Continue,
    })
}

/// Optimized ACTION_CONSTRAINT evaluation that skips constraints when
/// referenced variables haven't changed.
///
/// This is the drop-in replacement for `check_action_constraints_array`
/// that adds the skip optimization. Falls back to full evaluation when
/// the analysis indicates a constraint cannot be skipped.
pub(crate) fn check_action_constraints_with_analysis(
    ctx: &mut EvalCtx,
    action_constraints: &[String],
    current: &ArrayState,
    succ: &ArrayState,
    analysis: &ActionConstraintAnalysis,
) -> Result<bool, crate::check::CheckError> {
    if action_constraints.is_empty() {
        return Ok(true);
    }

    debug_assert_eq!(action_constraints.len(), analysis.constraints.len());

    // Fast path: check if ALL constraints can be skipped (no referenced vars changed).
    // This avoids binding state/next-state guards entirely.
    let all_skippable =
        (0..action_constraints.len()).all(|i| analysis.can_skip_constraint(i, current, succ));

    if all_skippable {
        analysis
            .skipped
            .fetch_add(action_constraints.len() as u64, Ordering::Relaxed);
        return Ok(true);
    }

    // At least one constraint needs evaluation. Bind both states and
    // evaluate only the constraints that reference changed variables.
    let _state_guard = ctx.bind_state_env_guard(current.env_ref());
    let _next_guard = ctx.bind_next_state_env_guard(succ.env_ref());
    crate::eval::clear_for_bound_state_eval_scope(ctx);

    for (i, constraint_name) in action_constraints.iter().enumerate() {
        if analysis.can_skip_constraint(i, current, succ) {
            analysis.record_skip();
            continue;
        }
        analysis.record_eval();
        if !super::eval_constraint_bool(ctx, constraint_name)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker_setup::{setup_checker_modules, SetupOptions};
    use crate::config::Config;
    use crate::test_support::parse_module;
    use crate::Value;

    fn make_test_ctx_and_analysis(
        src: &str,
        action_constraints: &[&str],
    ) -> (EvalCtx, Vec<String>, ActionConstraintAnalysis) {
        let module = parse_module(src);
        let constraint_names: Vec<String> =
            action_constraints.iter().map(|s| s.to_string()).collect();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            action_constraints: constraint_names.clone(),
            ..Default::default()
        };
        let mut setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        // Resolve Ident nodes to StateVar nodes in operator bodies loaded
        // into the EvalCtx. Without this, the POR dependency extractor
        // cannot see state variable references (it only recognizes
        // Expr::StateVar and Expr::Prime(StateVar), not bare Ident nodes).
        // The production code path (ModelChecker) calls this during setup.
        setup.ctx.resolve_state_vars_in_loaded_ops();
        let analysis = ActionConstraintAnalysis::build(&setup.ctx, &constraint_names);
        (setup.ctx, constraint_names, analysis)
    }

    #[test]
    fn analysis_extracts_reads_and_writes() {
        let src = r#"
---- MODULE AnalysisTest ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
OnlyIncrease == x' > x
====
"#;
        let (ctx, _, analysis) = make_test_ctx_and_analysis(src, &["OnlyIncrease"]);
        let registry = ctx.var_registry().clone();

        assert_eq!(analysis.constraints.len(), 1);
        let deps = &analysis.constraints[0];
        assert!(!deps.must_always_eval);

        // OnlyIncrease references x' (write) and x (read)
        let x_idx = registry.get("x").unwrap();
        assert!(deps.reads.contains(&x_idx) || deps.writes.contains(&x_idx));
        assert!(!deps.all_vars.is_empty());
    }

    #[test]
    fn skip_optimization_disabled_for_soundness() {
        // The skip optimization was unsound: it assumed constraints pass when
        // no referenced variables changed, but constraints like x' > x FAIL
        // on stuttering steps (where x' == x). See the DISABLED comment on
        // can_skip_constraint. This test verifies the optimization is off.
        let src = r#"
---- MODULE SkipTest ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
OnlyIncreaseX == x' > x
====
"#;
        let (ctx, _, analysis) = make_test_ctx_and_analysis(src, &["OnlyIncreaseX"]);
        let registry = ctx.var_registry().clone();

        // Transition where only y changes (x stays the same)
        let current = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]),
            &registry,
        );
        let succ_y_only = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(1)), ("y", Value::int(5))]),
            &registry,
        );

        // Skip optimization is disabled for soundness — always returns false
        assert!(!analysis.can_skip_constraint(0, &current, &succ_y_only));

        // Transition where x changes — also cannot skip (optimization disabled)
        let succ_x_changes = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(2)), ("y", Value::int(0))]),
            &registry,
        );
        assert!(!analysis.can_skip_constraint(0, &current, &succ_x_changes));
    }

    #[test]
    fn no_skip_for_must_always_eval() {
        let src = r#"
---- MODULE TlcGetTest ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
LevelBound == TLCGet("level") < 10
====
"#;
        let (_ctx, _, analysis) = make_test_ctx_and_analysis(src, &["LevelBound"]);

        assert_eq!(analysis.constraints.len(), 1);
        assert!(analysis.constraints[0].must_always_eval);
    }

    #[test]
    fn optimized_eval_matches_baseline() {
        let src = r#"
---- MODULE EvalMatchTest ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' \in {x-1, x, x+1} /\ y' \in {y-1, y, y+1}
OnlyIncrease == x' >= x
====
"#;
        let (mut ctx, names, analysis) = make_test_ctx_and_analysis(src, &["OnlyIncrease"]);
        let registry = ctx.var_registry().clone();

        let current = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]),
            &registry,
        );

        // Successor where x increases (constraint should pass)
        let succ_pass = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(2)), ("y", Value::int(0))]),
            &registry,
        );
        let result = check_action_constraints_with_analysis(
            &mut ctx, &names, &current, &succ_pass, &analysis,
        )
        .unwrap();
        assert!(result, "x increased: constraint should pass");

        // Successor where x decreases (constraint should fail)
        let succ_fail = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]),
            &registry,
        );
        let result = check_action_constraints_with_analysis(
            &mut ctx, &names, &current, &succ_fail, &analysis,
        )
        .unwrap();
        assert!(!result, "x decreased: constraint should fail");

        // Successor where only y changes — constraint x' >= x is satisfied
        // because x' == x (1 >= 1). With skip optimization disabled, this is
        // evaluated through the full constraint path and still passes.
        let succ_y_only = ArrayState::from_state(
            &crate::State::from_pairs([("x", Value::int(1)), ("y", Value::int(5))]),
            &registry,
        );
        let result = check_action_constraints_with_analysis(
            &mut ctx,
            &names,
            &current,
            &succ_y_only,
            &analysis,
        )
        .unwrap();
        assert!(
            result,
            "only y changed, x' >= x holds (1 >= 1): constraint should pass"
        );
        // Skip optimization is disabled for soundness, so skip count stays 0
        assert_eq!(
            analysis.skip_count(),
            0,
            "skip optimization is disabled — no skips should be recorded"
        );
    }

    #[test]
    fn empty_constraints_always_pass() {
        let src = r#"
---- MODULE EmptyTest ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
        let (mut ctx, _, _) = make_test_ctx_and_analysis(src, &[]);
        let analysis = ActionConstraintAnalysis::build(&ctx, &[]);
        let registry = ctx.var_registry().clone();
        let current =
            ArrayState::from_state(&crate::State::from_pairs([("x", Value::int(0))]), &registry);
        let succ =
            ArrayState::from_state(&crate::State::from_pairs([("x", Value::int(1))]), &registry);

        let result =
            check_action_constraints_with_analysis(&mut ctx, &[], &current, &succ, &analysis)
                .unwrap();
        assert!(result);
    }
}
