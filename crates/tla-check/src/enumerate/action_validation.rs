// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-enumeration validation that successor states satisfy action predicates.
//!
//! Split from `guard_check.rs` for file-size hygiene (Part of #3427).

use smallvec::SmallVec;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use crate::Value;
use tla_eval::tir::TirProgram;

use super::tir_leaf::eval_leaf;

use super::debug_enum;
use super::expr_analysis::{
    expr_contains_prime_ctx, flatten_and_spanned, might_contain_action_predicate,
};

/// Validate that successor state satisfies action predicates.
/// Uses ArrayState for O(1) variable access (Part of #131).
pub(super) fn action_holds_in_next_state_array(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    next_array: &ArrayState,
    _registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    let debug = debug_enum();

    // FIX #1819: Use array-based next_state_env (matching the enumeration path)
    // instead of HashMap-based next_state.  The HashMap path causes eval_prime
    // to follow a different code path for complex primed expressions, which can
    // produce divergent results for operators like Serializable' in MCInnerSerial.
    let mut eval_ctx = ctx.clone();
    eval_ctx.bind_next_state_env(next_array.env_ref());
    *eval_ctx.next_state_mut() = None;

    // Validate conjuncts that might contain action predicates
    let mut conjuncts = SmallVec::new();
    flatten_and_spanned(expr, &mut conjuncts);

    for conjunct in &conjuncts {
        if !might_contain_action_predicate(&conjunct.node) {
            continue;
        }

        // Part of #1100: Skip EXISTS conjuncts that contain primed assignments.
        // Same rationale as action_holds_in_next_state - see comment there.
        if matches!(&conjunct.node, Expr::Exists(_, body) if expr_contains_prime_ctx(ctx, &body.node))
        {
            if debug {
                eprintln!(
                    "action_holds_in_next_state_array: skipping EXISTS with primed body at span {:?}",
                    conjunct.span
                );
            }
            continue;
        }

        match eval_leaf(&eval_ctx, conjunct, tir) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                if debug {
                    eprintln!(
                        "action_holds_in_next_state_array: prime-guard false at span {:?}",
                        conjunct.span
                    );
                }
                return Ok(false);
            }
            Ok(other) => {
                if debug {
                    eprintln!(
                        "action_holds_in_next_state_array: prime-guard non-boolean ({}) at span {:?}",
                        other.type_name(),
                        conjunct.span
                    );
                }
                return Err(EvalError::TypeError {
                    expected: "BOOLEAN",
                    got: other.type_name(),
                    span: Some(conjunct.span),
                });
            }
            Err(e) => {
                if debug {
                    eprintln!(
                        "action_holds_in_next_state_array: prime-guard eval error ({:?}) at span {:?}",
                        e, conjunct.span
                    );
                }
                return Err(e);
            }
        }
    }

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;

    /// Regression test for #1819: action_holds_in_next_state_array must use array-based
    /// eval context (bind_next_state_array) to match the enumeration path. The HashMap
    /// path can produce divergent results for primed operator references.
    ///
    /// This test creates a spec where:
    /// - An operator `IsPositive` references `y'` (primed variable)
    /// - The Next action references `IsPositive` (triggering might_need_prime_binding)
    /// - A valid successor {x = 1, y = 2} is validated via array-based context
    /// - The validation must return true (not false-prune the successor)
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_1819_action_holds_array_context_primed_operator_ref() {
        let module = parse_module(
            r#"
---- MODULE PrimeOpRef ----
VARIABLES x, y
IsPositive == y' > 0
Next == /\ x' = x + 1
        /\ y' = 2
        /\ IsPositive
====
"#,
        );

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        ctx.register_var("x");
        ctx.register_var("y");
        // Set current state: x = 0, y = 0
        ctx.bind_state_array(&[Value::int(0), Value::int(0)]);
        let registry = ctx.var_registry().clone();

        let next_expr = module
            .units
            .iter()
            .find_map(|u| match &u.node {
                tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => {
                    Some(def.body.clone())
                }
                _ => None,
            })
            .expect("Next operator should exist");

        // Successor state: x = 1, y = 2 (valid per Next action)
        let next_array = ArrayState::from_values(vec![Value::int(1), Value::int(2)]);
        let result =
            action_holds_in_next_state_array(&ctx, &next_expr, &next_array, &registry, None);

        assert!(
            matches!(result, Ok(true)),
            "#1819 regression: action_holds_in_next_state_array with array context \
             must accept valid successors containing primed operator refs. \
             Got: {:?}",
            result
        );
    }

    /// Test that action_holds_in_next_state_array correctly rejects an invalid
    /// successor state when primed operator references are involved.
    /// Part of #1819: ensures array-based context properly evaluates primed guards.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_1819_action_holds_array_context_rejects_invalid() {
        let module = parse_module(
            r#"
---- MODULE PrimeOpRefInvalid ----
VARIABLES x, y
IsPositive == y' > 0
Next == /\ x' = x + 1
        /\ y' \in {-1, 0, 1}
        /\ IsPositive
====
"#,
        );

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        ctx.register_var("x");
        ctx.register_var("y");
        ctx.bind_state_array(&[Value::int(0), Value::int(0)]);
        let registry = ctx.var_registry().clone();

        let next_expr = module
            .units
            .iter()
            .find_map(|u| match &u.node {
                tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => {
                    Some(def.body.clone())
                }
                _ => None,
            })
            .expect("Next operator should exist");

        // Invalid successor: y = -1 (IsPositive requires y' > 0)
        let invalid_next = ArrayState::from_values(vec![Value::int(1), Value::int(-1)]);
        let result =
            action_holds_in_next_state_array(&ctx, &next_expr, &invalid_next, &registry, None);

        assert!(
            matches!(result, Ok(false)),
            "#1819: action_holds_in_next_state_array should reject invalid successor \
             where primed operator ref evaluates to false. Got: {:?}",
            result
        );

        // Valid successor: y = 1 (IsPositive satisfied)
        let valid_next = ArrayState::from_values(vec![Value::int(1), Value::int(1)]);
        let result =
            action_holds_in_next_state_array(&ctx, &next_expr, &valid_next, &registry, None);

        assert!(
            matches!(result, Ok(true)),
            "#1819: action_holds_in_next_state_array should accept valid successor \
             where primed operator ref evaluates to true. Got: {:?}",
            result
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_1467_action_holds_propagates_guard_eval_error() {
        let module = parse_module(
            r#"
---- MODULE GuardError ----
VARIABLE x
Next == /\ UndefinedGuardOp(x')
        /\ x' = 1
====
"#,
        );

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        ctx.register_var("x");
        let registry = ctx.var_registry().clone();

        let next_expr = module
            .units
            .iter()
            .find_map(|u| match &u.node {
                tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => {
                    Some(def.body.clone())
                }
                _ => None,
            })
            .expect("Next operator should exist");

        let next_array = ArrayState::from_values(vec![Value::int(1)]);
        let result =
            action_holds_in_next_state_array(&ctx, &next_expr, &next_array, &registry, None);

        assert!(
            matches!(result, Err(EvalError::UndefinedOp { .. })),
            "#1467 regression: guard eval errors in post-validation must propagate"
        );
    }
}
