// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Catchall branch tests (issue #1432)
// ========================================================================

/// Regression test for #1432: The catch-all branch in enumerate_unified_inner
/// previously discarded the eval result entirely (`let _eval_result = eval(...)`)
/// and returned Ok(()). This meant fatal eval errors were silently swallowed,
/// turning spec bugs into silent branch elimination.
///
/// After the fix, non-disabled-action errors are propagated from the catch-all.
/// This test verifies that TypeError from `\neg x'` propagates as Err.
///
/// Key flow:
/// 1. `check_and_guards` sees `\neg x'` (contains Prime) → not a guard → Ok(true)
/// 2. Conjuncts processed: `x' = x + 1` produces assignment, then `\neg x'` hits catch-all
/// 3. `extract_symbolic_assignments` for `Not` → empty (no assignments)
/// 4. `eval(ctx, \neg x')` with x'=1 bound → `eval_not(1)` → TypeError("BOOLEAN","integer")
/// 5. TypeError is NOT a disabled-action error → Err propagates through catch-all
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1432_catchall_propagates_fatal_eval_error() {
    let src = r#"
---- MODULE Test1432 ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ \neg x'
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    assert!(
        result.is_err(),
        "#1432 regression: TypeError from catch-all branch must propagate, got Ok"
    );
    assert!(
        matches!(result.unwrap_err(), EvalError::TypeError { .. }),
        "#1432 regression: expected TypeError, got different error"
    );
}

/// Regression test for #1432: Disabled-action errors from the catch-all branch
/// should still be swallowed (action is disabled, not a spec bug).
/// This verifies the `Err(e) if is_disabled_action_error(&e)` arm works.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1432_catchall_swallows_disabled_action_error() {
    // `\neg (1 \div 0 = 0)` — Not wraps Eq wraps DivisionByZero.
    // Not is a catch-all expression type. Symbolic extraction returns empty.
    // eval produces DivisionByZero (a disabled-action error), which should
    // be swallowed and return Ok with no successors.
    let src = r#"
---- MODULE Test1432b ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ \neg (1 \div 0 = 0)
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    // Fix #1552: TLC propagates DivisionByZero fatally from action evaluation.
    // Previously this was suppressed as a "disabled action" error — incorrect.
    let err = result.expect_err(
        "#1552: DivisionByZero in action should propagate as fatal error, not be suppressed",
    );
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "#1634: expected DivisionByZero, got {err:?}"
    );
}

/// Regression test for #1740: non-boolean CASE guard in symbolic assignment extraction
/// must propagate as CaseGuardError.
///
/// This exercises the `extract_case_symbolic_assignments` path in symbolic_assignments.rs,
/// NOT the `conjunct_case` path in unified.rs. The difference: here the CASE expression
/// CONTAINS the primed assignment (`CASE guard -> x' = value`) rather than being a
/// separate guard conjunct.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1740_symbolic_case_guard_non_boolean_is_fatal() {
    let src = r#"
---- MODULE Test1740SymbolicNonBool ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == CASE 42 -> x' = 1
     [] OTHER -> x' = 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err =
        result.expect_err("#1740: non-boolean CASE guard in symbolic extraction must be fatal");
    match err {
        EvalError::CaseGuardError { source, .. } => {
            assert!(
                matches!(&*source, EvalError::TypeError { .. }),
                "#1740: expected wrapped TypeError, got {:?}",
                source
            );
        }
        other => panic!("#1740: expected CaseGuardError, got {other:?}"),
    }
}

/// Regression test for #1740: CASE guard eval error in symbolic assignment extraction
/// must propagate as CaseGuardError.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1740_symbolic_case_guard_eval_error_is_fatal() {
    let src = r#"
---- MODULE Test1740SymbolicEvalErr ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == CASE 1 \div 0 = 0 -> x' = 1
     [] OTHER -> x' = 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err =
        result.expect_err("#1740: CASE guard eval error in symbolic extraction must be fatal");
    match err {
        EvalError::CaseGuardError { source, .. } => {
            assert!(
                matches!(&*source, EvalError::DivisionByZero { .. }),
                "#1740: expected wrapped DivisionByZero, got {:?}",
                source
            );
        }
        other => panic!("#1740: expected CaseGuardError, got {other:?}"),
    }
}

/// Regression test for #1723: non-boolean IF condition in symbolic assignment extraction
/// must propagate as TypeError, not silently merge both branches.
///
/// TLC: "Error: A non-boolean expression was used as the condition of an IF."
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1723_if_condition_non_boolean_is_fatal() {
    let src = r#"
---- MODULE Test1723IfNonBool ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF 42 THEN x' = 1 ELSE x' = 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1723: non-boolean IF condition must be fatal TypeError");
    assert!(
        matches!(
            err,
            EvalError::TypeError {
                expected: "BOOLEAN",
                ..
            }
        ),
        "#1723: expected TypeError{{BOOLEAN}}, got {err:?}"
    );
}

/// Regression test for #1723: eval error in IF guard condition (no primed vars)
/// must propagate, not silently merge branches.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1723_if_guard_eval_error_propagates() {
    let src = r#"
---- MODULE Test1723IfGuardErr ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF 1 \div 0 = 0 THEN x' = 1 ELSE x' = 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1723: eval error in IF guard condition must propagate");
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "#1723: expected DivisionByZero, got {err:?}"
    );
}

/// Regression test for #1732: CASE exhaustion (no arm matches, no OTHER) in symbolic
/// assignment extraction must propagate CaseNoMatch, not silently return Ok(()).
///
/// TLC: Assert.fail("Attempted to evaluate a CASE expression, and none of the conditions were true.")
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1732_symbolic_case_exhaustion_is_fatal() {
    let src = r#"
---- MODULE Test1732CaseExhaustion ----
EXTENDS Integers
VARIABLE x
Init == x = 0
\* All guards are FALSE when x = 0, no OTHER clause
Next == CASE x = 1 -> x' = 2
     [] x = 2 -> x' = 3
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1732: CASE exhaustion in symbolic extraction must be fatal");
    assert!(
        matches!(err, EvalError::CaseNoMatch { .. }),
        "#1732: expected CaseNoMatch, got {err:?}"
    );
}
