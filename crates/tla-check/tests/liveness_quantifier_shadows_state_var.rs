// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2116: WF_/SF_ simple-identifier subscripts can
//! capture quantifier bindings when `resolve_action_expr` eagerly inlines the
//! operator body into the quantifier scope.
//!
//! TLC semantics require that an operator like `vars == <<x, p>>` retains its
//! lexical scope when referenced as a fairness subscript inside `\A p \in
//! Procs : WF_vars(Step(p))`. The bug was that `resolve_action_expr` inlined
//! the body of `vars` as `Tuple([x, p])`, exposing the inlined `p` to the
//! quantifier-bound `p` from the enclosing `\A`. The fix preserves the
//! operator boundary by keeping simple identifier subscripts as `Ident("vars")`
//! at conversion time, so runtime evaluation resolves `vars` through its
//! operator definition in lexical scope.

use tla_check::CheckResult;
use tla_check::Config;

mod common;

/// Test that a quantifier-bound variable correctly shadows a state variable
/// of a different name during ENABLED evaluation in the liveness fast path.
///
/// The spec has state variable `p` (value 0) and a fairness property that
/// quantifies `\A p_var \in Procs : WF_vars(Step(p_var))`. The bound
/// `p_var` must not be confused with the state variable `p`.
///
/// Uses a bounded state space (x in {0, 1}) to ensure termination.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn quantifier_bound_var_shadows_state_var_in_enabled() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessQuantifierShadowsStateVar ----

VARIABLES x, p

Procs == {1, 2}

Init ==
    /\ x = 0
    /\ p = 0

Step(proc) ==
    /\ proc \in Procs
    /\ x' = IF x = 0 THEN proc ELSE x
    /\ p' = p

Next ==
    \/ \E proc \in Procs : Step(proc)
    \/ UNCHANGED <<x, p>>

vars == <<x, p>>

Fairness == \A p_var \in Procs : WF_vars(Step(p_var))

Prop == Fairness => <>(x > 0)

====
"#;

    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Expected: the property holds because WF ensures Step
            // is eventually taken, making x > 0.
            // States: (x=0,p=0), (x=1,p=0), (x=2,p=0) = 3 states
            assert!(
                stats.states_found >= 2,
                "spec should explore at least 2 states (init + one step), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            assert!(
                !msg.contains("Undefined variable"),
                "quantifier binding lost — undefined variable error: {msg}"
            );
            panic!("expected Success, got Error: {msg}");
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}

/// Direct test: use the exact same name `p` for both the state variable
/// and the quantifier-bound variable. This is the exact collision scenario
/// described in #2116.
///
/// The spec has state variable `p` (value 0) and the fairness property
/// `\A p \in Procs : WF_vars(Step(p))` where the bound `p` shadows
/// the state variable `p`. During ENABLED evaluation, the bound value
/// (1 or 2) must be used, not the state value (0).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn exact_name_collision_quantifier_bound_var_and_state_var() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessExactNameCollision ----

VARIABLES x, p

Procs == {1, 2}

Init ==
    /\ x = 0
    /\ p = 0

Step(proc) ==
    /\ proc \in Procs
    /\ x' = IF x = 0 THEN proc ELSE x
    /\ p' = p

Next ==
    \/ \E proc \in Procs : Step(proc)
    \/ UNCHANGED <<x, p>>

vars == <<x, p>>

\* Here `p` in `\A p \in Procs` shadows the state variable `p`.
\* During ENABLED evaluation of WF_vars(Step(p)), the bound p must
\* take the quantifier value (1 or 2), not the state value (0).
Fairness == \A p \in Procs : WF_vars(Step(p))

Prop == Fairness => <>(x > 0)

====
"#;

    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Expected: property holds. The quantifier-bound p correctly
            // shadows state variable p, so ENABLED evaluates correctly.
            assert!(
                stats.states_found >= 2,
                "spec should explore at least 2 states (init + one step), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            assert!(
                !msg.contains("Undefined variable"),
                "quantifier binding lost — undefined variable error: {msg}"
            );
            panic!("expected Success, got Error: {msg}");
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}
