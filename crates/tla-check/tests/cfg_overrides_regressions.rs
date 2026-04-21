// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for module-scoped .cfg overrides.

mod common;

use std::collections::HashMap;
use tla_check::ConfigCheckError;
use tla_check::{CheckError, CheckResult, Config, ModelChecker};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cfg_scoped_override_can_shadow_builtin_in_extended_module() {
    // Real configs override Nat/Int/Real inside extended modules to make domains finite.
    let z_src = r#"
---- MODULE Z ----
Ballot == Nat
====
"#;
    let main_src = r#"
---- MODULE Main ----
EXTENDS Z
VARIABLE x
NatOverride == 1..3
Init == x \in Ballot
Next == FALSE
Inv == x \in 1..3
====
"#;

    let z = common::parse_module(z_src);
    let main = common::parse_module(main_src);

    let module_overrides = HashMap::from([(
        "Z".to_string(),
        HashMap::from([("Nat".to_string(), "NatOverride".to_string())]),
    )]);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        module_overrides,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&main, &[&z], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Init == x \in Ballot, Ballot overridden from Nat to 1..3.
            // 3 initial states (x=1, x=2, x=3), Next == FALSE. 3 total states.
            assert_eq!(stats.initial_states, 3, "expected 3 initial states (1..3)");
            assert_eq!(stats.states_found, 3, "expected 3 total states");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cfg_scoped_override_lhs_can_come_from_instance_import() {
    let base_src = r#"
---- MODULE Base ----
X == 1..10
====
"#;

    let z_src = r#"
---- MODULE Z ----
LOCAL INSTANCE Base
ZBallot == X
====
"#;

    let main_src = r#"
---- MODULE Main ----
EXTENDS Z
VARIABLE v
XOverride == 1..3
Init == v = 1
Next == FALSE
Inv == Cardinality(ZBallot) = 3
====
"#;

    let base = common::parse_module(base_src);
    let z = common::parse_module(z_src);
    let main = common::parse_module(main_src);

    let module_overrides = HashMap::from([(
        "Z".to_string(),
        HashMap::from([("X".to_string(), "XOverride".to_string())]),
    )]);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        module_overrides,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&main, &[&base, &z], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Init == v = 1, Next == FALSE. 1 initial state, 1 total state.
            // Inv checks Cardinality(ZBallot) = 3 where X overridden to 1..3.
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert_eq!(stats.states_found, 1, "expected 1 total state");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cfg_scoped_override_rhs_must_be_root_visible() {
    let z_src = r#"
---- MODULE Z ----
X == 1..3
====
"#;
    let main_src = r#"
---- MODULE Main ----
EXTENDS Z
VARIABLE v
Init == v \\in X
Next == FALSE
Inv == v \\in 1..3
====
"#;

    let z = common::parse_module(z_src);
    let main = common::parse_module(main_src);

    let module_overrides = HashMap::from([(
        "Z".to_string(),
        HashMap::from([("X".to_string(), "NoSuchOp".to_string())]),
    )]);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        module_overrides,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&main, &[&z], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Config(ConfigCheckError::Config(_)),
                ..
            }
        ),
        "{result:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cfg_root_override_applies_to_instance_qualified_operator() {
    // TLC supports overriding instance-qualified operator names like `I!X <- XOverride`
    // via the CONSTANTS override mechanism (Bug44).
    //
    // This regression ensures TLA2 applies the same override to `Expr::ModuleRef`
    // evaluation, not just to unqualified identifier lookups.
    let foo_src = r#"
---- MODULE Foo ----
X == 1
====
"#;

    let main_src = r#"
---- MODULE Main ----
I == INSTANCE Foo
VARIABLE v
XOverride == 3
Init == v = I!X
Next == v' = v
Inv == v = 1
====
"#;

    let foo = common::parse_module(foo_src);
    let main = common::parse_module(main_src);

    let cfg_src = r#"
INIT Init
NEXT Next
INVARIANT Inv
CONSTANTS
I!X <- XOverride
"#;
    let config = Config::parse(cfg_src).expect("config parse");

    let mut checker = ModelChecker::new_with_extends(&main, &[&foo], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    let CheckResult::InvariantViolation {
        invariant,
        trace,
        stats: _,
    } = result
    else {
        panic!("Expected InvariantViolation, got: {result:?}");
    };
    assert_eq!(invariant, "Inv");
    assert!(
        !trace.states.is_empty(),
        "Expected at least one state in the counterexample trace"
    );
    let s0 = &trace.states[0];
    let v = s0
        .vars()
        .find(|(name, _)| name.as_ref() == "v")
        .map(|(_, v)| v.clone())
        .expect("expected v in initial state");
    assert_eq!(v.to_string(), "3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cfg_parse_module_scoped_override_allows_qualified_lhs() {
    let cfg_src = r#"
INIT Init
NEXT Next
CONSTANTS
I!X <- [Foo] XOverride
Def!1 <- [Foo] DefOverride
"#;
    let config = Config::parse(cfg_src).expect("config parse");
    assert_eq!(
        config
            .module_overrides
            .get("Foo")
            .and_then(|m| m.get("I!X"))
            .map(std::string::String::as_str),
        Some("XOverride")
    );
    assert_eq!(
        config
            .module_overrides
            .get("Foo")
            .and_then(|m| m.get("Def!1"))
            .map(std::string::String::as_str),
        Some("DefOverride")
    );
}
