// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #3166: INSTANCE substitution must propagate to
//! transitively-referenced operators in the compiled guard path.
//!
//! When `I == INSTANCE Inner WITH x <- y` and `Inner!Inv` calls helper operator
//! `B` which references variable `x`, the substitution `x <- y` must be applied
//! to `B`'s body as well, not just to `Inv`'s body. Without this fix, the
//! compiled guard evaluator hits "Undefined variable: x" because `B` still
//! references the unsubstituted variable name.
//!
//! The fix (in `compile_module_ref_guard`) applies INSTANCE substitutions to ALL
//! operators in the instance module's `local_ops` before building the merged scope.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::FileId;

fn assert_success(result: CheckResult, expected_states: usize, label: &str) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Bug #3166 ({label}): expected {expected_states} states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #3166 regression ({label}): INSTANCE invariant with transitive \
                 operator reference failed. Result: {other:?}"
            );
        }
    }
}

/// Inner module: VARIABLE `x`, helper `B == x > 0`, invariant `Inv == B \/ x = 0`.
fn inner_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers
VARIABLE x
B == x > 0
Inv == B \/ x = 0
Init == x = 0
Next == x' = (x + 1) % 3
====
"#,
        FileId(1),
    )
}

/// Regression test for #3166: INVARIANT through INSTANCE with transitive
/// operator references exercises the compiled guard path.
///
/// Without the fix, this crashes with "Undefined variable: x" because
/// `compile_module_ref_guard` only substitutes the top-level operator body
/// (`Inv`) but not the transitively-referenced operator (`B`).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3166_instance_invariant_transitive_operator_substitution() {
    let inner = inner_module();
    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = (y + 1) % 3
I == INSTANCE Inner WITH x <- y
OuterInv == I!Inv
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        por_enabled: false,
        auto_por: Some(false),
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_success(checker.check(), 3, "transitive operator");
}

/// Regression test for #3166: deep chain `Inv -> C -> B`, each referencing
/// substituted variable `x`. All operators must have `x <- y` applied.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3166_instance_deep_transitive_chain() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE InnerDeep ----
EXTENDS Integers
VARIABLE x
B == x >= 0
C == B /\ x < 10
Inv == C
Init == x = 0
Next == x' = (x + 1) % 5
====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE OuterDeep ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = (y + 1) % 5
I == INSTANCE InnerDeep WITH x <- y
OuterInv == I!Inv
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        por_enabled: false,
        auto_por: Some(false),
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_success(checker.check(), 5, "deep chain");
}

/// Protocol module with 3 variables and 3 helper operators.
fn protocol_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE Protocol ----
EXTENDS Integers
VARIABLE active, pending, color
IsBool == active \in {TRUE, FALSE}
IsNat == pending >= 0
IsColor == color \in {"white", "black"}
Inv == IsBool /\ IsNat /\ IsColor
Init == active = TRUE /\ pending = 0 /\ color = "white"
Next ==
    \/ (active' = FALSE /\ pending' = pending /\ color' = color)
    \/ (active' = active /\ pending' = (pending + 1) % 3 /\ color' = "black")
    \/ (active' = active /\ pending' = 0 /\ color' = "white")
====
"#,
        FileId(1),
    )
}

/// System module that INSTANCEs Protocol with 3 variable substitutions.
fn system_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE System ----
EXTENDS Integers
VARIABLE a, p, c
Init == a = TRUE /\ p = 0 /\ c = "white"
Next ==
    \/ (a' = FALSE /\ p' = p /\ c' = c)
    \/ (a' = a /\ p' = (p + 1) % 3 /\ c' = "black")
    \/ (a' = a /\ p' = 0 /\ c' = "white")
Proto == INSTANCE Protocol WITH active <- a, pending <- p, color <- c
SysInv == Proto!Inv
====
"#,
        FileId(0),
    )
}

/// Regression test for #3166: multi-variable INSTANCE substitution matching
/// the EWD998Chan pattern. Three substituted variables, three helper operators.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3166_instance_multi_variable_substitution() {
    let inner = protocol_module();
    let outer = system_module();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SysInv".to_string()],
        check_deadlock: false,
        por_enabled: false,
        auto_por: Some(false),
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    // active={T,F}, pending={0,1,2}, color={"white","black"} — 8 reachable states.
    assert_success(checker.check(), 8, "multi-variable");
}
