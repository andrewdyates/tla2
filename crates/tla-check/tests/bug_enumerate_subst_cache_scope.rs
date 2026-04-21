// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{check_module, CheckResult, Config, ModelChecker};
use tla_core::FileId;

/// Regression for #3104: the same `F(x)` call site is evaluated under two
/// different higher-order operator scopes (`F <- Op1` and `F <- Op2`).
///
/// `enumerate::subst_cache` used to key only by the `F(x)` AST pointer, so the
/// first substituted body could be reused for both operator resolutions. With
/// `Op1(v) == v' = 1` and `Op2(v) == v' = 2`, that collapses the state space
/// from `{0,1,2}` to `{0,1}`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_3104_subst_cache_discriminates_higher_order_scope() {
    let module = common::parse_module_strict_with_id(
        r#"
---- MODULE EnumSubstCacheScope ----
EXTENDS Integers

VARIABLE x

Op1(v) == v' = 1
Op2(v) == v' = 2

Wrap(F(_)) == F(x)

Init == x = 0
Next == Wrap(Op1) \/ Wrap(Op2)
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "same F(x) call site under Op1/Op2 must reach states {{0,1,2}}, got {}",
                stats.states_found
            );
        }
        other => panic!("expected Success for higher-order scope regression, got {other:?}"),
    }
}

/// Regression for #3104 through the INSTANCE/module-ref path described in the
/// design. The shared inner call site `F(v)` inside `Inner!Act` must resolve
/// against the surrounding branch-local `LET F`.
///
/// When `enumerate::subst_cache` keyed only by the `F(v)` AST pointer, the
/// second branch could reuse the first branch's substituted body and collapse
/// `{0,1,2}` to `{0,1}`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_3104_subst_cache_discriminates_instance_module_ref_scope() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLE x

Act(v) == F(v)
====
"#,
        FileId(1),
    );
    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE x

I == INSTANCE Inner

Init == x = 0
Next ==
    \/ (LET F(v) == x' = 1 IN I!Act(1))
    \/ (LET F(v) == x' = 2 IN I!Act(2))
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "Inner!Act must preserve both branch-local LET F bindings, got {}",
                stats.states_found
            );
        }
        other => panic!("expected Success for module-ref scope regression, got {other:?}"),
    }
}
