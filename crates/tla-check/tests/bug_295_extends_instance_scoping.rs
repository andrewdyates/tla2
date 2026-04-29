// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for bug #295 (EXTENDS-vs-INSTANCE variable scoping).
//!
//! Bug #295: INSTANCE'd modules were incorrectly contributing variables to the
//! main module's state space. Only EXTENDS'd modules should contribute variables;
//! INSTANCE'd modules have their variables substituted by the INSTANCE mechanism.
//!
//! Without the fix, INSTANCE'd module variables inflate the state vector, producing
//! incorrect state counts and potential false positives in refinement checks.
//!
//! The fix is implemented in checker_setup.rs (shared pipeline):
//! - setup_imports: compute_import_sets() / collect_ops_vars_and_assumes()
//! - Both ModelChecker and ParallelChecker use the shared pipeline via setup_checker_modules().

mod common;

use tla_check::{CheckResult, Config, ModelChecker, ParallelChecker};
use tla_core::FileId;

static PARALLEL_CHECK_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn acquire_parallel_check_lock() -> std::sync::MutexGuard<'static, ()> {
    PARALLEL_CHECK_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Inner module with VARIABLES x, y — reused across INSTANCE tests.
fn inner_xy_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLES x, y

Init == x = 0 /\ y = 0

Next ==
    \/ (x' = x + 1 /\ y' = y)
    \/ (x' = x /\ y' = y + 1)

====
"#,
        FileId(1),
    )
}

/// Config with explicit INIT/NEXT and a Constraint to bound the state space.
fn bounded_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Constraint".to_string()],
        check_deadlock: false,
        por_enabled: false,
        auto_por: Some(false),
        ..Default::default()
    }
}

/// Run the model checker and assert it succeeds with the expected state count.
fn assert_state_count(
    outer: &tla_core::ast::Module,
    extended_modules: &[&tla_core::ast::Module],
    config: &Config,
    expected_states: usize,
    context: &str,
) {
    let mut checker = ModelChecker::new_with_extends(outer, extended_modules, config);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "{context}: expected {expected_states} states, got {}",
                stats.states_found
            );
            assert_eq!(
                stats.initial_states, 1,
                "{context}: expected one initial state"
            );
        }
        other => panic!("{context}: expected Success, got: {other:?}"),
    }
}

fn assert_parallel_parity_state_count(
    outer: &tla_core::ast::Module,
    extended_modules: &[&tla_core::ast::Module],
    config: &Config,
    expected_states: usize,
    context: &str,
) {
    let _serial = acquire_parallel_check_lock();

    let mut seq_checker = ModelChecker::new_with_extends(outer, extended_modules, config);
    let seq_result = seq_checker.check();
    let seq_states = match &seq_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("{context}: sequential expected Success, got: {other:?}"),
    };

    let mut par_checker = ParallelChecker::new_with_extends(outer, extended_modules, config, 2);
    par_checker.set_deadlock_check(config.check_deadlock);
    let par_result = par_checker.check();
    let par_states = match &par_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("{context}: parallel expected Success, got: {other:?}"),
    };

    assert_eq!(
        seq_states, par_states,
        "{context}: parallel/sequential state mismatch: seq={seq_states}, par={par_states}"
    );
    assert_eq!(
        seq_states, expected_states,
        "{context}: expected {expected_states} states, got {seq_states}"
    );
}

/// Bug #295 regression: named INSTANCE WITH explicit substitution.
///
/// Outer has 1 variable (data, a tuple). Inner has 2 variables (x, y).
/// INSTANCE WITH substitutes Inner's x and y with operators from Outer's data.
/// Therefore Inner's x and y must NOT appear in Outer's state space.
///
/// State space: data ∈ {<<0,0>>, <<0,1>>, <<1,0>>, <<1,1>>} = 4 states.
/// TLC baseline: 4 distinct states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_named_instance_with_explicit_substitution_state_count() {
    let inner = inner_xy_module();
    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE data

GetX == data[1]
GetY == data[2]

\* Named INSTANCE: Inner's variables x, y are substituted, NOT added to state space
I == INSTANCE Inner WITH x <- GetX, y <- GetY

Init == data = <<0, 0>>

Next ==
    \/ data' = <<data[1] + 1, data[2]>>
    \/ data' = <<data[1], data[2] + 1>>

Constraint == data[1] < 2 /\ data[2] < 2

====
"#,
        FileId(0),
    );

    assert_state_count(
        &outer,
        &[&inner],
        &bounded_config(),
        4,
        "bug #295 regression: named INSTANCE WITH should not inflate state space",
    );
}

/// Bug #295 regression: named INSTANCE with implicit substitution.
///
/// Inner's variables are implicitly substituted because Outer defines
/// operators with the same names (x, y).
///
/// TLC baseline: 4 distinct states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_named_instance_implicit_substitution_state_count() {
    let inner = inner_xy_module();
    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE data

\* Same names as Inner's variables -> implicit substitution
x == data[1]
y == data[2]

\* Named INSTANCE without WITH: implicit substitution of x, y
I == INSTANCE Inner

Init == data = <<0, 0>>

Next ==
    \/ data' = <<data[1] + 1, data[2]>>
    \/ data' = <<data[1], data[2] + 1>>

Constraint == data[1] < 2 /\ data[2] < 2

====
"#,
        FileId(0),
    );

    assert_state_count(
        &outer,
        &[&inner],
        &bounded_config(),
        4,
        "bug #295 regression: implicit INSTANCE should not inflate state space",
    );
}

/// Bug #295 regression: standalone INSTANCE (unqualified import).
///
/// Standalone `INSTANCE Inner` imports Inner's operators unqualified into the
/// outer module, but must NOT import Inner's variables. This is the pattern
/// that originally triggered bug #295 in EWD998PCal.
///
/// TLC baseline: 4 distinct states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_standalone_instance_does_not_contribute_variables() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLES x, y

InnerOp == x + y

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE data

\* Operators matching Inner's variables for substitution
x == data[1]
y == data[2]

\* Standalone INSTANCE: imports operators unqualified, but NOT variables
INSTANCE Inner

Init == data = <<0, 0>>

Next ==
    \/ data' = <<data[1] + 1, data[2]>>
    \/ data' = <<data[1], data[2] + 1>>

Constraint == data[1] < 2 /\ data[2] < 2

====
"#,
        FileId(0),
    );

    assert_state_count(
        &outer,
        &[&inner],
        &bounded_config(),
        4,
        "bug #295 regression: standalone INSTANCE should not contribute variables",
    );
}

/// Regression for #3086: standalone `INSTANCE ... WITH` must rewrite imported
/// `Init`/`Next` bodies before the checker uses them from the unqualified namespace.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_standalone_instance_with_explicit_substitution_imports_init_next() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = x + 1

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE y

INSTANCE Inner WITH x <- y

Constraint == y < 2

====
"#,
        FileId(0),
    );

    assert_parallel_parity_state_count(
        &outer,
        &[&inner],
        &bounded_config(),
        2,
        "standalone INSTANCE WITH should materialize imported Init/Next bodies",
    );
}

/// Regression for #3086: imported ASSUMEs must see the standalone `WITH`
/// substitutions rather than the raw inner-module constant/variable names.
///
/// Uses a CONSTANT in the ASSUME (not a VARIABLE) because ASSUMEs are
/// evaluated at setup time before any state exists. The substitution
/// replaces `c <- 0`, so `ASSUME c \in 0..1` becomes `ASSUME 0 \in 0..1`
/// which evaluates to TRUE. Without substitution, `c` would be undefined.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_standalone_instance_with_explicit_substitution_imports_assume() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

CONSTANT c
VARIABLE x

ASSUME c \in 0..1
Init == x = c
Next == x' = x

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE y

INSTANCE Inner WITH x <- y, c <- 0

====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        por_enabled: false,
        auto_por: Some(false),
        ..Default::default()
    };

    assert_parallel_parity_state_count(
        &outer,
        &[&inner],
        &config,
        1,
        "standalone INSTANCE WITH should materialize imported ASSUME bodies",
    );
}

/// Regression for #3086: outer standalone `WITH` substitutions must propagate
/// through nested standalone imports inside the imported module.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_standalone_instance_with_explicit_substitution_propagates_to_nested_import() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLE z

Init == z = 0
Next == z' = z + 1

====
"#,
        FileId(2),
    );

    let middle = common::parse_module_strict_with_id(
        r#"
---- MODULE Middle ----
EXTENDS Integers

VARIABLE x

INSTANCE Inner WITH z <- x

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE y

INSTANCE Middle WITH x <- y

Constraint == y < 2

====
"#,
        FileId(0),
    );

    assert_parallel_parity_state_count(
        &outer,
        &[&middle, &inner],
        &bounded_config(),
        2,
        "outer standalone INSTANCE WITH should materialize nested imported Init/Next bodies",
    );
}

/// Positive control: EXTENDS DOES contribute variables.
///
/// When a module uses EXTENDS (not INSTANCE), the extended module's variables
/// are part of the outer module's state space. This verifies the fix didn't
/// break EXTENDS behavior.
///
/// Outer has VARIABLE a. Extended has VARIABLE b. Both contribute to state space.
/// State space: (a, b) ∈ {0,1} × {0,1} = 4 states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_extends_does_contribute_variables() {
    let extended = common::parse_module_strict_with_id(
        r#"
---- MODULE Extended ----
EXTENDS Integers

VARIABLE b

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Extended

VARIABLE a

Init == a = 0 /\ b = 0

Next ==
    \/ (a' = a + 1 /\ b' = b)
    \/ (a' = a /\ b' = b + 1)

Constraint == a < 2 /\ b < 2

====
"#,
        FileId(0),
    );

    assert_state_count(
        &outer,
        &[&extended],
        &bounded_config(),
        4,
        "EXTENDS should contribute variables (both a and b in state space)",
    );
}

/// Parallel parity test for #2787: standalone INSTANCE with implicit binding.
///
/// Verifies that the parallel checker produces the same state count as the
/// sequential checker when an EXTENDS'd module declares both `VARIABLE x` and
/// operator `x == ...` (implicit constant binding). The parallel path's
/// two-pass collect_vars_and_ops (fix in e8672a5) must skip variables that
/// are shadowed by operators, matching the sequential path's behavior.
///
/// Without the #2787 fix, the parallel path would include `x` and `y` as
/// state variables, inflating the state vector and producing a different
/// state count than the sequential path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_parallel_parity_standalone_instance_implicit_binding() {
    let _serial = acquire_parallel_check_lock();

    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
EXTENDS Integers

VARIABLES x, y

InnerOp == x + y

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers

VARIABLE data

\* Operators matching Inner's variables for substitution
x == data[1]
y == data[2]

\* Standalone INSTANCE: imports operators unqualified, but NOT variables
INSTANCE Inner

Init == data = <<0, 0>>

Next ==
    \/ data' = <<data[1] + 1, data[2]>>
    \/ data' = <<data[1], data[2] + 1>>

Constraint == data[1] < 2 /\ data[2] < 2

====
"#,
        FileId(0),
    );

    let config = bounded_config();

    // Sequential baseline
    let mut seq_checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    let seq_result = seq_checker.check();
    let seq_states = match &seq_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("sequential: expected Success, got: {other:?}"),
    };

    // Parallel must match
    let mut par_checker = ParallelChecker::new_with_extends(&outer, &[&inner], &config, 2);
    par_checker.set_deadlock_check(false);
    let par_result = par_checker.check();
    let par_states = match &par_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("parallel: expected Success, got: {other:?}"),
    };

    assert_eq!(
        seq_states, par_states,
        "parallel/sequential state count mismatch for standalone INSTANCE + implicit binding: \
         seq={seq_states}, par={par_states}"
    );
    assert_eq!(
        seq_states, 4,
        "expected 4 states (data[1],data[2] in {{0,1}}x{{0,1}}), got {seq_states}"
    );
}

/// Parallel parity test: EXTENDS contributes variables in parallel path.
///
/// Verifies that the parallel checker correctly includes EXTENDS'd module
/// variables in the state space, matching sequential behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bug_295_parallel_parity_extends_contributes_variables() {
    let _serial = acquire_parallel_check_lock();

    let extended = common::parse_module_strict_with_id(
        r#"
---- MODULE Extended ----
EXTENDS Integers

VARIABLE b

====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Extended

VARIABLE a

Init == a = 0 /\ b = 0

Next ==
    \/ (a' = a + 1 /\ b' = b)
    \/ (a' = a /\ b' = b + 1)

Constraint == a < 2 /\ b < 2

====
"#,
        FileId(0),
    );

    let config = bounded_config();

    // Sequential baseline
    let mut seq_checker = ModelChecker::new_with_extends(&outer, &[&extended], &config);
    let seq_result = seq_checker.check();
    let seq_states = match &seq_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("sequential: expected Success, got: {other:?}"),
    };

    // Parallel must match
    let mut par_checker = ParallelChecker::new_with_extends(&outer, &[&extended], &config, 2);
    par_checker.set_deadlock_check(false);
    let par_result = par_checker.check();
    let par_states = match &par_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("parallel: expected Success, got: {other:?}"),
    };

    assert_eq!(
        seq_states, par_states,
        "parallel/sequential state count mismatch for EXTENDS variable contribution: \
         seq={seq_states}, par={par_states}"
    );
    assert_eq!(
        seq_states, 4,
        "expected 4 states ((a,b) in {{0,1}}x{{0,1}}), got {seq_states}"
    );
}
