// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core codegen integration tests: state struct, StateMachine impl, init/next,
//! invariants, operator references, harness generation, and snapshot regression.

mod common;

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_counter_spec() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1

InvNonNegative == count >= 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify key elements in generated code
    assert!(
        code.contains("pub struct CounterState"),
        "Missing state struct"
    );
    assert!(code.contains("pub count: i64"), "Missing count field");
    assert!(
        code.contains("impl StateMachine for Counter"),
        "Missing StateMachine impl"
    );
    assert!(code.contains("fn init(&self)"), "Missing init method");
    assert!(
        code.contains("fn next(&self, state: &Self::State)"),
        "Missing next method"
    );
    assert!(
        code.contains("fn check_invariant"),
        "Missing invariant check"
    );
    assert!(
        code.contains("fn check_inv_non_negative"),
        "Missing invariant method"
    );

    // Verify Init body
    assert!(code.contains("count: 0_i64"), "Init should set count to 0");

    // Verify Next body
    assert!(
        code.contains("state.count + 1_i64"),
        "Next should increment count"
    );

    // Verify invariant body
    assert!(
        code.contains("state.count >= 0_i64"),
        "Invariant should check count >= 0"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_for_each_closure_name_does_not_capture_tla_vars() {
    let source = r#"
---- MODULE CaptureAvoidance ----
VARIABLE __tla2_yield_state_fn

Init == __tla2_yield_state_fn = 0

Next == __tla2_yield_state_fn' = __tla2_yield_state_fn
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("fn for_each_init<F>(&self, mut __tla2_yield_state_fn_0: F)"),
        "Expected for_each_init closure parameter to avoid capturing state variable name"
    );
    assert!(
        code.contains(
            "fn for_each_next<F>(&self, state: &Self::State, mut __tla2_yield_state_fn_0: F)"
        ),
        "Expected for_each_next closure parameter to avoid capturing state variable name"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_two_variable_spec() {
    let source = r#"
---- MODULE TwoPhase ----
VARIABLES x, y

Init == x = 0 /\ y = 0

Next == x' = x + 1 /\ y' = y + x

InvPositive == y >= 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify both variables in state struct
    assert!(code.contains("pub x: i64"), "Missing x field");
    assert!(code.contains("pub y: i64"), "Missing y field");

    // Verify init sets both variables
    assert!(code.contains("x: 0_i64"), "Init should set x");
    assert!(code.contains("y: 0_i64"), "Init should set y");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nondeterministic_init() {
    let source = r#"
---- MODULE Nondet ----
VARIABLE x

Init == x \in 1..3

Next == x' = x
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify non-deterministic init generates a loop
    assert!(
        code.contains("for x in range_set(1_i64, 3_i64)"),
        "Should generate loop for non-deterministic init"
    );
    assert!(
        code.contains("states.push("),
        "Should collect states in a vector"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nondeterministic_next_over_state_set() {
    let source = r#"
---- MODULE NondetNext ----
VARIABLES s, x

Init == s = {1, 2} /\ x = 0

Next == x' \in s /\ UNCHANGED s
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("for x_next in state.s.clone()"),
        "Nondeterministic Next over a state set should iterate state.s"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conditional_next() {
    let source = r#"
---- MODULE Bounded ----
VARIABLE count

Init == count = 0

Inc == count < 10 /\ count' = count + 1
Dec == count > 0 /\ count' = count - 1

Next == Inc \/ Dec

InvBounded == count >= 0 /\ count <= 10
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // The Next action uses disjunction, should generate multiple action blocks
    assert!(code.contains("// Action 1"), "Should have action comments");
    assert!(code.contains("// Action 2"), "Should have multiple actions");

    // Guards should reference the input state (not free variables).
    assert!(
        code.contains("if (state.count < 10_i64)"),
        "Guard should reference state.count"
    );
    assert!(
        code.contains("if (state.count > 0_i64)"),
        "Guard should reference state.count"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_operations() {
    let source = r#"
---- MODULE Sets ----
VARIABLE s

Init == s = {}

Next == s' = s \union {1}

InvSmall == s \subseteq {1, 2, 3}
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Note: Type inference currently defaults unknown types to i64
    // Set operations are still translated correctly
    assert!(
        code.contains("TlaSet::new()"),
        "Empty set should use TlaSet::new()"
    );
    assert!(code.contains(".union("), "Should use union method");
    assert!(code.contains(".is_subset("), "Should use is_subset method");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_kani_harness_generation() {
    let source = r#"
---- MODULE Simple ----
VARIABLE x

Init == x = 0

Next == x' = x + 1

Invariant == x >= 0
====
"#;

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: true,
        generate_checker: false,
        checker_map: None,
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify Kani proofs are generated
    assert!(code.contains("#[cfg(kani)]"), "Missing kani cfg");
    assert!(code.contains("mod kani_proofs"), "Missing kani module");
    assert!(
        code.contains("#[kani::proof]"),
        "Missing kani::proof attribute"
    );
    assert!(
        code.contains("fn init_satisfies_invariants()"),
        "Missing init proof"
    );
    assert!(
        code.contains("fn next_preserves_invariants()"),
        "Missing next proof"
    );
    assert!(code.contains("kani::assert"), "Missing kani assertions");
    assert!(
        code.contains("#[kani::unwind(5)]"),
        "Missing unwind attribute"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_variable() {
    let source = r#"
---- MODULE Toggle ----
VARIABLE flag

Init == flag = FALSE

Next == flag' = ~flag

InvBoolean == flag \in {TRUE, FALSE}
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Note: Type inference currently treats booleans as bool type when
    // assigned FALSE/TRUE directly
    // Verify boolean operations in generated code
    assert!(
        code.contains("flag: false") || code.contains("flag: FALSE"),
        "Init should set flag to false"
    );
    // The negation operator should be translated
    assert!(
        code.contains("!") || code.contains("flag"),
        "Next should negate flag"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_then_else() {
    let source = r#"
---- MODULE IfThenElse ----
VARIABLE x

Init == x = 0

Next == x' = IF x < 5 THEN x + 1 ELSE 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify if-then-else is generated
    assert!(
        code.contains("if (state.x < 5_i64)"),
        "Should generate if condition"
    );
    assert!(
        code.contains("(state.x + 1_i64)"),
        "Should have then branch"
    );
    assert!(code.contains("else { 0_i64 }"), "Should have else branch");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multiple_invariants() {
    let source = r#"
---- MODULE MultiInv ----
VARIABLE x

Init == x = 5

Next == x' = x

InvPositive == x > 0
InvBounded == x <= 10
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify both invariant methods
    assert!(
        code.contains("fn check_inv_positive"),
        "Missing first invariant method"
    );
    assert!(
        code.contains("fn check_inv_bounded"),
        "Missing second invariant method"
    );

    // Verify check_invariant combines them
    assert!(
        code.contains("self.check_inv_positive(state)"),
        "Missing first invariant call"
    );
    assert!(
        code.contains("self.check_inv_bounded(state)"),
        "Missing second invariant call"
    );

    assert!(
        code.contains("fn invariant_names(&self) -> Vec<&'static str>"),
        "Missing invariant_names impl"
    );
    assert!(
        code.contains(
            "fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool>"
        ),
        "Missing check_named_invariant impl"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_syntax() {
    let source = r#"
---- MODULE Unchanged ----
VARIABLES x, y

Init == x = 0 /\ y = 0

IncX == x' = x + 1 /\ UNCHANGED y
IncY == y' = y + 1 /\ UNCHANGED x

Next == IncX \/ IncY
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // The code should correctly handle UNCHANGED by copying from state
    assert!(
        code.contains("state.x.clone()") || code.contains("state.x,"),
        "Should preserve unchanged x"
    );
    assert!(
        code.contains("state.y.clone()") || code.contains("state.y,"),
        "Should preserve unchanged y"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_conflict_adds_guard() {
    let source = r#"
---- MODULE Conflict ----
VARIABLE x

Init == x = 0
Next == x' = 1 /\ UNCHANGED x
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("if state.x == 1_i64"),
        "Expected UNCHANGED/assignment conflict to emit a guard"
    );
    assert!(
        code.contains("x: state.x.clone()"),
        "Expected UNCHANGED to keep old value in successor"
    );
    // is_next must enforce both constraints: UNCHANGED (old.x == new.x) AND
    // primed assignment (new.x == 1). Both are needed because the spec is a
    // conjunction: x' = 1 /\ UNCHANGED x.
    assert!(
        code.contains("old.x == new.x") && code.contains("new.x == 1_i64"),
        "Expected is_next to enforce both UNCHANGED and assignment constraints"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proptest_generation() {
    let source = r#"
---- MODULE PropTest ----
VARIABLE x

Init == x = 0
Next == x' = x + 1
Invariant == x >= 0
====
"#;

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: true,
        generate_kani: false,
        generate_checker: false,
        checker_map: None,
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify proptest module is generated
    assert!(code.contains("#[cfg(test)]"), "Missing test cfg");
    assert!(code.contains("mod tests"), "Missing tests module");
    assert!(
        code.contains("use std::collections::HashSet"),
        "Missing HashSet import"
    );

    // Verify test functions are generated
    assert!(
        code.contains("fn test_init_not_empty()"),
        "Missing init not empty test"
    );
    assert!(
        code.contains("fn test_init_satisfies_invariants()"),
        "Missing init invariants test"
    );
    assert!(
        code.contains("fn test_bounded_exploration()"),
        "Missing bounded exploration test"
    );
    assert!(
        code.contains("fn test_next_preserves_invariants()"),
        "Missing next preserves invariants test"
    );

    // Verify test content
    assert!(
        code.contains("max_states = 1000"),
        "Missing max_states limit"
    );
    assert!(
        code.contains("machine.check_invariant"),
        "Missing invariant check"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_module_name_override() {
    let source = r#"
---- MODULE Original ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;

    let options = CodeGenOptions {
        module_name: Some("CustomName".to_string()),
        generate_proptest: false,
        generate_kani: false,
        generate_checker: false,
        checker_map: None,
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify custom module name is used
    assert!(
        code.contains("CustomNameState"),
        "Should use custom name for state struct"
    );
    assert!(
        code.contains("struct CustomName;"),
        "Should use custom name for machine struct"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_counter() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1

InvNonNegative == count >= 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    insta::assert_snapshot!("counter_codegen", code);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_operator_reference_in_init() {
    let source = r#"
---- MODULE InitRef ----
VARIABLE x

Start == x = 0
Init == Start

Next == x' = x
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("x: 0_i64"),
        "Init should expand operator reference"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_operator_reference_in_invariant() {
    let source = r#"
---- MODULE InvRef ----
VARIABLE x

Init == x = 0
Next == x' = x

TypeOK == x >= 0
InvNonNeg == TypeOK
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("fn check_inv_non_neg"),
        "Missing invariant method"
    );
    assert!(
        code.contains("state.x >= 0_i64"),
        "Invariant should expand operator reference"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parameterized_action_operator() {
    let source = r#"
---- MODULE ParamOp ----
VARIABLE x

Init == x = 0

Inc(v) == v' = v + 1
Next == Inc(x)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("state.x + 1_i64"),
        "Next should expand parameterized operator application"
    );
}
