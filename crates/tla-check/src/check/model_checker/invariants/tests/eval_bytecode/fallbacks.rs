// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode/tree-walk fallback tests: hybrid execution, tree-walk fallback
//! violation detection, and runtime pruning diagnostics (#3626).

use super::*;

/// Hybrid bytecode/tree-walking: when only some invariants compile to bytecode,
/// the compiled ones evaluate via the VM and the rest fall back to tree-walking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_partial_coverage_hybrid() {
    let mut module = parse_module(
        r#"
---- MODULE BytecodePartialHybrid ----
VARIABLE x
Init == x = 5
Next == x' = x
\* Simple invariant: compilable to bytecode.
SimpleSafety == x > 0
\* Complex invariant using LAMBDA: NOT compilable to bytecode.
ComplexSafety == (\A y \in {x} : y > 0)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SimpleSafety".to_string(), "ComplexSafety".to_string()],
        ..Default::default()
    };
    let registry = {
        let checker = ModelChecker::new(&module, &config);
        checker.ctx.var_registry().clone()
    };

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }

    // Compile bytecode for only "SimpleSafety" by providing it alone.
    // "ComplexSafety" won't be in the bytecode op_indices.
    let bytecode = tla_eval::bytecode_vm::compile_operators_to_bytecode(
        &module,
        &[],
        &["SimpleSafety".to_string()],
    );
    assert!(
        bytecode.op_indices.contains_key("SimpleSafety"),
        "SimpleSafety should compile to bytecode"
    );
    assert!(
        !bytecode.op_indices.contains_key("ComplexSafety"),
        "ComplexSafety should NOT be in bytecode (not requested)"
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.bytecode = Some(bytecode);

    // Passing state: both invariants should pass (hybrid path).
    let pass = ArrayState::from_state(&State::from_pairs([("x", Value::int(5))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("hybrid invariant check should pass"),
        None
    );

    // Failing state: x = 0 violates SimpleSafety (bytecode) before
    // ComplexSafety (tree-walk) is reached.
    let fail = ArrayState::from_state(&State::from_pairs([("x", Value::int(0))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&fail)
            .expect("hybrid invariant check should detect violation"),
        Some("SimpleSafety".to_string())
    );
}

/// Hybrid path: tree-walk fallback detects a violation that bytecode cannot check.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_treewalk_fallback_detects_violation() {
    let mut module = parse_module(
        r#"
---- MODULE BytecodeFallbackViolation ----
VARIABLE x
Init == x = 5
Next == x' = x
\* Simple invariant: compilable to bytecode — always TRUE for x > 0.
SimpleSafety == x > 0
\* Complex invariant NOT compiled: fails when x < 10.
ComplexSafety == (\A y \in {x} : y >= 10)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SimpleSafety".to_string(), "ComplexSafety".to_string()],
        ..Default::default()
    };
    let registry = {
        let checker = ModelChecker::new(&module, &config);
        checker.ctx.var_registry().clone()
    };

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }

    let bytecode = tla_eval::bytecode_vm::compile_operators_to_bytecode(
        &module,
        &[],
        &["SimpleSafety".to_string()],
    );
    assert!(bytecode.op_indices.contains_key("SimpleSafety"));

    let mut checker = ModelChecker::new(&module, &config);
    checker.bytecode = Some(bytecode);

    // x = 5: SimpleSafety passes (bytecode), ComplexSafety fails (tree-walk: 5 < 10).
    let fail_complex =
        ArrayState::from_state(&State::from_pairs([("x", Value::int(5))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&fail_complex)
            .expect("tree-walk fallback should detect ComplexSafety violation"),
        Some("ComplexSafety".to_string())
    );

    // x = 10: both pass.
    let pass = ArrayState::from_state(&State::from_pairs([("x", Value::int(10))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("both invariants should pass"),
        None
    );
}
