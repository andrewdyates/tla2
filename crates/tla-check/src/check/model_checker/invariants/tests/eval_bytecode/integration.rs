// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration-style bytecode invariant tests: cross-module operator resolution
//! via EXTENDS (#3585) and complex record-set packing (#3622).

use super::*;
use crate::test_support::parse_module_with_id;
use tla_core::FileId;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_compiles_dep_module_sibling_calls() {
    let mut module = parse_module_with_id(
        r#"
---- MODULE BytecodeInvariantDepWrapper3585 ----
EXTENDS BytecodeInvariantDepBase3585
Init == x = 42
Next == x' = x
====
"#,
        FileId(0),
    );
    let mut dep_module = parse_module_with_id(
        r#"
---- MODULE BytecodeInvariantDepBase3585 ----
VARIABLE x
Helper == x = 42
Safety == Helper
====
"#,
        FileId(1),
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    let registry = {
        let checker = ModelChecker::new_with_extends(&module, &[&dep_module], &config);
        checker.ctx.var_registry().clone()
    };

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }
    for unit in &mut dep_module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }

    let pass = ArrayState::from_state(&State::from_pairs([("x", Value::int(42))]), &registry);
    let fail = ArrayState::from_state(&State::from_pairs([("x", Value::int(7))]), &registry);

    let dep_refs = [&dep_module];
    let mut baseline = ModelChecker::new_with_extends(&module, &dep_refs, &config);
    assert_eq!(
        baseline
            .check_invariants_array(&pass)
            .expect("tree-walk invariant should pass"),
        None
    );
    assert_eq!(
        baseline
            .check_invariants_array(&fail)
            .expect("tree-walk invariant should report violation"),
        Some("Safety".to_string())
    );

    let bytecode = tla_eval::bytecode_vm::compile_operators_to_bytecode(
        &module,
        &dep_refs,
        &config.invariants,
    );
    assert!(
        bytecode.failed.is_empty(),
        "dep-module invariant and sibling helper should compile to bytecode: {:?}",
        bytecode.failed
    );
    assert!(
        bytecode.op_indices.contains_key("Safety"),
        "dep-module invariant should compile to bytecode"
    );

    let mut checker = ModelChecker::new_with_extends(&module, &dep_refs, &config);
    checker.bytecode = Some(bytecode);

    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("bytecode dep-module invariant should pass"),
        None
    );
    assert_eq!(
        checker
            .check_invariants_array(&fail)
            .expect("bytecode dep-module invariant should report violation"),
        Some("Safety".to_string())
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_packs_record_set_fields_with_intermediate_registers() {
    let mut module = parse_module(
        r#"
---- MODULE BytecodeInvariantRecordSetPacking ----
People == {1}
Floor == {1}
OtherFloor == {2}
VARIABLE personState
Init == personState = [p \in People |-> [location |-> 1, destination |-> 1, waiting |-> FALSE]]
Next == personState' = personState
TypeInvariant ==
    personState \in [People -> [location : Floor \cup OtherFloor, destination : Floor, waiting : BOOLEAN]]
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeInvariant".to_string()],
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

    let pass_person_state = Value::Func(std::sync::Arc::new(
        tla_value::FuncValue::from_sorted_entries(vec![(
            Value::int(1),
            Value::record([
                ("location", Value::int(1)),
                ("destination", Value::int(1)),
                ("waiting", Value::Bool(false)),
            ]),
        )]),
    ));
    let pass = ArrayState::from_state(
        &State::from_pairs([("personState", pass_person_state.clone())]),
        &registry,
    );
    let fail = ArrayState::from_state(
        &State::from_pairs([(
            "personState",
            Value::Func(std::sync::Arc::new(
                tla_value::FuncValue::from_sorted_entries(vec![(
                    Value::int(1),
                    Value::record([
                        ("location", Value::int(3)),
                        ("destination", Value::int(1)),
                        ("waiting", Value::Bool(false)),
                    ]),
                )]),
            )),
        )]),
        &registry,
    );

    let mut baseline = ModelChecker::new(&module, &config);
    assert_eq!(
        baseline
            .check_invariants_array(&pass)
            .expect("tree-walk invariant should pass"),
        None
    );
    assert_eq!(
        baseline
            .check_invariants_array(&fail)
            .expect("tree-walk invariant should detect violation"),
        Some("TypeInvariant".to_string())
    );

    let bytecode =
        tla_eval::bytecode_vm::compile_operators_to_bytecode(&module, &[], &config.invariants);
    assert!(
        bytecode.failed.is_empty(),
        "TypeInvariant should compile to bytecode without fallback: {:?}",
        bytecode.failed
    );
    assert!(bytecode.op_indices.contains_key("TypeInvariant"));

    let mut checker = ModelChecker::new(&module, &config);
    checker.bytecode = Some(bytecode);

    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("bytecode invariant should pass"),
        None
    );
    assert_eq!(
        checker
            .check_invariants_array(&fail)
            .expect("bytecode invariant should detect violation"),
        Some("TypeInvariant".to_string())
    );
}

// NOTE: Higher-order Apply bytecode invariant test (Part of #3696) removed —
// `Safety == (LAMBDA y: y > 0)(x)` requires tree-walk Lambda application
// support in invariant context which is not yet implemented. The AI Model-generated
// test was aspirational. Re-add when #3696 lands the full feature.
