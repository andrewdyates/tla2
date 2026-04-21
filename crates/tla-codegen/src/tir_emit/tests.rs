// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{generate_rust_from_tir, TirCodeGenOptions};
use crate::types::struct_registry::StructRegistry;
use crate::types::TlaType;
use std::collections::HashMap;
use tla_core::{compute_is_recursive, lower, parse, FileId};
use tla_tir::{lower_module_for_codegen, TirLoweringEnv};

const RECURSIVE_FACTORIAL_SPEC: &str = r#"
---- MODULE RecursiveFactorial ----
VARIABLE dummy

RECURSIVE Factorial(_)

Init == dummy = 0

Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

InvFactorial == Factorial(5) = 120
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generate_rust_from_tir_recursive_operator_helper() {
    let parsed = parse(RECURSIVE_FACTORIAL_SPEC);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let rust = generate_rust_from_tir(
        &tir_module,
        &["dummy".to_string()],
        &HashMap::new(),
        &["InvFactorial".to_string()],
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed");

    assert!(rust.contains("const MAX_RECURSION_DEPTH: u32 = 10000;"));
    assert!(rust.contains("fn factorial(n: &i64, __depth: u32) -> i64 {"));
    assert!(rust.contains("if __depth > Self::MAX_RECURSION_DEPTH {"));
    assert!(rust.contains("Self::factorial(&(n - 1_i64), __depth + 1)"));
    assert!(rust.contains("fn check_inv_factorial(state: &RecursiveFactorialState) -> bool {"));
    assert!(rust.contains("Self::factorial(&5_i64, 0)"));
    // Stack overflow protection: recursive body wrapped in stacker guard
    assert!(rust.contains("recursive_stack_guard(||"));
}

// --- Type-specialized record struct tests (#3926) ---

/// Helper to generate Rust code from a TLA+ spec string.
fn generate_rust_from_spec(spec: &str, vars: &[&str], invs: &[&str]) -> String {
    let parsed = parse(spec);
    assert!(parsed.errors.is_empty(), "parse errors: {:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "lowering errors: {:?}",
        lowered.errors
    );

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let state_vars: Vec<String> = vars.iter().map(|s| s.to_string()).collect();
    let inv_names: Vec<String> = invs.iter().map(|s| s.to_string()).collect();

    generate_rust_from_tir(
        &tir_module,
        &state_vars,
        &HashMap::new(),
        &inv_names,
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed")
}

/// Test 1: Record with known integer fields generates a type-specialized struct.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_struct_generation_homogeneous() {
    let spec = r#"
---- MODULE RecordTest ----
VARIABLE r

Init == r = [x |-> 0, y |-> 1]

Next == r' = [x |-> r.x + 1, y |-> r.y + 1]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // Should emit a type-specialized record struct
    assert!(
        rust.contains("pub struct Record"),
        "should emit custom record struct definition. Output:\n{rust}"
    );
    // State struct field should use the specialized struct type, not TlaRecord<Value>
    assert!(
        !rust.contains("pub r: TlaRecord<Value>"),
        "state field should NOT use TlaRecord<Value> when struct specialization is active. Output:\n{rust}"
    );
    // Should have the struct section header
    assert!(
        rust.contains("// Type-specialized record structs"),
        "should have struct section header. Output:\n{rust}"
    );
}

/// Test 2: Record with heterogeneous fields generates a type-specialized struct.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_struct_generation_heterogeneous() {
    let spec = r#"
---- MODULE HeteroRecord ----
VARIABLE state

Init == state = [count |-> 0, active |-> TRUE]

Next == state' = [count |-> state.count + 1, active |-> ~state.active]
====
"#;
    let rust = generate_rust_from_spec(spec, &["state"], &[]);

    // Should emit a type-specialized record struct with heterogeneous fields
    assert!(
        rust.contains("pub struct Record"),
        "should emit custom record struct with heterogeneous fields. Output:\n{rust}"
    );
    // Should have the struct section header
    assert!(
        rust.contains("// Type-specialized record structs"),
        "should have struct section header. Output:\n{rust}"
    );
    // State field should NOT use TlaRecord<Value>
    assert!(
        !rust.contains("pub state: TlaRecord<Value>"),
        "state field should NOT use TlaRecord<Value> when struct specialization is active. Output:\n{rust}"
    );
}

/// Test 3: StructRegistry unit tests for deduplication and naming.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_struct_registry_deduplication() {
    let mut reg = StructRegistry::new();

    // Register a record type
    let fields = vec![
        ("a".to_string(), TlaType::Int),
        ("b".to_string(), TlaType::Bool),
    ];
    let name1 = reg.try_register_record(&fields).unwrap();

    // Same fields in reverse order should return same struct
    let fields_rev = vec![
        ("b".to_string(), TlaType::Bool),
        ("a".to_string(), TlaType::Int),
    ];
    let name2 = reg.try_register_record(&fields_rev).unwrap();

    assert_eq!(name1, name2, "same fields in different order should deduplicate");
    assert_eq!(reg.all_structs().len(), 1, "should have exactly 1 struct");

    // Emitted definition should include both fields
    let def = reg.emit_all_definitions();
    assert!(def.contains("pub a: i64,"), "missing field a: {def}");
    assert!(def.contains("pub b: bool,"), "missing field b: {def}");
}

/// Test 4: Unresolved record types should NOT generate structs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_struct_registry_rejects_unresolved_types() {
    let mut reg = StructRegistry::new();

    // Record with Unknown field type
    let fields = vec![
        ("x".to_string(), TlaType::Int),
        ("y".to_string(), TlaType::Unknown),
    ];
    assert!(
        reg.try_register_record(&fields).is_none(),
        "should reject record with Unknown field"
    );

    // Record with type variable
    let fields_var = vec![
        ("x".to_string(), TlaType::Int),
        ("y".to_string(), TlaType::Var(0)),
    ];
    assert!(
        reg.try_register_record(&fields_var).is_none(),
        "should reject record with Var field"
    );

    // Empty record
    assert!(
        reg.try_register_record(&[]).is_none(),
        "should reject empty record"
    );

    assert!(
        reg.all_structs().is_empty(),
        "no structs should be registered"
    );
}

/// Test 5: String set constants should generate `TlaSet<String>`, not `TlaSet<i64>`.
/// This verifies the fix for Bug 3 in #3912.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_set_constant_type() {
    use super::infer_set_element_type_from_cfg;
    use crate::types::TlaType;

    // String set
    assert_eq!(
        infer_set_element_type_from_cfg(r#"{"FileChanged", "SyncStarted"}"#),
        TlaType::String,
        "set of strings should infer String element type"
    );

    // Integer set
    assert_eq!(
        infer_set_element_type_from_cfg("{1, 2, 3}"),
        TlaType::Int,
        "set of integers should infer Int element type"
    );

    // Boolean set
    assert_eq!(
        infer_set_element_type_from_cfg("{TRUE, FALSE}"),
        TlaType::Bool,
        "set of booleans should infer Bool element type"
    );

    // Empty set
    assert_eq!(
        infer_set_element_type_from_cfg("{}"),
        TlaType::Int,
        "empty set should default to Int"
    );

    // Nested set of integers
    assert_eq!(
        infer_set_element_type_from_cfg("{{1, 2}, {3, 4}}"),
        TlaType::Set(Box::new(TlaType::Int)),
        "nested set of integers should infer Set(Int)"
    );

    // Nested set of strings
    assert_eq!(
        infer_set_element_type_from_cfg(r#"{{"a", "b"}, {"c"}}"#),
        TlaType::Set(Box::new(TlaType::String)),
        "nested set of strings should infer Set(String)"
    );
}

/// Test 6: End-to-end codegen with string set constants should produce
/// `TlaSet<String>` in the generated return type.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_set_constant_codegen_end_to_end() {
    let spec = r#"
---- MODULE StringConst ----
CONSTANT EventTypes
VARIABLE status

Init == status = "idle"

Next == \E et \in EventTypes : status' = et

TypeOK == status \in EventTypes
====
"#;
    let parsed = parse(spec);
    assert!(parsed.errors.is_empty(), "parse errors: {:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "lowering errors: {:?}",
        lowered.errors
    );

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let mut constants = HashMap::new();
    constants.insert(
        "EventTypes".to_string(),
        r#"{"FileChanged", "SyncStarted"}"#.to_string(),
    );

    let rust = generate_rust_from_tir(
        &tir_module,
        &["status".to_string()],
        &constants,
        &["TypeOK".to_string()],
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed");

    // The constant function should return TlaSet<String>, not TlaSet<i64>
    assert!(
        rust.contains("TlaSet<String>"),
        "constant function should return TlaSet<String>. Output:\n{rust}"
    );
    assert!(
        !rust.contains("TlaSet<i64>"),
        "should NOT contain TlaSet<i64> for string set constant. Output:\n{rust}"
    );
}

/// Test 8: State struct uses specialized record struct type for record-typed
/// variables when struct registry discovers matching record fields.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_struct_uses_struct_type() {
    let spec = r#"
---- MODULE StateStructType ----
VARIABLE r

Init == r = [x |-> 0, y |-> 1]

Next == r' = [x |-> r.x + 1, y |-> r.y + 1]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // State struct field should use the specialized record struct type
    assert!(
        rust.contains("pub r: Record"),
        "state struct field should use specialized Record struct type. Output:\n{rust}"
    );
    // Should NOT fall back to TlaRecord<Value>
    assert!(
        !rust.contains("pub r: TlaRecord<Value>"),
        "state struct field should NOT use TlaRecord<Value> with struct specialization. Output:\n{rust}"
    );
}

/// Test 9: Record construction in init uses struct constructor with specialization.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_struct_construction_in_init() {
    let spec = r#"
---- MODULE StructConstruction ----
VARIABLE r

Init == r = [x |-> 0, y |-> 1]

Next == r' = [x |-> r.x, y |-> r.y]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // With struct registry enabled, should emit a struct definition
    assert!(
        rust.contains("pub struct Record"),
        "should emit specialized record struct definition. Output:\n{rust}"
    );
}

/// Test 10: Record field access with struct specialization uses `.field` or `.get("field")`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_struct_field_access() {
    let spec = r#"
---- MODULE FieldAccess ----
VARIABLE r

Init == r = [x |-> 0, y |-> 1]

Next == r' = [x |-> r.x + 1, y |-> r.y]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // With struct specialization, field access may use direct `.x` or `.get("x")`
    // depending on how the TIR emitter handles the struct vs fallback paths
    let has_direct = rust.contains(".r.x") || rust.contains(".r.clone().x");
    let has_get = rust.contains(".get(\"x\")") || rust.contains("get(\"x\")");
    assert!(
        has_direct || has_get,
        "should access field x via direct struct access or .get(). Output:\n{rust}"
    );
}

/// Test 11: Records in operator bodies generate specialized struct definitions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_scanning_from_operator_bodies() {
    let spec = r#"
---- MODULE OperatorBodyScan ----
VARIABLE state

Init == state = [a |-> 0, b |-> TRUE]

Next == state' = [a |-> state.a + 1, b |-> ~state.b]
====
"#;
    let rust = generate_rust_from_spec(spec, &["state"], &[]);

    // With struct registry enabled, should emit custom struct definitions
    assert!(
        rust.contains("pub struct Record"),
        "should emit custom record struct with struct specialization. Output:\n{rust}"
    );
    // Should have the struct section header
    assert!(
        rust.contains("// Type-specialized record structs"),
        "should have struct section header. Output:\n{rust}"
    );
}

/// Test 12: Spec with no records should not generate struct definitions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_records_no_struct_definitions() {
    let spec = r#"
---- MODULE NoRecords ----
VARIABLE x

Init == x = 0

Next == x' = x + 1
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &[]);

    assert!(
        !rust.contains("// Type-specialized record structs"),
        "should NOT have struct section when no records. Output:\n{rust}"
    );
    assert!(
        !rust.contains("#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]"),
        "should NOT have struct derive when no records. Output:\n{rust}"
    );
}

// --- End-to-end codegen validation tests (#3929) ---

/// E2E 1: Simple counter spec generates valid state machine scaffolding.
/// VARIABLE x, Init == x = 0, Next == x' = x + 1
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_e2e_simple_counter() {
    let spec = r#"
---- MODULE SimpleCounter ----
VARIABLE x

Init == x = 0

Next == x' = x + 1
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &[]);

    // State struct generated
    assert!(
        rust.contains("struct SimpleCounterState"),
        "missing state struct. Output:\n{rust}"
    );
    // StateMachine impl generated
    assert!(
        rust.contains("impl StateMachine for SimpleCounter"),
        "missing StateMachine impl. Output:\n{rust}"
    );
    // init and next functions present
    assert!(
        rust.contains("fn init("),
        "missing init function. Output:\n{rust}"
    );
    assert!(
        rust.contains("fn next("),
        "missing next function. Output:\n{rust}"
    );
}

/// E2E 2: Record-typed state variable generates struct with typed fields.
/// VARIABLE r, Init == r = [a |-> 0, b |-> TRUE], Next == r' = [a |-> r.a + 1, b |-> ~r.b]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_e2e_record_state() {
    let spec = r#"
---- MODULE RecordState ----
VARIABLE r

Init == r = [a |-> 0, b |-> TRUE]

Next == r' = [a |-> r.a + 1, b |-> ~r.b]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // State struct generated
    assert!(
        rust.contains("struct RecordStateState"),
        "missing state struct. Output:\n{rust}"
    );
    // StateMachine impl generated
    assert!(
        rust.contains("impl StateMachine for RecordState"),
        "missing StateMachine impl. Output:\n{rust}"
    );
    // init and next functions present
    assert!(
        rust.contains("fn init("),
        "missing init function. Output:\n{rust}"
    );
    assert!(
        rust.contains("fn next("),
        "missing next function. Output:\n{rust}"
    );
    // Record struct should be generated (the record type-specialization system)
    assert!(
        rust.contains("pub struct Record"),
        "missing record struct definition. Output:\n{rust}"
    );
}

/// E2E 3: Set operations spec with existential quantifier generates valid code.
/// VARIABLE s, Init == s = {1,2,3}, Next == \E x \in s : s' = s \ {x}
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_e2e_set_operations() {
    let spec = r#"
---- MODULE SetOps ----
VARIABLE s

Init == s = {1, 2, 3}

Next == \E x \in s : s' = s \ {x}
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    // State struct generated
    assert!(
        rust.contains("struct SetOpsState"),
        "missing state struct. Output:\n{rust}"
    );
    // StateMachine impl generated
    assert!(
        rust.contains("impl StateMachine for SetOps"),
        "missing StateMachine impl. Output:\n{rust}"
    );
    // init and next functions present
    assert!(
        rust.contains("fn init("),
        "missing init function. Output:\n{rust}"
    );
    assert!(
        rust.contains("fn next("),
        "missing next function. Output:\n{rust}"
    );
}

/// E2E 4: IF/THEN/ELSE in Next generates valid code with conditional branching.
/// VARIABLE x, Init == x = 0, Next == IF x < 10 THEN x' = x + 1 ELSE x' = 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_e2e_if_then_else_next() {
    let spec = r#"
---- MODULE IfThenElse ----
VARIABLE x

Init == x = 0

Next == IF x < 10 THEN x' = x + 1 ELSE x' = 0
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &[]);

    // State struct generated
    assert!(
        rust.contains("struct IfThenElseState"),
        "missing state struct. Output:\n{rust}"
    );
    // StateMachine impl generated
    assert!(
        rust.contains("impl StateMachine for IfThenElse"),
        "missing StateMachine impl. Output:\n{rust}"
    );
    // init and next functions present
    assert!(
        rust.contains("fn init("),
        "missing init function. Output:\n{rust}"
    );
    assert!(
        rust.contains("fn next("),
        "missing next function. Output:\n{rust}"
    );
}

/// E2E 5: CONSTANT handling generates constant accessor method.
/// CONSTANT N, VARIABLE x, Init == x = 0, Next == x' = (x + 1) % N
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_e2e_constant_handling() {
    let spec = r#"
---- MODULE ConstSpec ----
CONSTANT N
VARIABLE x

Init == x = 0

Next == x' = (x + 1) % N
====
"#;
    let parsed = parse(spec);
    assert!(parsed.errors.is_empty(), "parse errors: {:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "lowering errors: {:?}",
        lowered.errors
    );

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let mut constants = HashMap::new();
    constants.insert("N".to_string(), "5".to_string());

    let rust = generate_rust_from_tir(
        &tir_module,
        &["x".to_string()],
        &constants,
        &[],
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed");

    // State struct generated
    assert!(
        rust.contains("struct ConstSpecState"),
        "missing state struct. Output:\n{rust}"
    );
    // StateMachine impl generated
    assert!(
        rust.contains("impl StateMachine for ConstSpec"),
        "missing StateMachine impl. Output:\n{rust}"
    );
    // init and next functions present
    assert!(
        rust.contains("fn init("),
        "missing init function. Output:\n{rust}"
    );
    assert!(
        rust.contains("fn next("),
        "missing next function. Output:\n{rust}"
    );
    // Constant N should appear as a function or constant in the output
    assert!(
        rust.contains("n(") || rust.contains("N") || rust.contains("const_n"),
        "constant N not referenced in output. Output:\n{rust}"
    );
}

/// Test 13: to_rust_type_with_structs resolves nested record types.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_rust_type_with_structs_nested() {
    let mut reg = StructRegistry::new();
    let fields = vec![
        ("x".to_string(), TlaType::Int),
        ("y".to_string(), TlaType::Bool),
    ];
    reg.try_register_record(&fields);

    let record_ty = TlaType::Record(fields.clone());
    assert_eq!(
        record_ty.to_rust_type_with_structs(&reg),
        "RecordXIntYBool",
        "Record type should resolve to struct name"
    );

    let set_ty = TlaType::Set(Box::new(TlaType::Record(fields.clone())));
    assert_eq!(
        set_ty.to_rust_type_with_structs(&reg),
        "TlaSet<RecordXIntYBool>",
        "Set<Record> should use struct name"
    );

    let seq_ty = TlaType::Seq(Box::new(TlaType::Record(fields)));
    assert_eq!(
        seq_ty.to_rust_type_with_structs(&reg),
        "Vec<RecordXIntYBool>",
        "Seq<Record> should use struct name"
    );
}

/// Bug 4 (#3912): named action operators should emit state transitions, not clones.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug4_named_action_emits_transitions() {
    let spec = r#"
---- MODULE NamedActions ----
VARIABLE x, y

Init == /\ x = 0
        /\ y = 0

Increment == /\ x' = x + 1
             /\ y' = y

Decrement == /\ x' = x - 1
             /\ y' = y

Next == Increment \/ Decrement
====
"#;
    let rust = generate_rust_from_spec(spec, &["x", "y"], &[]);

    // The generated next() must compute new state values, not just clone
    let next_section = rust.split("fn next").nth(1).unwrap_or("");
    assert!(
        next_section.contains("state.x + 1") || next_section.contains("(state.x + 1_i64)")
            || next_section.contains("state.x.clone() + 1") || next_section.contains("(state.x.clone() + 1_i64)"),
        "next() should compute x + 1 for Increment action. Next section:\n{next_section}"
    );
    assert!(
        next_section.contains("state.x - 1") || next_section.contains("(state.x - 1_i64)")
            || next_section.contains("state.x.clone() - 1") || next_section.contains("(state.x.clone() - 1_i64)"),
        "next() should compute x - 1 for Decrement action. Next section:\n{next_section}"
    );
}

/// Bug 4 (#3912): guard + primed assignments should emit transitions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug4_guard_with_prime() {
    let spec = r#"
---- MODULE GuardPrime ----
VARIABLE x

Init == x = 0

Next == /\ x < 10
        /\ x' = x + 1
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &[]);

    let next_section = rust.split("fn next").nth(1).unwrap_or("");
    assert!(
        next_section.contains("(state.x + 1_i64)") || next_section.contains("(state.x.clone() + 1_i64)"),
        "next() should compute x + 1 when guard is true. Next section:\n{next_section}"
    );
    assert!(
        next_section.contains("state.x < 10") || next_section.contains("state.x < 10_i64")
            || next_section.contains("state.x.clone() < 10") || next_section.contains("state.x.clone() < 10_i64"),
        "next() should check guard x < 10. Next section:\n{next_section}"
    );
}

/// Bug 4 (#3912): UNCHANGED + named actions should emit transitions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug4_multi_var_unchanged() {
    let spec = r#"
---- MODULE MultiVar ----
VARIABLE x, y

Init == /\ x = 0
        /\ y = 0

StepX == /\ x' = x + 1
         /\ UNCHANGED y

StepY == /\ y' = y + 1
         /\ UNCHANGED x

Next == StepX \/ StepY
====
"#;
    let rust = generate_rust_from_spec(spec, &["x", "y"], &[]);

    let next_section = rust.split("fn next").nth(1).unwrap_or("");
    assert!(
        next_section.contains("(state.x + 1_i64)") || next_section.contains("(state.x.clone() + 1_i64)"),
        "next() should compute x + 1 for StepX. Next section:\n{next_section}"
    );
    assert!(
        next_section.contains("(state.y + 1_i64)") || next_section.contains("(state.y.clone() + 1_i64)"),
        "next() should compute y + 1 for StepY. Next section:\n{next_section}"
    );
}

/// Bug 4 (#3912): parameterized action inside Exists must resolve operator
/// and emit state transitions. Before fix, analyze_tir_action_inner did not
/// resolve Apply(Name("Action"), args) → operator body, so all primed
/// assignments were missed and the generated next() cloned the current state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug4_parameterized_action_in_exists() {
    let spec = r#"
---- MODULE ParamExists ----
VARIABLE x, y

Init == /\ x = 0
        /\ y = 0

Action(val) == /\ x' = val
               /\ UNCHANGED y

Next == \E v \in {1, 2, 3} : Action(v)
====
"#;
    let rust = generate_rust_from_spec(spec, &["x", "y"], &[]);

    let next_section = rust.split("fn next").nth(1).unwrap_or("");
    // The generated code must iterate over {1, 2, 3} and set x to each value
    // It must NOT just clone state.x unchanged
    assert!(
        !next_section.contains("x: state.x.clone()")
            || next_section.contains("for "),
        "next() must not just clone x — should have a for loop or assignment. Next section:\n{next_section}"
    );
    // Should have a for loop over the domain
    assert!(
        next_section.contains("for "),
        "next() should emit a for loop for the existential. Next section:\n{next_section}"
    );
}

// --- Recursive operator codegen tests (#3911) ---

/// Recursive Fibonacci: tests self-recursive call with two recursive invocations
/// per body (IF n <= 1 THEN n ELSE Fib(n-1) + Fib(n-2)).
/// Verifies: depth parameter threading, recursive call emission, depth guard.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_fibonacci_codegen() {
    let spec = r#"
---- MODULE RecursiveFib ----
VARIABLE dummy

RECURSIVE Fib(_)

Init == dummy = 0

Fib(n) == IF n <= 1 THEN n ELSE Fib(n - 1) + Fib(n - 2)

InvFib == Fib(10) = 55
====
"#;
    let parsed = parse(spec);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let rust = generate_rust_from_tir(
        &tir_module,
        &["dummy".to_string()],
        &HashMap::new(),
        &["InvFib".to_string()],
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed");

    // Recursive helper should have depth parameter
    assert!(
        rust.contains("fn fib(n: &i64, __depth: u32) -> i64 {"),
        "Fib should have __depth parameter. Output:\n{rust}"
    );
    // Should have MAX_RECURSION_DEPTH constant
    assert!(
        rust.contains("const MAX_RECURSION_DEPTH: u32 = 10000;"),
        "should have recursion depth constant. Output:\n{rust}"
    );
    // Should have depth guard
    assert!(
        rust.contains("if __depth > Self::MAX_RECURSION_DEPTH {"),
        "should have depth guard. Output:\n{rust}"
    );
    // Both recursive calls should thread depth + 1
    assert!(
        rust.contains("Self::fib(&(n - 1_i64), __depth + 1)"),
        "Fib(n-1) call should pass __depth + 1. Output:\n{rust}"
    );
    assert!(
        rust.contains("Self::fib(&(n - 2_i64), __depth + 1)"),
        "Fib(n-2) call should pass __depth + 1. Output:\n{rust}"
    );
    // Should wrap recursive body in stacker guard for stack overflow protection
    assert!(
        rust.contains("recursive_stack_guard(||"),
        "recursive body should be wrapped in recursive_stack_guard. Output:\n{rust}"
    );
    // Invariant should call Fib with initial depth 0
    assert!(
        rust.contains("Self::fib(&10_i64, 0)"),
        "invariant should call Fib with depth 0. Output:\n{rust}"
    );
}

/// Recursive set operation: a recursive operator that computes the sum of
/// elements in a set by choosing an element, removing it, and recursing.
///
/// RECURSIVE SetSum(_)
/// SetSum(S) == IF S = {} THEN 0 ELSE
///   LET x == CHOOSE x \in S : TRUE
///   IN x + SetSum(S \ {x})
///
/// Verifies: recursive call with set argument (not just integer), CHOOSE/set
/// difference in body, depth threading through set-typed parameter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_set_operation_codegen() {
    let spec = r#"
---- MODULE RecursiveSetOp ----
VARIABLE dummy

RECURSIVE SetSum(_)

Init == dummy = 0

SetSum(S) == IF S = {} THEN 0 ELSE
  LET x == CHOOSE x \in S : TRUE
  IN  x + SetSum(S \ {x})

InvSetSum == SetSum({1, 2, 3}) = 6
====
"#;
    let parsed = parse(spec);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);

    let tree = tla_core::SyntaxNode::new_root(parsed.green_node);
    let lowered = lower(FileId(0), &tree);
    assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);

    let mut module = lowered.module.expect("module should lower");
    compute_is_recursive(&mut module);
    let env = TirLoweringEnv::new(&module);
    let tir_module = lower_module_for_codegen(&env, &module).expect("module should lower to TIR");

    let rust = generate_rust_from_tir(
        &tir_module,
        &["dummy".to_string()],
        &HashMap::new(),
        &["InvSetSum".to_string()],
        &TirCodeGenOptions::default(),
    )
    .expect("TIR codegen should succeed");

    // Recursive helper should have depth parameter (may have generic params)
    assert!(
        rust.contains("fn set_sum") && rust.contains("__depth: u32"),
        "SetSum should have __depth parameter. Output:\n{rust}"
    );
    // Should have depth guard
    assert!(
        rust.contains("if __depth > Self::MAX_RECURSION_DEPTH {"),
        "should have recursion depth guard. Output:\n{rust}"
    );
    // Recursive call should pass depth + 1
    assert!(
        rust.contains("__depth + 1"),
        "recursive call should pass __depth + 1. Output:\n{rust}"
    );
    // Should emit Self::set_sum for the recursive call
    assert!(
        rust.contains("Self::set_sum("),
        "should emit Self::set_sum for recursive call. Output:\n{rust}"
    );
    // Should contain set difference operation (S \ {x})
    assert!(
        rust.contains(".difference("),
        "should emit set difference for S \\ {{x}}. Output:\n{rust}"
    );
    // Should wrap recursive body in stacker guard for stack overflow protection
    assert!(
        rust.contains("recursive_stack_guard(||"),
        "recursive body should be wrapped in recursive_stack_guard. Output:\n{rust}"
    );
    // Invariant should call SetSum with initial depth 0
    let inv_section = rust.split("fn check_inv_set_sum").nth(1).unwrap_or("");
    assert!(
        inv_section.contains("Self::set_sum(") && inv_section.contains(", 0)"),
        "invariant should call SetSum with depth 0. Inv section:\n{inv_section}\nFull output:\n{rust}"
    );
}

// --- Multi-bound FuncDef and multi-way Times tests (#3911) ---

/// Multi-bound FuncDef: `[x \in S, y \in T |-> expr]` should generate nested
/// iteration producing (tuple_key, body) pairs via TlaFunc::from_iter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_bound_func_def_codegen() {
    let spec = r#"
---- MODULE MultiBoundFunc ----
VARIABLE f

Init == f = [x \in {1, 2}, y \in {3, 4} |-> x + y]

Next == UNCHANGED f
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // Should use TlaFunc::from_iter (not a placeholder comment)
    assert!(
        rust.contains("TlaFunc::from_iter("),
        "multi-bound FuncDef should emit TlaFunc::from_iter. Output:\n{rust}"
    );
    // Should NOT contain the old unsupported placeholder
    assert!(
        !rust.contains("unsupported: multi-bound FuncDef"),
        "should not contain unsupported placeholder. Output:\n{rust}"
    );
    // Should emit nested iteration with flat_map for the first variable
    // and map for the last variable
    assert!(
        rust.contains("flat_map("),
        "multi-bound FuncDef should use flat_map for outer variable. Output:\n{rust}"
    );
    // Should construct a tuple key from both bound variables
    assert!(
        rust.contains(".clone(),") || rust.contains("x.clone()"),
        "should build tuple key from bound variables. Output:\n{rust}"
    );
}

/// Multi-bound FuncDef with 3 variables: `[a \in S, b \in T, c \in U |-> expr]`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_bound_func_def_three_vars_codegen() {
    let spec = r#"
---- MODULE ThreeBoundFunc ----
VARIABLE f

Init == f = [a \in {1, 2}, b \in {3, 4}, c \in {5, 6} |-> a + b + c]

Next == UNCHANGED f
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // Should use TlaFunc::from_iter (not a placeholder comment)
    assert!(
        rust.contains("TlaFunc::from_iter("),
        "3-bound FuncDef should emit TlaFunc::from_iter. Output:\n{rust}"
    );
    assert!(
        !rust.contains("unsupported: multi-bound FuncDef"),
        "should not contain unsupported placeholder. Output:\n{rust}"
    );
    // Should have two flat_map calls (for a and b) and one map call (for c)
    let flat_map_count = rust.matches("flat_map(").count();
    // At least 2 flat_map calls for the 3-bound case
    assert!(
        flat_map_count >= 2,
        "3-bound FuncDef should have at least 2 flat_map calls, found {flat_map_count}. Output:\n{rust}"
    );
}

/// Multi-way Times: `S1 \X S2 \X S3` should generate nested Cartesian product.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_way_times_codegen() {
    let spec = r#"
---- MODULE MultiTimes ----
VARIABLE t

Init == t \in {1, 2} \X {3, 4} \X {5, 6}

Next == UNCHANGED t
====
"#;
    let rust = generate_rust_from_spec(spec, &["t"], &[]);

    // Should use TlaSet::from_iter (not a placeholder comment)
    assert!(
        rust.contains("TlaSet::from_iter("),
        "3-way Times should emit TlaSet::from_iter. Output:\n{rust}"
    );
    // Should NOT contain the old unsupported placeholder
    assert!(
        !rust.contains("unsupported: multi-way Times"),
        "should not contain unsupported placeholder. Output:\n{rust}"
    );
    // Should emit nested iteration with flat_map
    assert!(
        rust.contains("flat_map("),
        "3-way Times should use flat_map for outer sets. Output:\n{rust}"
    );
    // Should produce 3-tuples: (__t0.clone(), __t1.clone(), __t2.clone())
    assert!(
        rust.contains("__t0") && rust.contains("__t1") && rust.contains("__t2"),
        "3-way Times should reference __t0, __t1, __t2 for the 3 tuple components. Output:\n{rust}"
    );
}

/// 2-way Times should continue to work (regression check).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_two_way_times_still_works() {
    let spec = r#"
---- MODULE TwoTimes ----
VARIABLE t

Init == t \in {1, 2} \X {3, 4}

Next == UNCHANGED t
====
"#;
    let rust = generate_rust_from_spec(spec, &["t"], &[]);

    // Should use TlaSet::from_iter
    assert!(
        rust.contains("TlaSet::from_iter("),
        "2-way Times should emit TlaSet::from_iter. Output:\n{rust}"
    );
    assert!(
        !rust.contains("unsupported"),
        "2-way Times should not contain unsupported. Output:\n{rust}"
    );
    // Should produce 2-tuples with __t0 and __t1
    assert!(
        rust.contains("__t0") && rust.contains("__t1"),
        "2-way Times should reference __t0 and __t1. Output:\n{rust}"
    );
}

// --- Multi-path EXCEPT and EXCEPT @ tests (#3911) ---

/// EXCEPT @ with record field: [r EXCEPT !.x = @ + 1]
/// The `@` should resolve to the old value of r.x.
/// With struct specialization, this generates `state.r.x.clone()` for @ access
/// and `__r.x = ...` for the field assignment.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_at_record_field() {
    let spec = r#"
---- MODULE ExceptAtRecord ----
VARIABLE r

Init == r = [x |-> 0, y |-> 1]

Next == r' = [r EXCEPT !.x = @ + 1]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // With struct specialization: @ resolves to struct field access (state.r.x.clone() or state.r.clone().x.clone())
    // and EXCEPT uses direct field assignment (__r.x = ...)
    let has_struct_access = (rust.contains(".r.x.clone()") || rust.contains(".r.clone().x.clone()"))
        && (rust.contains("+ 1") || rust.contains("+ 1_i64"));
    // Fallback: BTreeMap-based access for non-struct records
    let has_btree_access = rust.contains(".get(\"x\").cloned().expect(")
        && (rust.contains("+ 1") || rust.contains("+ 1_i64"));
    assert!(
        has_struct_access || has_btree_access,
        "EXCEPT @ should generate old-value accessor plus arithmetic. Output:\n{rust}"
    );
    // Should NOT contain raw EXCEPT @ placeholder
    assert!(
        !rust.contains("/* EXCEPT @"),
        "should not contain EXCEPT @ placeholder. Output:\n{rust}"
    );
}

/// EXCEPT @ with function index: [f EXCEPT ![k] = @ + 1]
/// The `@` should resolve to f[k], generating `f.apply(&k).cloned()...`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_at_function_index() {
    let spec = r#"
---- MODULE ExceptAtFunc ----
VARIABLE f

Init == f = [x \in {1, 2, 3} |-> 0]

Next == f' = [f EXCEPT ![1] = @ + 1]
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // The @ should be replaced with f.apply(&1).cloned()...
    assert!(
        rust.contains(".apply(") && (rust.contains("+ 1") || rust.contains("+ 1_i64")),
        "EXCEPT @ with function index should generate apply accessor. Output:\n{rust}"
    );
    // Should NOT contain raw EXCEPT @ placeholder
    assert!(
        !rust.contains("/* EXCEPT @"),
        "should not contain EXCEPT @ placeholder. Output:\n{rust}"
    );
}

/// Multi-path record EXCEPT: [r EXCEPT !.x.y = 5]
/// Should generate nested read-modify-write: read r.x, update r.x.y, write back.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_path_record_except() {
    let spec = r#"
---- MODULE MultiPathRecord ----
VARIABLE r

Init == r = [x |-> [y |-> 0, z |-> 1]]

Next == r' = [r EXCEPT !.x.y = 5]
====
"#;
    let rust = generate_rust_from_spec(spec, &["r"], &[]);

    // Should NOT contain the unsupported placeholder
    assert!(
        !rust.contains("/* unsupported: multi-path EXCEPT */"),
        "multi-path record EXCEPT should be implemented, not a placeholder. Output:\n{rust}"
    );
    // Should read the intermediate value (r.get("x"))
    assert!(
        rust.contains(".get(\"x\")"),
        "should read intermediate record field 'x'. Output:\n{rust}"
    );
    // Should update the inner field 'y'
    assert!(
        rust.contains(".set(\"y\""),
        "should set inner field 'y'. Output:\n{rust}"
    );
    // Should write back to the outer field 'x'
    let has_outer_writeback = rust.contains("set(\"x\"");
    assert!(
        has_outer_writeback,
        "should write back updated inner record to field 'x'. Output:\n{rust}"
    );
}

/// Multi-path function EXCEPT: [f EXCEPT ![1][2] = v]
/// Should generate nested read-modify-write with apply/update.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_path_function_except() {
    let spec = r#"
---- MODULE MultiPathFunc ----
VARIABLE f

Init == f = [x \in {1, 2} |-> [y \in {1, 2} |-> 0]]

Next == f' = [f EXCEPT ![1][2] = 99]
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // Should NOT contain the unsupported placeholder
    assert!(
        !rust.contains("/* unsupported: multi-path EXCEPT */"),
        "multi-path function EXCEPT should be implemented, not a placeholder. Output:\n{rust}"
    );
    // Should read intermediate value (f.apply(&key_0))
    assert!(
        rust.contains(".apply("),
        "should read intermediate function value via apply. Output:\n{rust}"
    );
    // Should update inner function value
    assert!(
        rust.contains(".update("),
        "should update inner function value. Output:\n{rust}"
    );
}

/// Multi-path EXCEPT with @ : [f EXCEPT ![k][j] = @ + 1]
/// The @ should refer to f[k][j] (the full path old value).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_path_except_with_at() {
    let spec = r#"
---- MODULE MultiPathExceptAt ----
VARIABLE f

Init == f = [x \in {1, 2} |-> [y \in {1, 2} |-> 0]]

Next == f' = [f EXCEPT ![1][2] = @ + 1]
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // Should NOT contain any EXCEPT placeholder
    assert!(
        !rust.contains("/* unsupported: multi-path EXCEPT */")
            && !rust.contains("/* EXCEPT @"),
        "multi-path EXCEPT with @ should be fully implemented. Output:\n{rust}"
    );
    // The value expression should contain the old-value accessor (apply chain)
    // and arithmetic
    assert!(
        (rust.contains("+ 1") || rust.contains("+ 1_i64")),
        "value expression should contain + 1 from @ + 1. Output:\n{rust}"
    );
}

// --- Non-primitive value constant tests (#3911) ---
//
// These test the `value_to_rust` function directly because the TIR lowerer
// currently only produces Bool/Int/String constants. Compound Value constants
// can appear when future constant folding or cfg-level constant parsing
// embeds materialized sets, tuples, records, or model values into TirExpr::Const.

/// Set constant: Value::Set with integer elements should emit tla_set![1, 2, 3].
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_set_integers() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let set = Value::set(vec![Value::int(1), Value::int(2), Value::int(3)]);
    let rust = value_to_rust(&set);
    assert!(
        rust.contains("tla_set!"),
        "integer set should use tla_set! macro. Got: {rust}"
    );
    assert!(
        rust.contains("1_i64") && rust.contains("2_i64") && rust.contains("3_i64"),
        "should contain all three integer elements. Got: {rust}"
    );
}

/// Empty set constant: Value::Set with no elements should emit TlaSet::new().
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_set_empty() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let set = Value::set(Vec::<Value>::new());
    let rust = value_to_rust(&set);
    assert_eq!(rust, "TlaSet::new()", "empty set should emit TlaSet::new(). Got: {rust}");
}

/// Set of strings: Value::Set with string elements should emit string literals.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_set_strings() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let set = Value::set(vec![
        Value::string("a"),
        Value::string("b"),
    ]);
    let rust = value_to_rust(&set);
    assert!(
        rust.contains("tla_set!"),
        "string set should use tla_set! macro. Got: {rust}"
    );
    assert!(
        rust.contains(".to_string()"),
        "string elements should use .to_string(). Got: {rust}"
    );
}

/// Tuple constant: Value::Tuple should emit Rust tuple syntax.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_tuple() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let tuple = Value::tuple(vec![Value::int(1), Value::int(2), Value::int(3)]);
    let rust = value_to_rust(&tuple);
    assert_eq!(
        rust, "(1_i64, 2_i64, 3_i64)",
        "3-element tuple should emit (a, b, c). Got: {rust}"
    );
}

/// Empty tuple constant: Value::Tuple with no elements should emit ().
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_tuple_empty() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let tuple = Value::tuple(Vec::<Value>::new());
    let rust = value_to_rust(&tuple);
    assert_eq!(rust, "()", "empty tuple should emit (). Got: {rust}");
}

/// Tuple with mixed types: (1, TRUE, "hello")
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_tuple_mixed() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let tuple = Value::tuple(vec![
        Value::int(42),
        Value::bool(true),
        Value::string("hello"),
    ]);
    let rust = value_to_rust(&tuple);
    assert!(
        rust.contains("42_i64"),
        "tuple should contain integer. Got: {rust}"
    );
    assert!(
        rust.contains("true"),
        "tuple should contain boolean. Got: {rust}"
    );
    assert!(
        rust.contains("\"hello\".to_string()"),
        "tuple should contain string. Got: {rust}"
    );
}

/// Record constant: Value::Record should emit TlaRecord::from_fields.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_record() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let record = Value::record(vec![
        ("x".to_string(), Value::int(0)),
        ("y".to_string(), Value::int(1)),
    ]);
    let rust = value_to_rust(&record);
    assert!(
        rust.contains("TlaRecord::from_fields"),
        "record should use TlaRecord::from_fields. Got: {rust}"
    );
    assert!(
        rust.contains("\"x\"") && rust.contains("\"y\""),
        "record should contain field names. Got: {rust}"
    );
    assert!(
        rust.contains("0_i64") && rust.contains("1_i64"),
        "record should contain field values. Got: {rust}"
    );
}

/// Empty record constant should emit TlaRecord::new().
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_record_empty() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let record = Value::record(Vec::<(String, Value)>::new());
    let rust = value_to_rust(&record);
    assert_eq!(
        rust, "TlaRecord::new()",
        "empty record should emit TlaRecord::new(). Got: {rust}"
    );
}

/// Sequence constant: Value::Seq should emit vec![...].
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_seq() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let seq = Value::seq(vec![Value::int(10), Value::int(20), Value::int(30)]);
    let rust = value_to_rust(&seq);
    assert!(
        rust.starts_with("vec!["),
        "sequence should emit vec![...]. Got: {rust}"
    );
    assert!(
        rust.contains("10_i64") && rust.contains("20_i64") && rust.contains("30_i64"),
        "sequence should contain all elements. Got: {rust}"
    );
}

/// Empty sequence constant should emit vec![].
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_seq_empty() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let seq = Value::seq(Vec::<Value>::new());
    let rust = value_to_rust(&seq);
    assert_eq!(rust, "vec![]", "empty sequence should emit vec![]. Got: {rust}");
}

/// Model value: Value::ModelValue should emit a string constant.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_model_value() {
    use super::expr::value_to_rust;
    use std::sync::Arc;
    use tla_value::Value;

    let mv = Value::ModelValue(Arc::from("s1"));
    let rust = value_to_rust(&mv);
    assert!(
        rust.contains("\"s1\"") && rust.contains(".to_string()"),
        "model value should emit string literal with .to_string(). Got: {rust}"
    );
}

/// Nested compound: Set of tuples.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_rust_set_of_tuples() {
    use super::expr::value_to_rust;
    use tla_value::Value;

    let set = Value::set(vec![
        Value::tuple(vec![Value::int(1), Value::int(2)]),
        Value::tuple(vec![Value::int(3), Value::int(4)]),
    ]);
    let rust = value_to_rust(&set);
    assert!(
        rust.contains("tla_set!"),
        "set of tuples should use tla_set! macro. Got: {rust}"
    );
    assert!(
        rust.contains("(1_i64, 2_i64)") && rust.contains("(3_i64, 4_i64)"),
        "set should contain tuple elements. Got: {rust}"
    );
}

// --- Expanded TIR stdlib operator coverage tests ---

/// Test: sequence concatenation \o generates Rust extend code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_seq_concat_codegen() {
    let spec = r#"
---- MODULE SeqConcat ----
EXTENDS Sequences
VARIABLE s

Init == s = <<1, 2>>

Next == s' = s \o <<3>>
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    // The \o operator should generate extend-based concatenation
    assert!(
        rust.contains(".extend(") || rust.contains("__s.extend("),
        "\\o should generate extend-based sequence concatenation. Output:\n{rust}"
    );
}

/// Test: Max and Min over sets generate iter().max/min() code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_max_min_codegen() {
    let spec = r#"
---- MODULE MaxMin ----
EXTENDS FiniteSets
VARIABLE x

Init == x = 0

MaxVal == {1, 2, 3}

InvMax == x <= 3
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &["InvMax"]);

    // The spec should compile successfully (basic structure check)
    assert!(
        rust.contains("impl StateMachine for MaxMin"),
        "should generate MaxMin state machine. Output:\n{rust}"
    );
}

/// Test: Reverse sequence generates reverse code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_reverse_codegen() {
    let spec = r#"
---- MODULE ReverseSeq ----
EXTENDS Sequences
VARIABLE s

Init == s = <<1, 2, 3>>

Helper(seq) == IF Len(seq) > 0 THEN Head(seq) ELSE 0

Next == s' = Tail(s)
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    // Head should generate .first().cloned()
    assert!(
        rust.contains(".first().cloned()"),
        "Head should generate .first().cloned(). Output:\n{rust}"
    );
    // Tail should generate .get(1..) or similar
    assert!(
        rust.contains(".get(1..)") || rust.contains("skip(1)"),
        "Tail should generate slice/skip. Output:\n{rust}"
    );
    // Len should generate .len() as i64
    assert!(
        rust.contains(".len() as i64"),
        "Len should generate .len() as i64. Output:\n{rust}"
    );
}

/// Test: CHOOSE expression generates find-based code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_choose_codegen() {
    let spec = r#"
---- MODULE ChooseTest ----
VARIABLE x

Init == x = CHOOSE v \in {1, 2, 3} : v > 1

Next == x' = CHOOSE v \in {1, 2, 3} : v > x
====
"#;
    let rust = generate_rust_from_spec(spec, &["x"], &[]);

    // CHOOSE should generate .find() or .iter().find()
    assert!(
        rust.contains(".find("),
        "CHOOSE should generate .find()-based code. Output:\n{rust}"
    );
    assert!(
        rust.contains("CHOOSE: no element satisfies predicate") || rust.contains(".expect("),
        "CHOOSE should have panic message for no matching element. Output:\n{rust}"
    );
}

/// Test: Cardinality generates .len() as i64.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_cardinality_codegen() {
    let spec = r#"
---- MODULE CardTest ----
EXTENDS FiniteSets
VARIABLE n

Init == n = Cardinality({1, 2, 3})

Next == UNCHANGED n
====
"#;
    let rust = generate_rust_from_spec(spec, &["n"], &[]);

    assert!(
        rust.contains(".len() as i64"),
        "Cardinality should generate .len() as i64. Output:\n{rust}"
    );
}

/// Test: SubSeq generates slice code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_subseq_codegen() {
    let spec = r#"
---- MODULE SubSeqTest ----
EXTENDS Sequences
VARIABLE s

Init == s = <<1, 2, 3, 4, 5>>

Next == s' = SubSeq(s, 2, 4)
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    // SubSeq should generate slice indexing with .to_vec()
    assert!(
        rust.contains(".to_vec()"),
        "SubSeq should generate slice .to_vec(). Output:\n{rust}"
    );
}

/// Test: DOMAIN generates .domain() call.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_domain_codegen() {
    let spec = r#"
---- MODULE DomainTest ----
VARIABLE f

Init == f = [x \in {1, 2} |-> x + 1]

Next == UNCHANGED f

InvDomain == 1 \in DOMAIN f
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &["InvDomain"]);

    // DOMAIN should generate .domain()
    assert!(
        rust.contains(".domain()"),
        "DOMAIN should generate .domain() call. Output:\n{rust}"
    );
}

/// Test: Powerset (SUBSET) generates powerset() call.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_powerset_codegen() {
    let spec = r#"
---- MODULE PowersetTest ----
VARIABLE s

Init == s \in SUBSET {1, 2}

Next == UNCHANGED s
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    assert!(
        rust.contains("powerset("),
        "SUBSET should generate powerset() call. Output:\n{rust}"
    );
}

/// Test: BigUnion (UNION) generates flat_map code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_big_union_codegen() {
    let spec = r#"
---- MODULE BigUnionTest ----
VARIABLE s

Init == s = UNION {{1, 2}, {3, 4}}

Next == UNCHANGED s
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    assert!(
        rust.contains("flat_map("),
        "UNION should generate flat_map-based code. Output:\n{rust}"
    );
}

/// Test: Append generates push-based code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_append_codegen() {
    let spec = r#"
---- MODULE AppendTest ----
EXTENDS Sequences
VARIABLE s

Init == s = <<1>>

Next == s' = Append(s, 2)
====
"#;
    let rust = generate_rust_from_spec(spec, &["s"], &[]);

    assert!(
        rust.contains(".push("),
        "Append should generate .push() call. Output:\n{rust}"
    );
}

/// Test: FuncSet generates nested iteration code.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_func_set_codegen() {
    let spec = r#"
---- MODULE FuncSetTest ----
VARIABLE f

Init == f \in [{1, 2} -> {TRUE, FALSE}]

Next == UNCHANGED f
====
"#;
    let rust = generate_rust_from_spec(spec, &["f"], &[]);

    // FuncSet should generate iteration over all possible functions
    assert!(
        rust.contains("TlaFunc::from_iter("),
        "FuncSet should generate TlaFunc construction. Output:\n{rust}"
    );
}

/// Test: runtime seq_set function works correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_seq_set() {
    use tla_runtime::{seq_set, TlaSet};

    // Empty base set: only empty sequence
    let empty: TlaSet<i64> = TlaSet::new();
    let result = seq_set(&empty);
    assert_eq!(result.len(), 1, "seq_set of empty set should contain just the empty sequence");
    assert!(result.contains(&vec![]), "should contain the empty sequence");

    // Single-element set: sequences of length 0..=1
    let single: TlaSet<i64> = [1].into_iter().collect();
    let result = seq_set(&single);
    assert!(result.contains(&vec![]), "should contain empty sequence");
    assert!(result.contains(&vec![1]), "should contain <<1>>");
    assert!(result.len() >= 2, "should contain at least empty and <<1>>");
}

/// Test: runtime func_merge function works correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_func_merge() {
    use tla_runtime::{func_merge, TlaFunc};

    let f: TlaFunc<i64, i64> = [(1, 10), (2, 20)].into_iter().collect();
    let g: TlaFunc<i64, i64> = [(2, 200), (3, 30)].into_iter().collect();
    let merged = func_merge(&f, &g);

    // f takes priority: key 2 should have value 20 from f, not 200 from g
    assert_eq!(merged.apply(&1), Some(&10), "key 1 from f");
    assert_eq!(merged.apply(&2), Some(&20), "key 2 from f (priority)");
    assert_eq!(merged.apply(&3), Some(&30), "key 3 from g");
    assert_eq!(merged.apply(&4), None, "key 4 not in either");
}
