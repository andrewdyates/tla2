// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for full generate_rust integration: counter, invariant, kani,
//! nondeterministic init.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generate_simple_counter() {
    let module = make_counter_module();

    let options = CodeGenOptions {
        generate_checker: true,
        ..Default::default()
    };
    let result = generate_rust(&module, &options).unwrap();

    // Check that the generated code contains expected elements
    assert!(result.contains("pub struct CounterState"));
    assert!(result.contains("pub count: i64"));
    assert!(result.contains("impl StateMachine for Counter"));
    assert!(result.contains("fn init(&self)"));
    assert!(result.contains("fn for_each_init"));
    assert!(result.contains("fn next(&self, state: &Self::State)"));
    assert!(result.contains("fn for_each_next"));
    assert!(result.contains("for_each_next(&old_state"));
    assert!(!result.contains("machine.init()"));
    assert!(!result.contains("self.init("));
    assert!(!result.contains("machine.next(&old_state)"));
    assert!(
        !result.contains("self.next("),
        "expected generated for_each_next to avoid delegating to next()"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generate_with_invariant() {
    use tla_core::ast::{Module, OperatorDef, Unit};

    let inv_body = Expr::Geq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(0.into()))),
    );

    let init_body = Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(0.into()))),
    );

    let module = Module {
        name: spanned("Counter".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("count".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("InvNonNegative".to_string()),
                params: vec![],
                body: spanned(inv_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    };

    let options = CodeGenOptions::default();
    let result = generate_rust(&module, &options).unwrap();

    // Check that invariant method is generated
    assert!(result.contains("fn check_inv_non_negative(&self, state: &CounterState) -> bool"));
    assert!(result.contains("(state.count >= 0_i64)"));
    assert!(result.contains("fn invariant_names(&self) -> Vec<&'static str>"));
    assert!(result.contains("vec![\"InvNonNegative\"]"));
    assert!(result.contains(
        "fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool>"
    ));
    assert!(result.contains("\"InvNonNegative\" => Some(self.check_inv_non_negative(state)),"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generate_with_kani() {
    use tla_core::ast::{Module, OperatorDef, Unit};

    let init_body = Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(0.into()))),
    );

    let module = Module {
        name: spanned("Simple".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("x".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: true,
        generate_checker: false,
        checker_map: None,
    };
    let result = generate_rust(&module, &options).unwrap();

    // Check that Kani proofs are generated
    assert!(result.contains("#[cfg(kani)]"));
    assert!(result.contains("mod kani_proofs"));
    assert!(result.contains("#[kani::proof]"));
    assert!(result.contains("fn init_satisfies_invariants()"));
    assert!(result.contains("fn next_preserves_invariants()"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_nondeterministic() {
    use tla_core::ast::{Module, OperatorDef, Unit};

    // Init == x \in 1..3
    let init_body = Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(1.into()))),
            Box::new(spanned(Expr::Int(3.into()))),
        ))),
    );

    let module = Module {
        name: spanned("Nondet".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("x".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    };

    let options = CodeGenOptions::default();
    let result = generate_rust(&module, &options).unwrap();

    // Check that non-deterministic init generates a loop
    assert!(result.contains("for x in range_set(1_i64, 3_i64)"));
    assert!(result.contains("states.push("));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generate_recursive_operator_helper() {
    use tla_core::ast::{Module, OpParam, OperatorDef, Unit};

    let init_body = Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "dummy".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(0.into()))),
    );

    let factorial_body = Expr::If(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "n".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(0.into()))),
        ))),
        Box::new(spanned(Expr::Int(1.into()))),
        Box::new(spanned(Expr::Mul(
            Box::new(spanned(Expr::Ident(
                "n".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Apply(
                Box::new(spanned(Expr::Ident(
                    "Factorial".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                vec![spanned(Expr::Sub(
                    Box::new(spanned(Expr::Ident(
                        "n".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(1.into()))),
                ))],
            ))),
        ))),
    );

    let inv_body = Expr::Eq(
        Box::new(spanned(Expr::Apply(
            Box::new(spanned(Expr::Ident(
                "Factorial".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            vec![spanned(Expr::Int(5.into()))],
        ))),
        Box::new(spanned(Expr::Int(120.into()))),
    );

    let module = Module {
        name: spanned("RecursiveFactorial".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("dummy".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Factorial".to_string()),
                params: vec![OpParam {
                    name: spanned("n".to_string()),
                    arity: 0,
                }],
                body: spanned(factorial_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: true,
                self_call_count: 1,
            })),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("InvFactorial".to_string()),
                params: vec![],
                body: spanned(inv_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    };

    let result = generate_rust(&module, &CodeGenOptions::default()).unwrap();

    assert!(result.contains("const MAX_RECURSION_DEPTH: u32 = 10000;"));
    assert!(result.contains("fn factorial(&self, n: &i64, __depth: u32) -> i64 {"));
    assert!(result.contains("if __depth > Self::MAX_RECURSION_DEPTH {"));
    assert!(result.contains("self.factorial(&(n - 1_i64), __depth + 1)"));
    assert!(
        result.contains("fn check_inv_factorial(&self, state: &RecursiveFactorialState) -> bool")
    );
    assert!(result.contains("(self.factorial(&5_i64, 0) == 120_i64)"));
}

/// Test that record-typed state variables use type-specialized structs (#3926).
///
/// When type inference determines that a state variable is a record with
/// statically known field types, the generated code should use a named
/// Rust struct instead of TlaRecord<Value>.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_struct_specialization_for_record_state_vars() {
    use tla_core::ast::{Module, OperatorDef, Unit};

    // Build: VARIABLE r
    //        Init == r = [x |-> 0, y |-> TRUE]
    //        Next == r' = [x |-> r.x + 1, y |-> ~r.y]
    let init_body = Expr::Eq(
        Box::new(spanned(Expr::Ident("r".to_string(), NameId::INVALID))),
        Box::new(spanned(Expr::Record(vec![
            (
                spanned("x".to_string()),
                spanned(Expr::Int(0.into())),
            ),
            (
                spanned("y".to_string()),
                spanned(Expr::Bool(true)),
            ),
        ]))),
    );

    let next_body = Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "r".to_string(),
            NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Record(vec![
            (
                spanned("x".to_string()),
                spanned(Expr::Add(
                    Box::new(spanned(Expr::RecordAccess(
                        Box::new(spanned(Expr::Ident("r".to_string(), NameId::INVALID))),
                        spanned("x".to_string()).into(),
                    ))),
                    Box::new(spanned(Expr::Int(1.into()))),
                )),
            ),
            (
                spanned("y".to_string()),
                spanned(Expr::Not(Box::new(spanned(Expr::RecordAccess(
                    Box::new(spanned(Expr::Ident("r".to_string(), NameId::INVALID))),
                    spanned("y".to_string()).into(),
                ))))),
            ),
        ]))),
    );

    let module = Module {
        name: spanned("RecordSpec".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("r".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Next".to_string()),
                params: vec![],
                body: spanned(next_body),
                local: false,
                contains_prime: true,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    };

    let options = CodeGenOptions::default();
    let result = generate_rust(&module, &options).unwrap();

    // Should emit type-specialized record struct
    assert!(
        result.contains("// Type-specialized record structs"),
        "should have struct section header. Output:\n{result}"
    );
    assert!(
        result.contains("pub struct Record"),
        "should emit specialized record struct. Output:\n{result}"
    );
    // State struct should use the specialized struct, not TlaRecord<Value>
    assert!(
        !result.contains("pub r: TlaRecord<Value>"),
        "state field should NOT use TlaRecord<Value>. Output:\n{result}"
    );
    assert!(
        result.contains("pub r: Record"),
        "state field should use specialized Record type. Output:\n{result}"
    );
}

/// Test that specs with no record types produce no struct section.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_struct_section_for_simple_types() {
    let module = make_counter_module();
    let options = CodeGenOptions::default();
    let result = generate_rust(&module, &options).unwrap();

    // Should NOT have struct definitions for a simple integer-only spec
    assert!(
        !result.contains("// Type-specialized record structs"),
        "should NOT have struct section for non-record specs. Output:\n{result}"
    );
}
