// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for expand_operators scope handling: bound variable scope isolation,
//! quantifier scope, lambda scope.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_bound_var_scope_does_not_leak() {
    use tla_core::ast::{BoundVar, OperatorDef};

    let op_defs = std::collections::HashMap::from([(
        "Foo".to_string(),
        OperatorDef {
            name: spanned("Foo".to_string()),
            params: vec![],
            body: spanned(Expr::Int(42.into())),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        },
    )]);

    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let scoped_foo = Expr::Exists(
        vec![BoundVar {
            name: spanned("Foo".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                1.into(),
            ))])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "Foo".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(1.into()))),
        ))),
    );

    let expr = Expr::And(
        Box::new(spanned(scoped_foo)),
        Box::new(spanned(Expr::Ident(
            "Foo".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    );

    let expanded = emitter.expand_operators(&expr);

    let Expr::And(lhs, rhs) = expanded else {
        panic!("expected And expression after expansion");
    };
    assert!(
        matches!(&rhs.node, Expr::Int(n) if *n == 42.into()),
        "expected right-hand Foo to expand into operator body"
    );

    let Expr::Exists(_, body) = &lhs.node else {
        panic!("expected left side to remain quantified");
    };
    let Expr::Eq(bound_ref, _) = &body.node else {
        panic!("expected quantified body to remain equality");
    };
    assert!(
        matches!(&bound_ref.node, Expr::Ident(name, NameId::INVALID) if name == "Foo"),
        "expected bound Foo inside quantifier to remain bound identifier"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_substitution_respects_quantifier_scope() {
    use tla_core::ast::{BoundVar, OpParam, OperatorDef};

    let op_defs = std::collections::HashMap::from([(
        "Op".to_string(),
        OperatorDef {
            name: spanned("Op".to_string()),
            params: vec![OpParam {
                name: spanned("x".to_string()),
                arity: 0,
            }],
            body: spanned(Expr::And(
                Box::new(spanned(Expr::Exists(
                    vec![BoundVar {
                        name: spanned("x".to_string()),
                        domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                            1.into(),
                        ))])))),
                        pattern: None,
                    }],
                    Box::new(spanned(Expr::Eq(
                        Box::new(spanned(Expr::Ident(
                            "x".to_string(),
                            tla_core::name_intern::NameId::INVALID,
                        ))),
                        Box::new(spanned(Expr::Int(1.into()))),
                    ))),
                ))),
                Box::new(spanned(Expr::Eq(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(2.into()))),
                ))),
            )),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        },
    )]);

    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Op".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Int(7.into()))],
    );
    let expanded = emitter.expand_operators(&expr);

    let Expr::And(lhs, rhs) = expanded else {
        panic!("expected Op application to expand into And");
    };

    let Expr::Eq(lhs_rhs, rhs_rhs) = &rhs.node else {
        panic!("expected right side of expanded Op to be Eq");
    };
    assert!(
        matches!(&lhs_rhs.node, Expr::Int(n) if *n == 7.into()),
        "expected free parameter x to substitute to argument value"
    );
    assert!(
        matches!(&rhs_rhs.node, Expr::Int(n) if *n == 2.into()),
        "expected literal on right side to remain unchanged"
    );

    let Expr::Exists(_, body) = &lhs.node else {
        panic!("expected left side to remain quantified");
    };
    let Expr::Eq(bound_ref, _) = &body.node else {
        panic!("expected quantified body to remain equality");
    };
    assert!(
        matches!(&bound_ref.node, Expr::Ident(name, NameId::INVALID) if name == "x"),
        "expected bound x inside quantifier to remain bound identifier"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_substitution_respects_lambda_scope() {
    use tla_core::ast::{OpParam, OperatorDef};

    let op_defs = std::collections::HashMap::from([(
        "Op".to_string(),
        OperatorDef {
            name: spanned("Op".to_string()),
            params: vec![OpParam {
                name: spanned("x".to_string()),
                arity: 0,
            }],
            body: spanned(Expr::And(
                Box::new(spanned(Expr::Apply(
                    Box::new(spanned(Expr::Lambda(
                        vec![spanned("x".to_string())],
                        Box::new(spanned(Expr::Ident(
                            "x".to_string(),
                            tla_core::name_intern::NameId::INVALID,
                        ))),
                    ))),
                    vec![spanned(Expr::Int(1.into()))],
                ))),
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
            )),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        },
    )]);

    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Op".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Int(7.into()))],
    );
    let expanded = emitter.expand_operators(&expr);

    let Expr::And(lhs, rhs) = expanded else {
        panic!("expected Op application to expand into And");
    };
    assert!(
        matches!(&rhs.node, Expr::Int(n) if *n == 7.into()),
        "expected free parameter x to substitute to argument value"
    );

    let Expr::Apply(op, _) = &lhs.node else {
        panic!("expected left side to remain lambda application");
    };
    let Expr::Lambda(_, body) = &op.node else {
        panic!("expected applied operator to remain a lambda");
    };
    assert!(
        matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x"),
        "expected lambda-bound x to remain bound identifier"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_params_shadow_zero_arg_helpers() {
    use tla_core::ast::{OpParam, OperatorDef};

    let op_defs = std::collections::HashMap::from([
        (
            "Arg".to_string(),
            OperatorDef {
                name: spanned("Arg".to_string()),
                params: vec![],
                body: spanned(Expr::Int((-1).into())),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ),
        (
            "Foo".to_string(),
            OperatorDef {
                name: spanned("Foo".to_string()),
                params: vec![OpParam {
                    name: spanned("Arg".to_string()),
                    arity: 0,
                }],
                body: spanned(Expr::Ident("Arg".to_string(), NameId::INVALID)),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ),
    ]);

    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Apply(
        Box::new(spanned(Expr::Ident("Foo".to_string(), NameId::INVALID))),
        vec![spanned(Expr::Int(7.into()))],
    );
    let expanded = emitter.expand_operators(&expr);

    assert!(
        matches!(expanded, Expr::Int(n) if n == 7.into()),
        "expected parameter Arg to shadow zero-arg helper during substitution"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_bound_args_do_not_reexpand_under_callee_scope() {
    use tla_core::ast::{BoundVar, OpParam, OperatorDef};

    let op_defs = std::collections::HashMap::from([
        (
            "X".to_string(),
            OperatorDef {
                name: spanned("X".to_string()),
                params: vec![],
                body: spanned(Expr::Int(99.into())),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ),
        (
            "Foo".to_string(),
            OperatorDef {
                name: spanned("Foo".to_string()),
                params: vec![OpParam {
                    name: spanned("p".to_string()),
                    arity: 0,
                }],
                body: spanned(Expr::Ident("p".to_string(), NameId::INVALID)),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ),
    ]);

    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Exists(
        vec![BoundVar {
            name: spanned("X".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                1.into(),
            ))])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Apply(
            Box::new(spanned(Expr::Ident("Foo".to_string(), NameId::INVALID))),
            vec![spanned(Expr::Ident("X".to_string(), NameId::INVALID))],
        ))),
    );

    let expanded = emitter.expand_operators(&expr);

    let Expr::Exists(_, body) = expanded else {
        panic!("expected existential after expansion");
    };
    assert!(
        matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "X"),
        "expected bound argument X to survive operator expansion without re-expanding to helper X"
    );
}
