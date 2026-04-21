// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Identity fold tests: verifies the default ExprFold implementation preserves
//! structure unchanged.

use super::*;

struct IdentityFold;
impl ExprFold for IdentityFold {}

#[test]
fn test_identity_fold_leaf_nodes() {
    let cases: Vec<Expr> = vec![
        Expr::Bool(true),
        Expr::Bool(false),
        Expr::Int(BigInt::from(42)),
        Expr::String("hello".to_string()),
        Expr::Ident("x".to_string(), NameId::INVALID),
        Expr::OpRef("Plus".to_string()),
    ];

    let mut fold = IdentityFold;
    for expr in cases {
        let input = spanned(expr.clone());
        let output = fold.fold_expr(input);
        assert!(
            assert_expr_eq(&expr, &output.node),
            "Identity fold changed leaf: {expr:?}"
        );
    }
}

#[test]
fn test_identity_fold_binary() {
    let expr = Expr::And(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        boxed_expr(Expr::Bool(true)),
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
}

#[test]
fn test_identity_fold_complex_nested() {
    // IF x THEN {1, 2} ELSE \A y \in S : y > 0
    let expr = Expr::If(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        boxed_expr(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])),
        boxed_expr(Expr::Forall(
            vec![BoundVar {
                name: spanned("y".to_string()),
                domain: Some(boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID))),
                pattern: None,
            }],
            boxed_expr(Expr::Gt(
                boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
                boxed_expr(Expr::Int(BigInt::from(0))),
            )),
        )),
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
}

#[test]
fn test_identity_fold_let_preserves_all_fields() {
    let expr = Expr::Let(
        vec![OperatorDef {
            name: spanned("op".to_string()),
            params: vec![OpParam {
                name: spanned("p".to_string()),
                arity: 0,
            }],
            body: spanned(Expr::Ident("p".to_string(), NameId::INVALID)),
            local: true,
            contains_prime: true,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Ident("op".to_string(), NameId::INVALID)),
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
    // Verify OperatorDef fields preserved
    if let Expr::Let(defs, _) = &output.node {
        assert_eq!(defs.len(), 1);
        assert!(defs[0].local);
        assert!(defs[0].contains_prime);
        assert!(!defs[0].guards_depend_on_prime);
        assert_eq!(defs[0].params.len(), 1);
        assert_eq!(defs[0].params[0].name.node, "p");
    } else {
        panic!("Expected Let");
    }
}

#[test]
fn test_identity_fold_except_path_elements() {
    // [f EXCEPT ![i].field = v]
    let expr = Expr::Except(
        boxed_expr(Expr::Ident("f".to_string(), NameId::INVALID)),
        vec![ExceptSpec {
            path: vec![
                ExceptPathElement::Index(spanned(Expr::Ident("i".to_string(), NameId::INVALID))),
                ExceptPathElement::Field(spanned("field".to_string()).into()),
            ],
            value: spanned(Expr::Ident("v".to_string(), NameId::INVALID)),
        }],
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
}

#[test]
fn test_identity_fold_instance_expr() {
    let expr = Expr::InstanceExpr(
        "Chan".to_string(),
        vec![Substitution {
            from: spanned("Data".to_string()),
            to: spanned(Expr::Ident("Message".to_string(), NameId::INVALID)),
        }],
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
}

#[test]
fn test_identity_fold_module_ref_parameterized() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![
                spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
                spanned(Expr::Int(BigInt::from(1))),
            ],
        ),
        "Op".to_string(),
        vec![spanned(Expr::Bool(true))],
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
}

#[test]
fn test_identity_fold_bound_var_with_pattern() {
    // \E <<x, y>> \in S : x = y
    let expr = Expr::Exists(
        vec![BoundVar {
            name: spanned("_tup".to_string()),
            domain: Some(boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID))),
            pattern: Some(BoundPattern::Tuple(vec![
                spanned("x".to_string()),
                spanned("y".to_string()),
            ])),
        }],
        boxed_expr(Expr::Eq(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    );
    let mut fold = IdentityFold;
    let output = fold.fold_expr(spanned(expr.clone()));
    assert!(assert_expr_eq(&expr, &output.node));
    // Verify pattern preserved
    if let Expr::Exists(bounds, _) = &output.node {
        assert!(bounds[0].pattern.is_some());
        if let Some(BoundPattern::Tuple(vars)) = &bounds[0].pattern {
            assert_eq!(vars.len(), 2);
            assert_eq!(vars[0].node, "x");
            assert_eq!(vars[1].node, "y");
        } else {
            panic!("Expected Tuple pattern");
        }
    } else {
        panic!("Expected Exists");
    }
}
