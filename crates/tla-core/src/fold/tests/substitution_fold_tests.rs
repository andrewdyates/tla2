// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simple substitution fold tests: verifies that custom ExprFold overrides
//! work across expression types using a ReplaceXWith42 fold.

use super::*;

struct ReplaceXWith42;
impl ExprFold for ReplaceXWith42 {
    fn fold_ident(&mut self, name: String, name_id: NameId) -> Expr {
        if name == "x" {
            Expr::Int(BigInt::from(42))
        } else {
            Expr::Ident(name, name_id)
        }
    }
}

#[test]
fn test_substitution_fold_simple() {
    let expr = spanned(Expr::Ident("x".to_string(), NameId::INVALID));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    assert!(assert_expr_eq(&Expr::Int(BigInt::from(42)), &output.node));
}

#[test]
fn test_substitution_fold_nested() {
    // x + y => 42 + y
    let expr = spanned(Expr::Add(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    let expected = Expr::Add(
        boxed_expr(Expr::Int(BigInt::from(42))),
        boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
    );
    assert!(assert_expr_eq(&expected, &output.node));
}

#[test]
fn test_substitution_fold_deep_nesting() {
    // IF x THEN {x, x} ELSE x
    let expr = spanned(Expr::If(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        boxed_expr(Expr::SetEnum(vec![
            spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
            spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
        ])),
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    let expected = Expr::If(
        boxed_expr(Expr::Int(BigInt::from(42))),
        boxed_expr(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(42))),
            spanned(Expr::Int(BigInt::from(42))),
        ])),
        boxed_expr(Expr::Int(BigInt::from(42))),
    );
    assert!(assert_expr_eq(&expected, &output.node));
}

#[test]
fn test_substitution_in_record() {
    // [a |-> x, b |-> y] => [a |-> 42, b |-> y]
    let expr = spanned(Expr::Record(vec![
        (
            spanned("a".to_string()),
            spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
        ),
        (
            spanned("b".to_string()),
            spanned(Expr::Ident("y".to_string(), NameId::INVALID)),
        ),
    ]));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Record(fields) = &output.node {
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &fields[0].1.node
        ));
        assert!(assert_expr_eq(
            &Expr::Ident("y".to_string(), NameId::INVALID),
            &fields[1].1.node
        ));
    } else {
        panic!("Expected Record");
    }
}

#[test]
fn test_substitution_in_except_index() {
    // [f EXCEPT ![x] = x] => [f EXCEPT ![42] = 42]
    let expr = spanned(Expr::Except(
        boxed_expr(Expr::Ident("f".to_string(), NameId::INVALID)),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(spanned(Expr::Ident(
                "x".to_string(),
                NameId::INVALID,
            )))],
            value: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
        }],
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Except(_, specs) = &output.node {
        if let ExceptPathElement::Index(idx) = &specs[0].path[0] {
            assert!(assert_expr_eq(&Expr::Int(BigInt::from(42)), &idx.node));
        } else {
            panic!("Expected Index path element");
        }
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &specs[0].value.node
        ));
    } else {
        panic!("Expected Except");
    }
}

#[test]
fn test_substitution_in_instance_expr() {
    // INSTANCE M WITH Data <- x => INSTANCE M WITH Data <- 42
    let expr = spanned(Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: spanned("Data".to_string()),
            to: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
        }],
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::InstanceExpr(name, substs) = &output.node {
        assert_eq!(name, "M");
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &substs[0].to.node
        ));
        assert_eq!(substs[0].from.node, "Data");
    } else {
        panic!("Expected InstanceExpr");
    }
}

#[test]
fn test_substitution_in_module_ref_params() {
    // IS(x)!Op => IS(42)!Op
    let expr = spanned(Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![spanned(Expr::Ident("x".to_string(), NameId::INVALID))],
        ),
        "Op".to_string(),
        vec![],
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::ModuleRef(ModuleTarget::Parameterized(_, params), _, _) = &output.node {
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &params[0].node
        ));
    } else {
        panic!("Expected ModuleRef Parameterized");
    }
}

#[test]
fn test_substitution_in_quantifier_domain() {
    // \A y \in x : y  => \A y \in 42 : y
    let expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Forall(bounds, body) = &output.node {
        if let Some(domain) = &bounds[0].domain {
            assert!(assert_expr_eq(&Expr::Int(BigInt::from(42)), &domain.node));
        } else {
            panic!("Expected domain");
        }
        // y should NOT be substituted (different name)
        assert!(assert_expr_eq(
            &Expr::Ident("y".to_string(), NameId::INVALID),
            &body.node
        ));
    } else {
        panic!("Expected Forall");
    }
}

#[test]
fn test_substitution_in_let_body() {
    // LET op == x IN x => LET op == 42 IN 42
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("op".to_string()),
            params: vec![],
            body: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Let(defs, body) = &output.node {
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &defs[0].body.node
        ));
        assert!(assert_expr_eq(&Expr::Int(BigInt::from(42)), &body.node));
    } else {
        panic!("Expected Let");
    }
}

#[test]
fn test_substitution_in_case() {
    // CASE x -> x [] OTHER -> x
    let expr = spanned(Expr::Case(
        vec![CaseArm {
            guard: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
            body: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
        }],
        Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Case(arms, default) = &output.node {
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &arms[0].guard.node
        ));
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &arms[0].body.node
        ));
        assert!(assert_expr_eq(
            &Expr::Int(BigInt::from(42)),
            &default.as_ref().unwrap().node
        ));
    } else {
        panic!("Expected Case");
    }
}

#[test]
fn test_substitution_in_lambda_body() {
    // LAMBDA a : x  => LAMBDA a : 42
    let expr = spanned(Expr::Lambda(
        vec![spanned("a".to_string())],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut fold = ReplaceXWith42;
    let output = fold.fold_expr(expr);
    if let Expr::Lambda(params, body) = &output.node {
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].node, "a");
        assert!(assert_expr_eq(&Expr::Int(BigInt::from(42)), &body.node));
    } else {
        panic!("Expected Lambda");
    }
}
