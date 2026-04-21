// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::enumerate::local_scope::LocalScope;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_local_scope_get_depth_prefers_innermost_binding() {
    let scope = LocalScope::new().with_var("x").with_var("y").with_var("x");
    assert_eq!(scope.get_depth("x"), Some(0));
    assert_eq!(scope.get_depth("y"), Some(1));
    assert_eq!(scope.get_depth("z"), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_values_fingerprint_same_values() {
    let v1 = vec![Value::int(1), Value::int(2)];
    let v2 = vec![Value::int(1), Value::int(2)];
    assert_eq!(
        compute_values_fingerprint(&v1),
        compute_values_fingerprint(&v2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_values_fingerprint_different_values() {
    let v1 = vec![Value::int(1), Value::int(2)];
    let v2 = vec![Value::int(2), Value::int(1)];
    assert_ne!(
        compute_values_fingerprint(&v1),
        compute_values_fingerprint(&v2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_values_fingerprint_empty() {
    let v1: Vec<Value> = vec![];
    let v2: Vec<Value> = vec![];
    assert_eq!(
        compute_values_fingerprint(&v1),
        compute_values_fingerprint(&v2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_unconstrained_vars_all_constrained() {
    let vars: Vec<Arc<str>> = vec![Arc::from("x"), Arc::from("y")];
    let branches = vec![vec![
        Constraint::Eq("x".to_string(), Value::int(1)),
        Constraint::Eq("y".to_string(), Value::int(2)),
    ]];
    let unconstrained = find_unconstrained_vars(&vars, &branches);
    assert!(unconstrained.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_unconstrained_vars_some_unconstrained() {
    let vars: Vec<Arc<str>> = vec![Arc::from("x"), Arc::from("y")];
    let branches = vec![vec![Constraint::Eq("x".to_string(), Value::int(1))]];
    let unconstrained = find_unconstrained_vars(&vars, &branches);
    assert_eq!(unconstrained, vec!["y"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_unconstrained_vars_in_constraint() {
    let vars: Vec<Arc<str>> = vec![Arc::from("x")];
    let branches = vec![vec![Constraint::In(
        "x".to_string(),
        InitDomain::Concrete(vec![Value::int(1), Value::int(2)]),
    )]];
    let unconstrained = find_unconstrained_vars(&vars, &branches);
    assert!(unconstrained.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_unconstrained_vars_noteq_not_sufficient() {
    // NotEq alone cannot define a domain
    let vars: Vec<Arc<str>> = vec![Arc::from("x")];
    let branches = vec![vec![Constraint::NotEq("x".to_string(), Value::int(1))]];
    let unconstrained = find_unconstrained_vars(&vars, &branches);
    assert_eq!(unconstrained, vec!["x"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_unconstrained_vars_multiple_branches() {
    let vars: Vec<Arc<str>> = vec![Arc::from("x"), Arc::from("y")];
    let branches = vec![
        vec![Constraint::Eq("x".to_string(), Value::int(1))],
        vec![Constraint::Eq("y".to_string(), Value::int(2))],
    ];
    // x is constrained in branch 0, y is constrained in branch 1
    // Each var only needs to be constrained in SOME branch
    let unconstrained = find_unconstrained_vars(&vars, &branches);
    assert!(unconstrained.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_eq_constraint() {
    let var = Arc::from("x");
    let constraints = vec![Constraint::Eq("x".to_string(), Value::int(42))];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("eager equality domain should not raise eval errors");
    assert_eq!(values, Some(vec![Value::int(42)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_in_constraint() {
    let var = Arc::from("x");
    let constraints = vec![Constraint::In(
        "x".to_string(),
        InitDomain::Concrete(vec![Value::int(1), Value::int(2), Value::int(3)]),
    )];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("eager set domain should not raise eval errors");
    let v = values.expect("should find values for In constraint");
    assert_eq!(v.len(), 3);
    assert!(v.contains(&Value::int(1)));
    assert!(v.contains(&Value::int(2)));
    assert!(v.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_intersection() {
    let var = Arc::from("x");
    let constraints = vec![
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![Value::int(1), Value::int(2), Value::int(3)]),
        ),
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![Value::int(2), Value::int(3), Value::int(4)]),
        ),
    ];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("intersecting eager domains should not raise eval errors");
    let v = values.expect("should find intersection values");
    assert_eq!(v.len(), 2); // {2, 3}
    assert!(v.contains(&Value::int(2)));
    assert!(v.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_noteq_exclusion() {
    let var = Arc::from("x");
    let constraints = vec![
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![Value::int(1), Value::int(2), Value::int(3)]),
        ),
        Constraint::NotEq("x".to_string(), Value::int(2)),
    ];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("eager exclusion should not raise eval errors");
    assert!(values.is_some());
    let v = values.unwrap();
    assert_eq!(v.len(), 2); // {1, 3}
    assert!(!v.contains(&Value::int(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_empty_intersection() {
    let var = Arc::from("x");
    let constraints = vec![
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![Value::int(1), Value::int(2)]),
        ),
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![Value::int(3), Value::int(4)]),
        ),
    ];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("eager empty intersection should not raise eval errors");
    assert_eq!(values, Some(vec![]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_values_for_var_wrong_var() {
    let var = Arc::from("x");
    let constraints = vec![Constraint::Eq("y".to_string(), Value::int(42))];
    let values = find_values_for_var(None, &var, &constraints)
        .expect("unrelated constraints should not raise eval errors");
    assert_eq!(values, None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_count_expr_nodes_simple() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    assert_eq!(count_expr_nodes(&expr), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_count_expr_nodes_and() {
    use tla_core::span::Span;
    let left = Spanned {
        node: Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let right = Spanned {
        node: Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let expr = Expr::And(Box::new(left), Box::new(right));
    assert_eq!(count_expr_nodes(&expr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_count_expr_nodes_nested() {
    use tla_core::span::Span;
    let a = Spanned {
        node: Expr::Ident("a".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let b = Spanned {
        node: Expr::Ident("b".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let c = Spanned {
        node: Expr::Ident("c".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let and_ab = Spanned {
        node: Expr::And(Box::new(a), Box::new(b)),
        span: Span::default(),
    };
    let expr = Expr::And(Box::new(and_ab), Box::new(c));
    assert_eq!(count_expr_nodes(&expr), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_and_single() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    let parts = flatten_and(&expr);
    assert_eq!(parts.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_and_two_conjuncts() {
    use tla_core::span::Span;
    let left = Spanned {
        node: Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let right = Spanned {
        node: Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let expr = Expr::And(Box::new(left), Box::new(right));
    let parts = flatten_and(&expr);
    assert_eq!(parts.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_contains_ident_found() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    assert!(expr_contains_ident(&expr, "x"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_contains_ident_not_found() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    assert!(!expr_contains_ident(&expr, "y"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_contains_ident_nested() {
    use tla_core::span::Span;
    let inner = Spanned {
        node: Expr::Ident("target".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::default(),
    };
    let expr = Expr::Not(Box::new(inner));
    assert!(expr_contains_ident(&expr, "target"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_contains_exists_false() {
    let expr = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
    assert!(!expr_contains_exists(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_contains_exists_true() {
    use tla_core::ast::BoundVar;
    use tla_core::span::Span;
    let bounds = vec![BoundVar {
        name: Spanned {
            node: "n".to_string(),
            span: Span::default(),
        },
        domain: Some(Box::new(Spanned {
            node: Expr::Ident("S".to_string(), tla_core::name_intern::NameId::INVALID),
            span: Span::default(),
        })),
        pattern: None,
    }];
    let body = Box::new(Spanned {
        node: Expr::Bool(true),
        span: Span::default(),
    });
    let expr = Expr::Exists(bounds, body);
    assert!(expr_contains_exists(&expr));
}

// #1629 ScopeRestore tests moved to scope_restore.rs
