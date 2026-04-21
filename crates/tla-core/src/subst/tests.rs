// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::free_vars::bound_names_from_bound_var;
use super::*;
use crate::ast::{BoundPattern, BoundVar, Expr, ModuleTarget, OpParam, OperatorDef};
use crate::name_intern::NameId;
use crate::span::{Span, Spanned};
use std::collections::HashSet;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned {
        node,
        span: Span::default(),
    }
}

fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string(), NameId::INVALID)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_free_vars_simple_ident() {
    let expr = ident("x");
    let free = free_vars(&expr);
    assert!(free.contains("x"));
    assert_eq!(free.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_free_vars_bound_in_forall() {
    // \A x \in S : x = y
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let body = Expr::Eq(Box::new(spanned(ident("x"))), Box::new(spanned(ident("y"))));
    let expr = Expr::Forall(vec![bound_var], Box::new(spanned(body)));

    let free = free_vars(&expr);
    assert!(free.contains("S"), "S should be free (in domain)");
    assert!(free.contains("y"), "y should be free");
    assert!(!free.contains("x"), "x should be bound");
    assert_eq!(free.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitution_would_capture_simple() {
    // Expression: \A x \in S : x + y
    // Substituting y |-> x would cause capture (x would become bound)
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let body = Expr::Add(Box::new(spanned(ident("x"))), Box::new(spanned(ident("y"))));
    let expr = Expr::Forall(vec![bound_var], Box::new(spanned(body)));

    let mut arg_free = HashSet::new();
    arg_free.insert("x".to_string()); // Substituting y |-> x

    let mut bound = BoundNameStack::new();
    let would_capture = substitution_would_capture(&expr, "y", &arg_free, &mut bound);
    assert!(would_capture, "Substituting y |-> x should cause capture");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substitution_safe_no_overlap() {
    // Expression: \A x \in S : x + y
    // Substituting y |-> z is safe (z is not bound by \A x)
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let body = Expr::Add(Box::new(spanned(ident("x"))), Box::new(spanned(ident("y"))));
    let expr = Expr::Forall(vec![bound_var], Box::new(spanned(body)));

    let mut arg_free = HashSet::new();
    arg_free.insert("z".to_string()); // Substituting y |-> z

    let mut bound = BoundNameStack::new();
    let would_capture = substitution_would_capture(&expr, "y", &arg_free, &mut bound);
    assert!(!would_capture, "Substituting y |-> z should be safe");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bound_name_stack_mark_pop() {
    let mut stack = BoundNameStack::new();
    stack.push("a".to_string());
    let mark = stack.mark();
    stack.push("b".to_string());
    stack.push("c".to_string());

    assert!(stack.contains("a"));
    assert!(stack.contains("b"));
    assert!(stack.contains("c"));

    stack.pop_to(mark);

    assert!(stack.contains("a"));
    assert!(!stack.contains("b"));
    assert!(!stack.contains("c"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bound_names_with_pattern() {
    // x = <<a, b>> \in S
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: Some(BoundPattern::Tuple(vec![
            spanned("a".to_string()),
            spanned("b".to_string()),
        ])),
    };

    let names = bound_names_from_bound_var(&bound_var);
    assert_eq!(names, vec!["x", "a", "b"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inlining_is_capture_safe_unsafe_case() {
    // Operator: f(y) == \A x \in S : x + y
    // Inlining f(x) would substitute y |-> x, causing capture
    let span = Span::default();
    let param = OpParam {
        name: spanned("y".to_string()),
        arity: 0,
    };
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let body = Expr::Forall(
        vec![bound_var],
        Box::new(spanned(Expr::Add(
            Box::new(spanned(ident("x"))),
            Box::new(spanned(ident("y"))),
        ))),
    );
    let def = OperatorDef {
        name: spanned("f".to_string()),
        params: vec![param],
        body: Spanned { node: body, span },
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    // Arg is just "x" which is free
    let args = vec![spanned(ident("x"))];

    assert!(
        !inlining_is_capture_safe(&def, &args),
        "Inlining f(x) should be unsafe (y |-> x causes capture)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inlining_is_capture_safe_safe_case() {
    // Operator: f(y) == \A x \in S : x + y
    // Inlining f(z) substitutes y |-> z, which is safe
    let span = Span::default();
    let param = OpParam {
        name: spanned("y".to_string()),
        arity: 0,
    };
    let bound_var = BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let body = Expr::Forall(
        vec![bound_var],
        Box::new(spanned(Expr::Add(
            Box::new(spanned(ident("x"))),
            Box::new(spanned(ident("y"))),
        ))),
    );
    let def = OperatorDef {
        name: spanned("f".to_string()),
        params: vec![param],
        body: Spanned { node: body, span },
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    // Arg is "z" which doesn't conflict with "x"
    let args = vec![spanned(ident("z"))];

    assert!(
        inlining_is_capture_safe(&def, &args),
        "Inlining f(z) should be safe (y |-> z has no capture)"
    );
}

// ================================================================
// ModuleTarget traversal tests (#1235)
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_free_vars_module_ref_parameterized() {
    // IS(x)!Op(y) - both x (in Parameterized params) and y (in args) are free
    let expr = Expr::ModuleRef(
        ModuleTarget::Parameterized("IS".to_string(), vec![spanned(ident("x"))]),
        "Op".to_string(),
        vec![spanned(ident("y"))],
    );
    let free = free_vars(&expr);
    assert!(
        free.contains("x"),
        "x in Parameterized params should be free"
    );
    assert!(free.contains("y"), "y in args should be free");
    assert_eq!(free.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_free_vars_module_ref_chained() {
    // (A!B)!Op(y) - vars in the chained base and in args are free
    let base = Expr::ModuleRef(
        ModuleTarget::Named("A".to_string()),
        "B".to_string(),
        vec![spanned(ident("x"))],
    );
    let expr = Expr::ModuleRef(
        ModuleTarget::Chained(Box::new(spanned(base))),
        "Op".to_string(),
        vec![spanned(ident("y"))],
    );
    let free = free_vars(&expr);
    assert!(free.contains("x"), "x in chained base args should be free");
    assert!(free.contains("y"), "y in outer args should be free");
    assert_eq!(free.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_free_vars_module_ref_named_no_extra_vars() {
    // M!Op(y) - Named target has no sub-expressions, only args contribute
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("M".to_string()),
        "Op".to_string(),
        vec![spanned(ident("y"))],
    );
    let free = free_vars(&expr);
    assert!(free.contains("y"));
    assert_eq!(free.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capture_check_module_ref_parameterized() {
    // IS(y)!Op inside \A y : ... - substituting z |-> y in IS(z)!Op
    // would be captured if y is bound
    let inner = Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![spanned(ident("z"))], // z appears in params
        ),
        "Op".to_string(),
        vec![],
    );
    // Wrap in \A y : IS(z)!Op
    let bound_var = BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let expr = Expr::Forall(vec![bound_var], Box::new(spanned(inner)));

    let mut arg_free = HashSet::new();
    arg_free.insert("y".to_string()); // Substituting z |-> y

    let mut bound = BoundNameStack::new();
    let would_capture = substitution_would_capture(&expr, "z", &arg_free, &mut bound);
    assert!(
        would_capture,
        "Substituting z |-> y in Parameterized params should detect capture"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capture_check_module_ref_chained() {
    // (A!B(z))!Op inside \A y : ... - substituting z |-> y would be captured
    let base = Expr::ModuleRef(
        ModuleTarget::Named("A".to_string()),
        "B".to_string(),
        vec![spanned(ident("z"))], // z in chained base args
    );
    let inner = Expr::ModuleRef(
        ModuleTarget::Chained(Box::new(spanned(base))),
        "Op".to_string(),
        vec![],
    );
    let bound_var = BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(ident("S")))),
        pattern: None,
    };
    let expr = Expr::Forall(vec![bound_var], Box::new(spanned(inner)));

    let mut arg_free = HashSet::new();
    arg_free.insert("y".to_string()); // Substituting z |-> y

    let mut bound = BoundNameStack::new();
    let would_capture = substitution_would_capture(&expr, "z", &arg_free, &mut bound);
    assert!(
        would_capture,
        "Substituting z |-> y in Chained base should detect capture"
    );
}
