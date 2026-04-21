// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression and specialized fold tests: SubstituteAt, #2452 SetFilter/LET
//! interaction, tuple pattern free variable handling, and #2996 StateVar
//! substitution.

use super::*;
use crate::name_intern::intern_name;

// --- SubstituteAt tests ---

#[test]
fn test_substitute_at_replaces_only_at_identifiers() {
    let expr = spanned(Expr::Add(
        boxed_expr(Expr::Ident("@".to_string(), NameId::INVALID)),
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let replacement = spanned(Expr::Int(BigInt::from(7)));
    let mut sub = SubstituteAt {
        replacement: &replacement,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Add(left, right)
            if matches!(&left.node, Expr::Int(n) if n == &BigInt::from(7))
                && matches!(&right.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));
}

#[test]
fn test_substitute_at_respects_nested_except_scopes() {
    let expr = spanned(Expr::Except(
        boxed_expr(Expr::Ident("@".to_string(), NameId::INVALID)),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(spanned(Expr::Add(
                boxed_expr(Expr::Ident("@".to_string(), NameId::INVALID)),
                boxed_expr(Expr::Int(BigInt::from(1))),
            )))],
            value: spanned(Expr::Except(
                boxed_expr(Expr::Ident("@".to_string(), NameId::INVALID)),
                vec![ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Sub(
                        boxed_expr(Expr::Ident("@".to_string(), NameId::INVALID)),
                        boxed_expr(Expr::Int(BigInt::from(1))),
                    )))],
                    value: spanned(Expr::Ident("@".to_string(), NameId::INVALID)),
                }],
            )),
        }],
    ));
    let replacement = spanned(Expr::Ident("participant_i".to_string(), NameId::INVALID));
    let mut sub = SubstituteAt {
        replacement: &replacement,
    };

    let out = sub.fold_expr(expr);
    let Expr::Except(base, specs) = &out.node else {
        panic!("expected outer EXCEPT");
    };
    assert!(matches!(
        &base.node,
        Expr::Ident(name, NameId::INVALID) if name == "participant_i"
    ));

    let [outer_spec] = specs.as_slice() else {
        panic!("expected one outer EXCEPT spec");
    };
    let ExceptPathElement::Index(outer_idx) = &outer_spec.path[0] else {
        panic!("expected outer EXCEPT index path");
    };
    assert!(matches!(
        &outer_idx.node,
        Expr::Add(left, right)
            if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "participant_i")
                && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(1))
    ));

    let Expr::Except(inner_base, inner_specs) = &outer_spec.value.node else {
        panic!("expected nested EXCEPT in outer value");
    };
    assert!(matches!(
        &inner_base.node,
        Expr::Ident(name, NameId::INVALID) if name == "@"
    ));

    let [inner_spec] = inner_specs.as_slice() else {
        panic!("expected one inner EXCEPT spec");
    };
    let ExceptPathElement::Index(inner_idx) = &inner_spec.path[0] else {
        panic!("expected inner EXCEPT index path");
    };
    assert!(matches!(
        &inner_idx.node,
        Expr::Sub(left, right)
            if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "@")
                && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(1))
    ));
    assert!(matches!(
        &inner_spec.value.node,
        Expr::Ident(name, NameId::INVALID) if name == "@"
    ));
}

// --- Regression: #2452 — SetFilter replacement must not block unrelated LET substitution ---

#[test]
fn test_substitute_expr_set_filter_replacement_allowed_in_let_body_2452() {
    // LET perms == 5 IN f(S) with subs {S -> {c \in D : c > 0}}
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("perms".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::FuncApply(
            boxed_expr(Expr::Ident("perms".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID)),
        )),
    ));
    let repl = spanned(Expr::SetFilter(
        BoundVar {
            name: spanned("c".to_string()),
            domain: Some(boxed_expr(Expr::Ident("D".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Gt(
            boxed_expr(Expr::Ident("c".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Int(BigInt::from(0))),
        )),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("S", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    if let Expr::Let(_, body) = &out.node {
        if let Expr::FuncApply(_, arg) = &body.node {
            assert!(
                matches!(&arg.node, Expr::SetFilter(..)),
                "S should be replaced with SetFilter, got: {:?}",
                arg.node
            );
        } else {
            panic!("Expected FuncApply in LET body, got: {:?}", body.node);
        }
    } else {
        panic!("Expected Let, got: {:?}", out.node);
    }
}

#[test]
fn test_substitute_expr_exists_replacement_allowed_in_let_body_2452() {
    // LET f == 5 IN g(S) with subs {S -> \E x \in D : x > 0}
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("f".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Apply(
            boxed_expr(Expr::Ident("g".to_string(), NameId::INVALID)),
            vec![spanned(Expr::Ident("S".to_string(), NameId::INVALID))],
        )),
    ));
    let repl = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("D".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Gt(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Int(BigInt::from(0))),
        )),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("S", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    if let Expr::Let(_, body) = &out.node {
        if let Expr::Apply(_, args) = &body.node {
            assert!(
                matches!(&args[0].node, Expr::Exists(..)),
                "S should be replaced with Exists, got: {:?}",
                args[0].node
            );
        } else {
            panic!("Expected Apply in LET body, got: {:?}", body.node);
        }
    } else {
        panic!("Expected Let, got: {:?}", out.node);
    }
}

#[test]
fn test_substitute_expr_set_filter_replacement_blocked_when_captures_let_name() {
    // LET perms == 5 IN f(S) with subs {S -> g(perms)}
    // "perms" is free in replacement and would be captured.
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("perms".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID)),
    ));
    let repl = spanned(Expr::Apply(
        boxed_expr(Expr::Ident("g".to_string(), NameId::INVALID)),
        vec![spanned(Expr::Ident("perms".to_string(), NameId::INVALID))],
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("S", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    if let Expr::Let(_, body) = &out.node {
        assert!(
            matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "S"),
            "S should remain as Ident('S') due to capture avoidance, got: {:?}",
            body.node
        );
    } else {
        panic!("Expected Let, got: {:?}", out.node);
    }
}

// --- Tuple pattern free variable handling ---

#[test]
fn test_substitute_expr_tuple_pattern_vars_excluded_from_free_var_check() {
    // LET x == 5 IN f(S) with subs {S -> \E <<x, y>> \in D : x > 0}
    // The replacement's "x" is bound by the tuple pattern, NOT free.
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("x".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID)),
    ));
    let repl = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("__tuple".to_string()),
            domain: Some(boxed_expr(Expr::Ident("D".to_string(), NameId::INVALID))),
            pattern: Some(BoundPattern::Tuple(vec![
                spanned("x".to_string()),
                spanned("y".to_string()),
            ])),
        }],
        boxed_expr(Expr::Gt(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Int(BigInt::from(0))),
        )),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("S", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    if let Expr::Let(_, body) = &out.node {
        assert!(
            matches!(&body.node, Expr::Exists(..)),
            "S should be replaced with Exists (pattern-bound x is not free), got: {:?}",
            body.node
        );
    } else {
        panic!("Expected Let, got: {:?}", out.node);
    }
}

// --- Part of #2996: SubstituteExpr must handle StateVar nodes ---

#[test]
fn test_substitute_expr_state_var_matched_by_name() {
    let pc_name_id = intern_name("pc");
    let expr = spanned(Expr::StateVar("pc".to_string(), 0, pc_name_id));
    let replacement = spanned(Expr::Int(BigInt::from(42)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("pc", &replacement)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert_eq!(
        out.node,
        Expr::Int(BigInt::from(42)),
        "StateVar('pc') should be substituted to Int(42)"
    );
}

#[test]
fn test_substitute_expr_state_var_unmatched_passes_through() {
    let pc_name_id = intern_name("pc");
    let expr = spanned(Expr::StateVar("pc".to_string(), 0, pc_name_id));
    let replacement = spanned(Expr::Int(BigInt::from(42)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("other", &replacement)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(
        matches!(&out.node, Expr::StateVar(name, 0, _) if name == "pc"),
        "StateVar('pc') should pass through when sub target is 'other', got: {:?}",
        out.node
    );
}

#[test]
fn test_substitute_expr_state_var_nested_in_expression() {
    let pc_name_id = intern_name("pc");
    let expr = spanned(Expr::And(
        boxed_expr(Expr::StateVar("pc".to_string(), 0, pc_name_id)),
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let repl_pc = spanned(Expr::Int(BigInt::from(1)));
    let repl_x = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("pc", &repl_pc), ("x", &repl_x)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(
        matches!(
            &out.node,
            Expr::And(left, right)
                if matches!(&left.node, Expr::Int(n) if n == &BigInt::from(1))
                    && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
        ),
        "Both StateVar('pc') and Ident('x') should be substituted, got: {:?}",
        out.node
    );
}

#[test]
fn test_substitute_expr_state_var_in_quantifier_domain_shadowed_in_body() {
    let pc_name_id = intern_name("pc");
    let expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("pc".to_string()),
            domain: Some(boxed_expr(Expr::StateVar("pc".to_string(), 0, pc_name_id))),
            pattern: None,
        }],
        boxed_expr(Expr::Eq(
            boxed_expr(Expr::StateVar("pc".to_string(), 0, pc_name_id)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    ));
    let repl_pc = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("pc", &repl_pc), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Forall(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &body.node,
                Expr::Eq(left, right)
                    if matches!(&left.node, Expr::StateVar(name, 0, _) if name == "pc")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}
