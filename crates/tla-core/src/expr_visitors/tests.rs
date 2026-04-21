// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

use std::sync::Arc;

use super::*;
use crate::ast::{BoundVar, Expr};
use crate::name_intern::NameId;
use crate::Spanned;

/// Helper: wrap an Expr in a dummy span.
fn s(e: Expr) -> Spanned<Expr> {
    Spanned::dummy(e)
}

/// Helper: construct `\A x \in S : body`.
fn forall_in(var_name: &str, domain: Expr, body: Expr) -> Expr {
    Expr::Forall(
        vec![BoundVar {
            name: Spanned::dummy(var_name.to_string()),
            domain: Some(Box::new(s(domain))),
            pattern: None,
        }],
        Box::new(s(body)),
    )
}

/// Helper: construct Apply(op_ident, args).
fn apply(op: &str, args: Vec<Expr>) -> Expr {
    Expr::Apply(
        Box::new(s(Expr::Ident(op.to_string(), NameId::INVALID))),
        args.into_iter().map(s).collect(),
    )
}

// ---- ContainsOperatorApplication tests ----

#[test]
fn test_apply_at_top_level() {
    // Apply(Op, [x]) should be detected
    let expr = apply("Op", vec![Expr::Ident("x".into(), NameId::INVALID)]);
    assert!(expr_contains_operator_application_v(&expr));
}

#[test]
fn test_no_apply() {
    // Simple ident has no operator application
    let expr = Expr::Ident("x".into(), NameId::INVALID);
    assert!(!expr_contains_operator_application_v(&expr));
}

#[test]
fn test_apply_inside_forall() {
    // \A x \in S : Op(x) — the bug: Apply inside Forall was undetected
    let expr = forall_in(
        "x",
        Expr::Ident("S".into(), NameId::INVALID),
        apply("Op", vec![Expr::Ident("x".into(), NameId::INVALID)]),
    );
    assert!(expr_contains_operator_application_v(&expr));
}

#[test]
fn test_apply_inside_exists() {
    // \E x \in S : Op(x)
    let expr = Expr::Exists(
        vec![BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(s(Expr::Ident("S".into(), NameId::INVALID)))),
            pattern: None,
        }],
        Box::new(s(apply(
            "Op",
            vec![Expr::Ident("x".into(), NameId::INVALID)],
        ))),
    );
    assert!(expr_contains_operator_application_v(&expr));
}

#[test]
fn test_apply_inside_choose() {
    // CHOOSE x \in S : Op(x)
    let expr = Expr::Choose(
        BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(s(Expr::Ident("S".into(), NameId::INVALID)))),
            pattern: None,
        },
        Box::new(s(apply(
            "Op",
            vec![Expr::Ident("x".into(), NameId::INVALID)],
        ))),
    );
    assert!(expr_contains_operator_application_v(&expr));
}

#[test]
fn test_apply_inside_set_builder() {
    // {Op(x) : x \in S}
    let expr = Expr::SetBuilder(
        Box::new(s(apply(
            "Op",
            vec![Expr::Ident("x".into(), NameId::INVALID)],
        ))),
        vec![BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(s(Expr::Ident("S".into(), NameId::INVALID)))),
            pattern: None,
        }],
    );
    assert!(expr_contains_operator_application_v(&expr));
}

#[test]
fn test_no_apply_inside_forall() {
    // \A x \in S : x = 1 — no Apply present
    let expr = forall_in(
        "x",
        Expr::Ident("S".into(), NameId::INVALID),
        Expr::Eq(
            Box::new(s(Expr::Ident("x".into(), NameId::INVALID))),
            Box::new(s(Expr::Int(1.into()))),
        ),
    );
    assert!(!expr_contains_operator_application_v(&expr));
}

#[test]
fn test_apply_inside_always() {
    // []Op(x) — temporal wrapper around Apply
    let expr = Expr::Always(Box::new(s(apply(
        "Op",
        vec![Expr::Ident("x".into(), NameId::INVALID)],
    ))));
    assert!(expr_contains_operator_application_v(&expr));
}

// ---- ReferencesAnyFreeName tests (Part of #3128) ----

use crate::ast::{BoundPattern, OperatorDef};

fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string(), NameId::INVALID)
}

fn name_set<'a>(names: &'a [&'a str]) -> std::collections::HashSet<&'a str> {
    names.iter().copied().collect()
}

#[test]
fn test_free_name_simple_hit() {
    // `x` references {"x"} as free
    let expr = ident("x");
    assert!(expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_simple_miss() {
    // `y` does not reference {"x"}
    let expr = ident("y");
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_empty_set() {
    // Empty name set always returns false
    let expr = ident("x");
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&[])));
}

#[test]
fn test_free_name_shadowed_by_forall() {
    // \A x \in S : x — "x" is shadowed by \A, not free
    let expr = forall_in("x", ident("S"), ident("x"));
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_in_forall_domain() {
    // \A y \in x : y — "x" appears free in the domain
    let expr = forall_in("y", ident("x"), ident("y"));
    assert!(expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_not_shadowed_different_var() {
    // \A y \in S : x — "x" is NOT shadowed by \A y, so it's free
    let expr = forall_in("y", ident("S"), ident("x"));
    assert!(expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_shadowed_by_choose() {
    // CHOOSE x \in S : x > 0 — "x" in body is shadowed
    let expr = Expr::Choose(
        BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(s(ident("S")))),
            pattern: None,
        },
        Box::new(s(ident("x"))),
    );
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_shadowed_by_let() {
    // LET x == 1 IN x — "x" in body is shadowed by LET def name
    let expr = Expr::Let(
        vec![OperatorDef {
            name: Spanned::dummy("x".to_string()),
            params: vec![],
            body: s(Expr::Int(1.into())),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        Box::new(s(ident("x"))),
    );
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_in_let_def_body() {
    // LET y == x IN y — "x" is free in the def body
    let expr = Expr::Let(
        vec![OperatorDef {
            name: Spanned::dummy("y".to_string()),
            params: vec![],
            body: s(ident("x")),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        Box::new(s(ident("y"))),
    );
    assert!(expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_shadowed_by_lambda() {
    // LAMBDA x : x — "x" is shadowed by lambda param
    let expr = Expr::Lambda(
        vec![Spanned::dummy("x".to_string())],
        Box::new(s(ident("x"))),
    );
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["x"])));
}

#[test]
fn test_free_name_tuple_pattern_shadow() {
    // \A <<a, b>> \in S : a — "a" is shadowed by tuple pattern
    let expr = Expr::Forall(
        vec![BoundVar {
            name: Spanned::dummy("__tuple".to_string()),
            domain: Some(Box::new(s(ident("S")))),
            pattern: Some(BoundPattern::Tuple(vec![
                Spanned::dummy("a".to_string()),
                Spanned::dummy("b".to_string()),
            ])),
        }],
        Box::new(s(ident("a"))),
    );
    assert!(!expr_references_any_free_name_v(&expr, &name_set(&["a"])));
}

#[test]
fn test_free_name_nested_quantifier_inner_shadows() {
    // \A y \in S : \A x \in T : x — inner \A shadows "x"
    let inner = forall_in("x", ident("T"), ident("x"));
    let outer = forall_in("y", ident("S"), inner);
    assert!(!expr_references_any_free_name_v(&outer, &name_set(&["x"])));
}

#[test]
fn test_free_name_nested_quantifier_outer_not_shadowed() {
    // \A y \in S : \A z \in T : x — neither quantifier shadows "x"
    let inner = forall_in("z", ident("T"), ident("x"));
    let outer = forall_in("y", ident("S"), inner);
    assert!(expr_references_any_free_name_v(&outer, &name_set(&["x"])));
}

#[test]
fn test_references_state_vars_statevar_hit() {
    let expr = Expr::StateVar("x".to_string(), 0, NameId::INVALID);
    let vars = vec![Arc::<str>::from("x")];
    assert!(expr_references_state_vars_v(&expr, &vars));
}

#[test]
fn test_references_state_vars_statevar_miss() {
    let expr = Expr::StateVar("y".to_string(), 0, NameId::INVALID);
    let vars = vec![Arc::<str>::from("x")];
    assert!(!expr_references_state_vars_v(&expr, &vars));
}
