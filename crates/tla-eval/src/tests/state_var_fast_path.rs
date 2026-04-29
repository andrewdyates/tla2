// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clear_for_test_reset;
use crate::helpers::function_values::try_borrow_materialized_read;
use crate::value::IntIntervalFunc;
use std::sync::Arc;
use tla_core::ast::{Expr, RecordFieldName, Substitution};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::{Span, Spanned};

fn state_var_expr(name: &str, idx: u16) -> Spanned<Expr> {
    Spanned::dummy(Expr::StateVar(name.to_string(), idx, intern_name(name)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_plain_state_array_fast_path_reads_state_and_tracks_dep() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(10)];
    ctx.bind_state_array(&state);

    let expr = state_var_expr("x", 0);
    let (value, deps) =
        eval_with_dep_tracking(&ctx, &expr).expect("plain StateVar should resolve state slot");
    assert_eq!(value, Value::int(10));
    assert!(
        !deps.state.is_empty(),
        "plain StateVar fast path must still record state-read dependencies"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_local_binding_bypasses_direct_array_fast_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(10)];
    ctx.bind_state_array(&state);

    let ctx_with_local = ctx.bind("x", Value::int(99));
    let expr = state_var_expr("x", 0);
    let (value, deps) =
        eval_with_dep_tracking(&ctx_with_local, &expr).expect("local binding should shadow x");
    assert_eq!(value, Value::int(99));
    assert!(
        deps.state.is_empty(),
        "non-liveness binding must keep StateVar off the direct state-array fast path"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_call_by_name_substitution_bypasses_direct_array_fast_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(10), Value::int(20)];
    ctx.bind_state_array(&state);

    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Ident("y".to_string(), NameId::INVALID), Span::dummy()),
    }]);

    let expr = state_var_expr("x", 0);
    let value = eval(&ctx_with_cbn, &expr).expect("call-by-name substitution should win");
    assert_eq!(value, Value::int(20));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_instance_substitution_bypasses_direct_array_fast_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(10), Value::int(20)];
    ctx.bind_state_array(&state);

    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Ident("y".to_string(), NameId::INVALID), Span::dummy()),
    }]);

    let expr = state_var_expr("x", 0);
    let value = eval(&ctx_with_subs, &expr).expect("INSTANCE substitution should win");
    assert_eq!(value, Value::int(20));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_eager_subst_binding_bypasses_direct_array_fast_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(10)];
    ctx.bind_state_array(&state);
    ctx.stable_mut().eager_subst_bindings = Some(Arc::new(vec![(
        intern_name("x"),
        Value::int(99),
        OpEvalDeps::default(),
    )]));

    let expr = state_var_expr("x", 0);
    let value = eval(&ctx, &expr).expect("eager substitution binding should shadow x");
    assert_eq!(value, Value::int(99));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_env_fallback_still_works_without_state_env() {
    clear_for_test_reset();

    let mut env = crate::HashMap::default();
    env.insert(Arc::from("x"), Value::int(7));

    let mut ctx = EvalCtx::with_env(env);
    ctx.register_var("x");

    let expr = state_var_expr("x", 0);
    let (value, deps) =
        eval_with_dep_tracking(&ctx, &expr).expect("env fallback should resolve StateVar");
    assert_eq!(value, Value::int(7));
    assert!(
        !deps.state.is_empty(),
        "env fallback must keep StateVar state-read dependency tracking"
    );

    clear_for_test_reset();
}

// --- StateVar -> apply fast path tests (exercises try_borrow_materialized_state_var) ---

fn func_apply_expr(func: Spanned<Expr>, arg: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::FuncApply(Box::new(func), Box::new(arg)))
}

fn int_literal_expr(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(num_bigint::BigInt::from(n)))
}

fn record_access_expr(record: Spanned<Expr>, field: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::RecordAccess(
        Box::new(record),
        RecordFieldName::new(Spanned::dummy(field.to_string())),
    ))
}

/// Part of #3168: plain function-valued state variable uses direct borrowed
/// slot via `try_borrow_materialized_state_var` and still records state-read deps.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_apply_plain_uses_direct_borrowed_slot() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("f");
    // f is an IntIntervalFunc: f[1] = 10, f[2] = 20
    let func_val = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));
    let state = vec![func_val];
    ctx.bind_state_array(&state);

    // Evaluate f[1] — this hits eval_func_apply → try_borrow_materialized_state_var
    let expr = func_apply_expr(state_var_expr("f", 0), int_literal_expr(1));
    let (value, deps) = eval_with_dep_tracking(&ctx, &expr)
        .expect("StateVar -> apply should resolve through borrowed slot");
    assert_eq!(value, Value::int(10));
    assert!(
        !deps.state.is_empty(),
        "StateVar -> apply fast path must still record state-read dependencies"
    );

    clear_for_test_reset();
}

/// Part of #3168: local binding shadows the state slot and forces fallback
/// to the owned eval path in eval_func_apply.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_apply_local_binding_shadows_state_slot() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("f");
    // f in state: f[1] = 10
    let func_val = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 1, vec![Value::int(10)])));
    let state = vec![func_val];
    ctx.bind_state_array(&state);

    // Shadow f with a different function: f[1] = 99
    let shadow = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 1, vec![Value::int(99)])));
    let ctx_with_local = ctx.bind("f", shadow);

    let expr = func_apply_expr(state_var_expr("f", 0), int_literal_expr(1));
    let value = eval(&ctx_with_local, &expr).expect("local binding should shadow state var");
    assert_eq!(value, Value::int(99));

    clear_for_test_reset();
}

/// Part of #3168: NotInDomain error is preserved correctly through the
/// borrowed fast path when the argument is out of domain.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_apply_not_in_domain_through_borrowed_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("f");
    // f is an IntIntervalFunc with domain 1..2
    let func_val = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));
    let state = vec![func_val];
    ctx.bind_state_array(&state);

    // Evaluate f[99] — argument out of domain
    let expr = func_apply_expr(state_var_expr("f", 0), int_literal_expr(99));
    let err = eval(&ctx, &expr).expect_err("f[99] should fail with NotInDomain");
    assert!(
        matches!(err, EvalError::NotInDomain { .. }),
        "expected NotInDomain error, got: {err:?}"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialized_read_nested_record_access_borrows_state_leaf() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("r");
    let state = vec![Value::Record(
        vec![(
            "outer".to_string(),
            Value::Record(vec![("leaf".to_string(), Value::int(42))].into()),
        )]
        .into(),
    )];
    ctx.bind_state_array(&state);

    let expr = record_access_expr(record_access_expr(state_var_expr("r", 0), "outer"), "leaf");
    let borrowed = try_borrow_materialized_read(&ctx, &expr)
        .expect("nested record access should stay on the materialized-read path")
        .expect("nested record access should resolve successfully");

    let outer = state[0]
        .as_record()
        .expect("state entry should be a record")
        .get_by_id(intern_name("outer"))
        .expect("outer field should exist");
    let expected = outer
        .as_record()
        .expect("outer field should be a record")
        .get_by_id(intern_name("leaf"))
        .expect("leaf field should exist");
    assert_eq!(
        &borrowed, expected,
        "nested record access should return the leaf from the state record"
    );
    assert_eq!(
        eval(&ctx, &expr).expect("nested record access should evaluate"),
        Value::int(42)
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialized_read_record_access_apply_borrows_function_result() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("r");
    let func = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));
    let state = vec![Value::Record(vec![("lookup".to_string(), func)].into())];
    ctx.bind_state_array(&state);

    let expr = func_apply_expr(
        record_access_expr(state_var_expr("r", 0), "lookup"),
        int_literal_expr(2),
    );
    let borrowed = try_borrow_materialized_read(&ctx, &expr)
        .expect("record access -> apply should stay on the materialized-read path")
        .expect("record access -> apply should resolve successfully");

    let lookup = state[0]
        .as_record()
        .expect("state entry should be a record")
        .get_by_id(intern_name("lookup"))
        .expect("lookup field should exist");
    let expected = match lookup {
        Value::IntFunc(func) => func
            .apply(&Value::int(2))
            .expect("function domain should contain the requested key"),
        other => panic!("expected IntFunc in lookup field, got {other:?}"),
    };
    assert_eq!(
        &borrowed, expected,
        "record access -> apply should return the function result"
    );
    assert_eq!(
        eval(&ctx, &expr).expect("record access -> apply should evaluate"),
        Value::int(20)
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialized_read_apply_record_access_borrows_record_field() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("f");
    let state = vec![Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        1,
        vec![Value::Record(
            vec![("leaf".to_string(), Value::int(7))].into(),
        )],
    )))];
    ctx.bind_state_array(&state);

    let expr = record_access_expr(
        func_apply_expr(state_var_expr("f", 0), int_literal_expr(1)),
        "leaf",
    );
    let borrowed = try_borrow_materialized_read(&ctx, &expr)
        .expect("apply -> record access should stay on the materialized-read path")
        .expect("apply -> record access should resolve successfully");

    let expected = match &state[0] {
        Value::IntFunc(func) => func
            .apply(&Value::int(1))
            .expect("function domain should contain the requested key")
            .as_record()
            .expect("function result should be a record")
            .get_by_id(intern_name("leaf"))
            .expect("leaf field should exist"),
        other => panic!("expected IntFunc state var, got {other:?}"),
    };
    assert_eq!(
        &borrowed, expected,
        "apply -> record access should return the record field"
    );
    assert_eq!(
        eval(&ctx, &expr).expect("apply -> record access should evaluate"),
        Value::int(7)
    );

    clear_for_test_reset();
}
