// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::cache::{raw_subst_scope_key, small_caches::SMALL_CACHES};
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::Spanned;

fn raw_subst_scope_handles(expr: &Spanned<Expr>) -> (usize, usize) {
    match &expr.node {
        Expr::SubstIn(subs, body) => (
            subs as *const Vec<_> as usize,
            std::ptr::addr_of!(**body) as usize,
        ),
        _ => panic!("expected Expr::SubstIn"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_raw_subst_scope_cache_reuses_arc_for_same_scope() {
    clear_for_test_reset();

    let expr = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Int(42.into())),
        }],
        Box::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            intern_name("x"),
        ))),
    ));
    let ctx = EvalCtx::new();
    let (subs_ptr, body_ptr) = raw_subst_scope_handles(&expr);
    let scope_key = raw_subst_scope_key(&ctx, subs_ptr, body_ptr);

    let first = eval(&ctx, &expr).expect("first raw SubstIn eval should succeed");
    assert_eq!(first, Value::int(42));

    let (first_arc, first_scope_id) = SMALL_CACHES
        .with(|sc| sc.borrow().raw_subst_scope_cache.get(&scope_key).cloned())
        .expect("first eval should populate RAW_SUBST_SCOPE_CACHE");

    let second = eval(&ctx, &expr).expect("second raw SubstIn eval should succeed");
    assert_eq!(second, Value::int(42));

    let (second_arc, second_scope_id) = SMALL_CACHES
        .with(|sc| sc.borrow().raw_subst_scope_cache.get(&scope_key).cloned())
        .expect("second eval should reuse RAW_SUBST_SCOPE_CACHE");

    assert_eq!(
        Arc::as_ptr(&first_arc),
        Arc::as_ptr(&second_arc),
        "repeated raw SubstIn evals in the same scope must reuse the cached Arc"
    );
    assert_eq!(
        first_scope_id, second_scope_id,
        "cached scope_id must be stable across evaluations"
    );
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().raw_subst_scope_cache.len()),
        1,
        "same-scope raw SubstIn evals should populate one cache entry"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_raw_subst_scope_cache_discriminates_outer_instance_scope() {
    clear_for_test_reset();

    let expr = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Int(42.into())),
        }],
        Box::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            intern_name("x"),
        ))),
    ));
    let base_ctx = EvalCtx::new();
    let ctx_a = base_ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("outer".to_string()),
        to: Spanned::dummy(Expr::Int(1.into())),
    }]);
    let ctx_b = base_ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("outer".to_string()),
        to: Spanned::dummy(Expr::Int(2.into())),
    }]);

    let (subs_ptr, body_ptr) = raw_subst_scope_handles(&expr);
    let key_a = raw_subst_scope_key(&ctx_a, subs_ptr, body_ptr);
    let key_b = raw_subst_scope_key(&ctx_b, subs_ptr, body_ptr);
    assert_ne!(
        key_a.outer_instance_subs_id, key_b.outer_instance_subs_id,
        "distinct outer scopes must produce distinct raw SubstIn scope keys"
    );

    let value_a = eval(&ctx_a, &expr).expect("raw SubstIn eval in outer scope A should succeed");
    let value_b = eval(&ctx_b, &expr).expect("raw SubstIn eval in outer scope B should succeed");
    assert_eq!(value_a, Value::int(42));
    assert_eq!(value_b, Value::int(42));

    let (arc_a, _scope_id_a) = SMALL_CACHES
        .with(|sc| sc.borrow().raw_subst_scope_cache.get(&key_a).cloned())
        .expect("scope A should populate RAW_SUBST_SCOPE_CACHE");
    let (arc_b, _scope_id_b) = SMALL_CACHES
        .with(|sc| sc.borrow().raw_subst_scope_cache.get(&key_b).cloned())
        .expect("scope B should populate RAW_SUBST_SCOPE_CACHE");

    assert_ne!(
        Arc::as_ptr(&arc_a),
        Arc::as_ptr(&arc_b),
        "different outer scopes must not alias the same raw SubstIn Arc"
    );
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().raw_subst_scope_cache.len()),
        2,
        "different outer scopes should occupy separate raw SubstIn cache entries"
    );
}
