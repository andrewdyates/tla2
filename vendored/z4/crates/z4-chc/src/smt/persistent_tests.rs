// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn int_array_var(name: &str) -> ChcVar {
    ChcVar::new(
        name,
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    )
}

fn select_eq(var: &ChcVar, idx: i64, value: i64) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(var.clone()), ChcExpr::Int(idx)),
        ChcExpr::Int(value),
    )
}

#[test]
fn test_persistent_executor_context_reuses_background_across_queries() {
    let a = int_array_var("A");
    let background = select_eq(&a, 0, 42);
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();

    assert!(ctx.ensure_background(&background, Duration::from_secs(5)));

    let first = ctx.check_query(&ChcExpr::Bool(true), &propagated, Duration::from_secs(5));
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected SAT for background-only query, got {first:?}"
    );

    let second = ctx.check_query(
        &ChcExpr::not(select_eq(&a, 0, 42)),
        &propagated,
        Duration::from_secs(5),
    );
    assert!(
        matches!(second, SmtResult::Unsat),
        "expected UNSAT when query contradicts persistent background, got {second:?}"
    );
}

#[test]
fn test_persistent_executor_context_rebuilds_when_background_changes() {
    let a = int_array_var("A");
    let background_one = select_eq(&a, 0, 1);
    let background_two = select_eq(&a, 0, 2);
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();

    assert!(ctx.ensure_background(&background_one, Duration::from_secs(5)));
    let first = ctx.check_query(&ChcExpr::Bool(true), &propagated, Duration::from_secs(5));
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected SAT for first background, got {first:?}"
    );

    assert!(ctx.ensure_background(&background_two, Duration::from_secs(5)));
    let second = ctx.check_query(&select_eq(&a, 0, 1), &propagated, Duration::from_secs(5));
    assert!(
        matches!(second, SmtResult::Unsat),
        "expected UNSAT after background rebuild, got {second:?}"
    );
}
