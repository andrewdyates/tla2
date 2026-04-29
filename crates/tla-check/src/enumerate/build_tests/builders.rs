// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diff_builder_skips_assigns_equal_to_base_value() {
    let src = r#"
---- MODULE DiffBuildersSameValue ----
VARIABLE x
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let current_array = ArrayState::from_values(vec![Value::int(100)]);

    let assignments = vec![PrimedAssignment::Assign(Arc::from("x"), Value::int(100))];

    let diffs = build_successor_diffs_from_array(&current_array, &vars, &assignments, &registry);
    assert_eq!(
        diffs.len(),
        1,
        "stuttering assign should still produce one successor"
    );
    assert!(
        diffs[0].changes.is_empty(),
        "same-value assign should not bloat the diff"
    );

    let mut diffs_into = Vec::new();
    build_successor_diffs_from_array_into(
        &mut ctx,
        &current_array,
        &vars,
        &assignments,
        &registry,
        &mut diffs_into,
    );
    assert_eq!(
        diffs_into.len(),
        1,
        "streaming diff builder should match batch behavior"
    );
    assert!(
        diffs_into[0].changes.is_empty(),
        "streaming builder should also drop same-value assigns"
    );

    let materialized = diffs[0].materialize(&current_array, &registry);
    assert_eq!(
        materialized.get(x_idx),
        Value::int(100),
        "empty diff must materialize back to the base value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symbolic_unchanged_uses_current_override_when_building_diffs() {
    let src = r#"
---- MODULE DiffBuildersUnchangedCurrent ----
VARIABLE x
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let current_array = ArrayState::from_values(vec![Value::int(0)]);
    ctx.bind_mut(Arc::from("x"), Value::int(10));

    let symbolic = vec![SymbolicAssignment::Unchanged(Arc::from("x"))];
    let assignments = evaluate_symbolic_assignments(&ctx, &symbolic, None).unwrap();
    assert_eq!(
        assignments.len(),
        1,
        "UNCHANGED should still yield one successor"
    );

    let diffs = build_successor_diffs_from_array(&current_array, &vars, &assignments, &registry);
    assert_eq!(
        diffs.len(),
        1,
        "UNCHANGED override should materialize one diff"
    );
    assert_eq!(
        diffs[0].materialize(&current_array, &registry).get(x_idx),
        Value::int(10),
        "diff builder must use the current override, not the base array value"
    );

    let mut diffs_into = Vec::new();
    build_successor_diffs_from_array_into(
        &mut ctx,
        &current_array,
        &vars,
        &assignments,
        &registry,
        &mut diffs_into,
    );
    assert_eq!(
        diffs_into.len(),
        1,
        "streaming diff builder should match batch override handling"
    );
    assert_eq!(
        diffs_into[0]
            .materialize(&current_array, &registry)
            .get(x_idx),
        Value::int(10),
        "streaming diff builder must preserve the override as well"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diff_builder_and_into_builder_match_materialized_states() {
    let src = r#"
---- MODULE DiffBuilders ----
VARIABLE x, y, z
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let y_idx = registry.get("y").unwrap();
    let z_idx = registry.get("z").unwrap();
    let current_array =
        ArrayState::from_values(vec![Value::int(0), Value::int(10), Value::int(100)]);

    let assignments = vec![
        PrimedAssignment::InSet(Arc::from("x"), vec![Value::int(1), Value::int(2)]),
        PrimedAssignment::Assign(Arc::from("y"), Value::int(7)),
        PrimedAssignment::Unchanged(Arc::from("z")),
    ];

    let diffs = build_successor_diffs_from_array(&current_array, &vars, &assignments, &registry);

    let mut diffs_into = Vec::new();
    build_successor_diffs_from_array_into(
        &mut ctx,
        &current_array,
        &vars,
        &assignments,
        &registry,
        &mut diffs_into,
    );

    for diff in diffs.iter().chain(diffs_into.iter()) {
        assert_eq!(diff.changes.len(), 2);
        assert!(diff.changes.iter().all(|(idx, _)| *idx != z_idx));
    }

    let mut materialized: Vec<(i64, i64, i64)> = diffs
        .iter()
        .map(|diff| {
            let next = diff.materialize(&current_array, &registry);
            (
                next.get(x_idx).as_i64().unwrap(),
                next.get(y_idx).as_i64().unwrap(),
                next.get(z_idx).as_i64().unwrap(),
            )
        })
        .collect();
    materialized.sort_unstable();

    let mut materialized_into: Vec<(i64, i64, i64)> = diffs_into
        .iter()
        .map(|diff| {
            let next = diff.materialize(&current_array, &registry);
            (
                next.get(x_idx).as_i64().unwrap(),
                next.get(y_idx).as_i64().unwrap(),
                next.get(z_idx).as_i64().unwrap(),
            )
        })
        .collect();
    materialized_into.sort_unstable();

    let expected = vec![(1, 7, 100), (2, 7, 100)];
    assert_eq!(materialized, expected);
    assert_eq!(materialized_into, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diff_builder_filtered_applies_predicate_to_next_state() {
    let src = r#"
---- MODULE DiffBuildersFiltered ----
VARIABLE x, y, z
====
"#;
    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let y_idx = registry.get("y").unwrap();
    let z_idx = registry.get("z").unwrap();
    let current_array =
        ArrayState::from_values(vec![Value::int(0), Value::int(10), Value::int(100)]);

    let assignments = vec![
        PrimedAssignment::InSet(
            Arc::from("x"),
            vec![Value::int(1), Value::int(2), Value::int(3)],
        ),
        PrimedAssignment::InSet(Arc::from("y"), vec![Value::int(5), Value::int(6)]),
        PrimedAssignment::Unchanged(Arc::from("z")),
    ];

    let diffs = build_successor_diffs_from_array_filtered(
        &current_array,
        &vars,
        &assignments,
        &registry,
        |next| {
            let x = next.get(x_idx).as_i64().unwrap();
            let y = next.get(y_idx).as_i64().unwrap();
            (x + y) % 2 == 0
        },
    );

    for diff in &diffs {
        assert_eq!(diff.changes.len(), 2);
        assert!(diff.changes.iter().all(|(idx, _)| *idx != z_idx));
    }

    let mut materialized: Vec<(i64, i64, i64)> = diffs
        .iter()
        .map(|diff| {
            let next = diff.materialize(&current_array, &registry);
            (
                next.get(x_idx).as_i64().unwrap(),
                next.get(y_idx).as_i64().unwrap(),
                next.get(z_idx).as_i64().unwrap(),
            )
        })
        .collect();
    materialized.sort_unstable();

    assert_eq!(materialized, vec![(1, 5, 100), (2, 6, 100), (3, 5, 100)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deferred_builders_evaluate_next_state_dependencies() {
    use tla_core::ast::Expr;
    use tla_core::{Span, Spanned};

    let src = r#"
---- MODULE DeferredBuild ----
VARIABLE x, y
====
"#;

    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let y_idx = registry.get("y").unwrap();
    let current_array = ArrayState::from_values(vec![Value::int(0), Value::int(0)]);

    let span = Span::dummy();
    let x_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let plus_ten = Spanned::new(
        Expr::Add(
            Box::new(x_prime),
            Box::new(Spanned::new(Expr::Int(10.into()), span)),
        ),
        span,
    );

    let assignments = vec![
        PrimedAssignment::InSet(Arc::from("x"), vec![Value::int(1), Value::int(2)]),
        PrimedAssignment::DeferredExpr(Arc::from("y"), plus_ten),
    ];

    let succs = build_successor_array_states_with_ctx(
        &current_array,
        &vars,
        &assignments,
        &registry,
        Some(&ctx),
    )
    .unwrap();

    let mut observed: Vec<(i64, i64)> = succs
        .iter()
        .map(|s| {
            (
                s.get(x_idx).as_i64().unwrap(),
                s.get(y_idx).as_i64().unwrap(),
            )
        })
        .collect();
    observed.sort_unstable();
    assert_eq!(observed, vec![(1, 11), (2, 12)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deferred_diff_builder_applies_filter_after_deferred_eval() {
    use tla_core::ast::Expr;
    use tla_core::{Span, Spanned};

    let src = r#"
---- MODULE DeferredDiffFilter ----
VARIABLE x, y
====
"#;

    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let y_idx = registry.get("y").unwrap();
    let current_array = ArrayState::from_values(vec![Value::int(0), Value::int(0)]);

    let span = Span::dummy();
    let x_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let plus_ten = Spanned::new(
        Expr::Add(
            Box::new(x_prime),
            Box::new(Spanned::new(Expr::Int(10.into()), span)),
        ),
        span,
    );

    let assignments = vec![
        PrimedAssignment::InSet(Arc::from("x"), vec![Value::int(1), Value::int(2)]),
        PrimedAssignment::DeferredExpr(Arc::from("y"), plus_ten),
    ];

    let diffs = build_successor_diffs_with_deferred_filtered(
        &current_array,
        &vars,
        &assignments,
        &registry,
        &ctx,
        |next| next.get(y_idx).as_i64().unwrap() >= 12,
    )
    .unwrap();

    assert_eq!(diffs.len(), 1);
    let materialized = diffs[0].materialize(&current_array, &registry);
    assert_eq!(materialized.get(x_idx).as_i64(), Some(2));
    assert_eq!(materialized.get(y_idx).as_i64(), Some(12));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deferred_array_builder_ignores_vars_missing_from_registry() {
    use tla_core::ast::Expr;
    use tla_core::{Span, Spanned};

    let src = r#"
---- MODULE DeferredMissingVar ----
VARIABLE x
====
"#;

    let (_module, ctx, vars) = setup_module(src);
    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").unwrap();
    let current_array = ArrayState::from_values(vec![Value::int(0)]);

    let mut vars_with_unknown = vars.clone();
    vars_with_unknown.push(Arc::from("ghost"));

    let span = Span::dummy();
    let assignments = vec![PrimedAssignment::DeferredExpr(
        Arc::from("x"),
        Spanned::new(Expr::Int(7.into()), span),
    )];

    let succs = build_successor_array_states_with_ctx(
        &current_array,
        &vars_with_unknown,
        &assignments,
        &registry,
        Some(&ctx),
    )
    .unwrap();

    assert_eq!(succs.len(), 1);
    assert_eq!(succs[0].get(x_idx).as_i64(), Some(7));
}
