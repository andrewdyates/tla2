// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for action instance splitting.

use super::*;
use crate::EvalCtx;
use tla_core::ast::{BoundVar, Expr, Module};
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn load_and_find_op(src: &str, name: &str) -> (EvalCtx, OperatorDef) {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(d) if d.name.node == name => Some(d.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing operator {name}"));
    (ctx, def)
}

fn lower_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    lowered.module.expect("lowered module")
}

// Part of #3354 Slice 4: bosco_real_next, action_contains_subset_constrained,
// and test_split_bosco_real_next_preserves_constrained_variant removed —
// they tested CompiledAction pattern preservation which is no longer applicable.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_specializes_const_level_apply_but_not_state_level() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) ==
  \/ a = 1 /\ x' = 1
  \/ a = 1 /\ x' = 2

Next == Op(1) \/ Op(x)
====
"#;

    let (ctx, next_def) = load_and_find_op(src, "Next");
    let actions = split_action_instances(&ctx, &next_def.body).unwrap();

    // Op(1) specializes and splits into 2 actions; Op(x) does not specialize and remains 1 leaf.
    assert_eq!(actions.len(), 3);

    let a1 = Value::int(1);
    let specialized = actions
        .iter()
        .filter(|a| {
            a.bindings
                .iter()
                .any(|(k, v)| k.as_ref() == "a" && v == &a1)
        })
        .count();
    assert_eq!(specialized, 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_allows_bounded_exists_bindings_for_const_level_actuals() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) ==
  \/ a = 1 /\ x' = 1
  \/ a = 2 /\ x' = 2

Next == \E y \in {1, 2} : Op(y)
====
"#;

    let (ctx, next_def) = load_and_find_op(src, "Next");
    let actions = split_action_instances(&ctx, &next_def.body).unwrap();

    // y is enumerated (2 values), and each Op(y) specializes + splits into 2 disjunct actions.
    assert_eq!(actions.len(), 4);

    let a_vals: Vec<i64> = actions
        .iter()
        .filter_map(|a| {
            a.bindings.iter().find_map(|(k, v)| {
                if k.as_ref() != "a" {
                    return None;
                }
                v.as_i64()
            })
        })
        .collect();
    assert_eq!(a_vals.iter().copied().filter(|v| *v == 1).count(), 2);
    assert_eq!(a_vals.iter().copied().filter(|v| *v == 2).count(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_supports_dependent_bounded_exists_domains() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) == x' = a

Next == \E y \in {1, 2} : \E z \in {y} : Op(z)
====
"#;

    let (ctx, next_def) = load_and_find_op(src, "Next");
    let actions = split_action_instances(&ctx, &next_def.body).unwrap();
    assert_eq!(actions.len(), 2);

    let mut a_vals: Vec<i64> = actions
        .iter()
        .map(|a| {
            a.bindings
                .iter()
                .find_map(|(k, v)| (k.as_ref() == "a").then_some(v))
                .and_then(tla_value::Value::as_i64)
                .expect("instance has a=int(..)")
        })
        .collect();
    a_vals.sort_unstable();
    assert_eq!(a_vals, vec![1, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_supports_dependent_bounded_exists_domains_when_bounds_reversed() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) == x' = a
====
"#;

    let module = lower_module(src);

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let y_bound = BoundVar {
        name: Spanned::dummy("y".to_string()),
        domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![
            Spanned::dummy(Expr::Int(1.into())),
            Spanned::dummy(Expr::Int(2.into())),
        ])))),
        pattern: None,
    };

    let z_bound = BoundVar {
        name: Spanned::dummy("z".to_string()),
        domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![
            Spanned::dummy(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        ])))),
        pattern: None,
    };

    let body = Spanned::dummy(Expr::Apply(
        Box::new(Spanned::dummy(Expr::Ident(
            "Op".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![Spanned::dummy(Expr::Ident(
            "z".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    ));

    // Deliberately reversed vs spec order: z depends on y, so the forward split fails and we
    // rely on the reverse-order fallback.
    let expr = Spanned::dummy(Expr::Exists(vec![z_bound, y_bound], Box::new(body)));

    let actions = split_action_instances(&ctx, &expr).unwrap();
    assert_eq!(actions.len(), 2);

    let mut a_vals: Vec<i64> = actions
        .iter()
        .map(|a| {
            a.bindings
                .iter()
                .find_map(|(k, v)| (k.as_ref() == "a").then_some(v))
                .and_then(tla_value::Value::as_i64)
                .expect("instance has a=int(..)")
        })
        .collect();
    a_vals.sort_unstable();
    assert_eq!(a_vals, vec![1, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_binds_const_level_module_ref_actuals() {
    let inst_src = r#"
---- MODULE Inst ----
VARIABLE x

Op(a) == x' = a
====
"#;
    let main_src = r#"
---- MODULE Test ----
VARIABLE x

I == INSTANCE Inst

Next == I!Op(1) \/ I!Op(2)
====
"#;

    let inst_module = lower_module(inst_src);
    let test_module = lower_module(main_src);

    let mut ctx = EvalCtx::new();
    ctx.load_instance_module("Inst".to_string(), &inst_module);
    ctx.load_module(&test_module);

    let next_def = test_module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(d) if d.name.node == "Next" => Some(d.clone()),
            _ => None,
        })
        .expect("missing Next");

    let actions = split_action_instances(&ctx, &next_def.body).unwrap();
    assert_eq!(actions.len(), 2);

    let mut a_vals: Vec<i64> = actions
        .iter()
        .map(|a| {
            assert_eq!(a.name.as_deref(), Some("I!Op"));
            a.bindings
                .iter()
                .find_map(|(k, v)| (k.as_ref() == "a").then_some(v))
                .and_then(tla_value::Value::as_i64)
                .expect("instance has a=int(..)")
        })
        .collect();
    a_vals.sort_unstable();
    assert_eq!(a_vals, vec![1, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_by_action_instance_attributes_bindings() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) == x' = a

Next == \E y \in {1, 2} : Op(y)
====
"#;

    let (mut ctx, next_def) = load_and_find_op(src, "Next");
    let state = State::from_pairs([("x", Value::int(0))]);
    let vars = vec![Arc::from("x")];

    let per = enumerate_successors_by_action_instance(&mut ctx, &next_def, &state, &vars)
        .expect("enumerate successors");
    assert_eq!(per.len(), 2);

    let mut xs = Vec::new();
    for inst in per {
        assert_eq!(inst.successors.len(), 1);
        let succ = &inst.successors[0];
        let x = succ
            .vars()
            .find_map(|(k, v)| (k.as_ref() == "x").then_some(v))
            .and_then(tla_value::Value::as_i64)
            .expect("successor has x=int(..)");

        let a = inst
            .instance
            .bindings
            .iter()
            .find_map(|(k, v)| (k.as_ref() == "a").then_some(v))
            .and_then(tla_value::Value::as_i64)
            .expect("instance has a=int(..)");
        assert_eq!(a, x);
        xs.push(x);
    }

    xs.sort_unstable();
    assert_eq!(xs, vec![1, 2]);
}

/// Regression test for #1886: split_action_instances correctly handles
/// const-level SetFilter domains that ARE enumerable.
///
/// When `try_eval_const_level` successfully evaluates a SetFilter domain
/// (e.g., `{n \in {1,2} : n > 0}` → `{1,2}`), the resulting concrete set
/// is iterable and produces one action per element. This verifies the
/// happy path still works after #1886 error discrimination changes.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1886_split_action_instances_const_setfilter_splits() {
    // Valid SetFilter domain evaluates at const-level to a concrete set.
    let src = r#"
---- MODULE SplitSetFilter ----
EXTENDS Integers
VARIABLE x
Next == \E v \in {n \in {1, 2} : n > 0} : x' = v
====
"#;
    let (ctx, next_def) = load_and_find_op(src, "Next");
    let result = split_action_instances(&ctx, &next_def.body);
    assert!(
        result.is_ok(),
        "#1886: valid SetFilter domain should not error: {:?}",
        result
    );
    let actions = result.unwrap();
    // {n \in {1,2} : n > 0} evaluates to {1,2} → 2 action instances.
    assert_eq!(
        actions.len(),
        2,
        "#1886: const-level SetFilter domain should produce 2 action instances"
    );
}

/// Regression test for #1886: split_action_instances returns Ok(leaf) when
/// SetFilter evaluation fails in try_eval_const_level (error caught before
/// reaching eval_iter_set).
///
/// The broken SetFilter `{n \in {1,2} : 1}` (non-boolean predicate) fails
/// during try_eval_const_level's eager evaluation, which catches the error
/// and returns None → leaf action. The #1886 error discrimination in
/// `try_split_exists_all_bounds` is defensive code for the case where
/// try_eval_const_level succeeds but eval_iter_set fails.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1886_split_action_instances_broken_setfilter_leaf() {
    let src = r#"
---- MODULE SplitBrokenFilter ----
EXTENDS Integers
VARIABLE x
Next == \E v \in {n \in {1, 2} : 1} : x' = v
====
"#;
    let (ctx, next_def) = load_and_find_op(src, "Next");
    let result = split_action_instances(&ctx, &next_def.body);
    assert!(
        result.is_ok(),
        "#1886: broken SetFilter caught by try_eval_const_level should produce \
         leaf action, not error: {:?}",
        result
    );
    let actions = result.unwrap();
    // try_eval_const_level returns None for the broken SetFilter,
    // so the EXISTS is not split → 1 leaf action.
    assert_eq!(
        actions.len(),
        1,
        "#1886: broken SetFilter domain should fall back to 1 leaf action"
    );
}

/// Regression test for #1886: split_action_instances correctly falls back
/// for non-enumerable domains (defer-class errors) without propagating.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1886_split_action_instances_defers_non_enumerable() {
    // Nat is not const-level (try_eval_const_level returns None), so the
    // split should return false → leaf action. This tests the existing
    // behavior is preserved: non-enumerable domains don't error.
    let src = r#"
---- MODULE SplitDefer ----
EXTENDS Naturals
VARIABLE x
Next == \E v \in Nat : x' = v
====
"#;
    let (ctx, next_def) = load_and_find_op(src, "Next");
    let result = split_action_instances(&ctx, &next_def.body);
    assert!(
        result.is_ok(),
        "#1886: non-enumerable domain should fall back to leaf, not error: {:?}",
        result
    );
    let actions = result.unwrap();
    // Should produce 1 leaf action (the EXISTS is not split).
    assert_eq!(
        actions.len(),
        1,
        "#1886: non-splittable EXISTS should produce 1 leaf action"
    );
}

/// Regression test for #1920: Verify that split_action_instances PROPAGATES
/// fatal errors from eval_iter_set when try_eval_const_level succeeds.
///
/// This exercises the Defer-vs-Fatal discrimination in `try_split_exists_all_bounds`
/// (line 323-329). The domain `{n \in SUBSET {1,2} : 1}` uses SUBSET (a lazy set),
/// so `try_eval_const_level` returns `Some(Value::SetPred(...))` without evaluating
/// the predicate. Then `eval_iter_set` materializes the SetPred, evaluating predicate
/// `1` for each element → TypeError(expected: BOOLEAN) → Fatal → propagated as Err.
///
/// This is the ONLY action_instance test that exercises the Fatal return path at
/// line 328. The other test_1886_* tests all have try_eval_const_level catching
/// errors before eval_iter_set runs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1920_split_fatal_error_propagated_from_lazy_setpred() {
    // SUBSET {1,2} is lazy → SetFilter over it creates a SetPred value.
    // try_eval_const_level returns Some(SetPred) — construction succeeds.
    // eval_iter_set evaluates the predicate `1` (not a boolean) → Fatal TypeError.
    let src = r#"
---- MODULE SplitFatalSetPred ----
EXTENDS FiniteSets
VARIABLE x
Next == \E v \in {n \in SUBSET {1, 2} : 1} : x' = v
====
"#;
    let (ctx, next_def) = load_and_find_op(src, "Next");
    let result = split_action_instances(&ctx, &next_def.body);
    assert!(
        result.is_err(),
        "#1920: SetPred with non-boolean predicate should propagate \
         Fatal error, not silently defer to leaf action. Got Ok({:?})",
        result.as_ref().ok().map(std::vec::Vec::len)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_by_action_instance_restores_ctx_env() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

Op(a) == x' = a

Next == \E y \in {1, 2} : Op(y)
====
"#;

    let (mut ctx, next_def) = load_and_find_op(src, "Next");
    let state = State::from_pairs([("x", Value::int(0))]);
    let vars = vec![Arc::from("x")];

    assert!(ctx.env().get("x").is_none(), "precondition: x unbound");
    let _ = enumerate_successors_by_action_instance(&mut ctx, &next_def, &state, &vars)
        .expect("enumerate successors");
    assert!(ctx.env().get("x").is_none(), "ctx.env should be restored");
}
