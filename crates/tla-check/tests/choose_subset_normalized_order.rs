// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use num_bigint::BigInt;
use tla_check::{eval, EvalCtx, SubsetValue, Value};
use tla_core::ast::{BoundVar, Expr};
use tla_core::Spanned;

fn int_expr(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(BigInt::from(n)))
}

fn ident_expr(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn subset_iterator_is_cardinality_first() {
    // TLC enumerates SUBSET S in "normalized" order by increasing cardinality:
    //   {}; all 1-subsets; all 2-subsets; ...; all n-subsets.
    // Within each cardinality bucket, subsets are enumerated in lexicographic order
    // w.r.t. the normalized order of S's elements.
    //
    // This is parity-critical for CHOOSE (first satisfying witness).
    //
    // Part of #980, #985.
    let base = Value::set([
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
        Value::SmallInt(4),
    ]);
    let ps = Value::Subset(SubsetValue::new(base));

    let elems: Vec<Value> = ps.iter_set().unwrap().collect();

    let expected = vec![
        Value::empty_set(),
        Value::set(vec![Value::SmallInt(1)]),
        Value::set(vec![Value::SmallInt(2)]),
        Value::set(vec![Value::SmallInt(3)]),
        Value::set(vec![Value::SmallInt(4)]),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(2)]),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(3)]),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(4)]),
        Value::set(vec![Value::SmallInt(2), Value::SmallInt(3)]),
        Value::set(vec![Value::SmallInt(2), Value::SmallInt(4)]),
        Value::set(vec![Value::SmallInt(3), Value::SmallInt(4)]),
        Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]),
        Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(4),
        ]),
        Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(3),
            Value::SmallInt(4),
        ]),
        Value::set(vec![
            Value::SmallInt(2),
            Value::SmallInt(3),
            Value::SmallInt(4),
        ]),
        Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
            Value::SmallInt(4),
        ]),
    ];
    assert_eq!(elems, expected);
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn subset_iterator_empty_base_is_singleton_empty_set() {
    // Part of #980.
    let ps = Value::Subset(SubsetValue::new(Value::empty_set()));
    let elems: Vec<Value> = ps.iter_set().unwrap().collect();
    assert_eq!(elems, vec![Value::empty_set()]);
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn subset_iterator_is_cardinality_then_lexicographic_small_int_property() {
    // Property-style check of TLC's normalized SUBSET iteration order:
    // - cardinality-first
    // - lexicographic within each fixed-cardinality bucket (w.r.t. base element order)
    //
    // This test intentionally uses only integers (which TLC can compare/sort). TLC throws on
    // attempting to normalize/compare incomparable mixed-type elements (e.g., Bool vs Int).
    //
    // Part of #980, #985, #989.
    let base = Value::set((1..=6).map(Value::SmallInt));
    let ps = Value::Subset(SubsetValue::new(base));

    let mut prev_k: Option<usize> = None;
    let mut prev_combo: Option<Vec<i64>> = None;
    let mut count = 0usize;

    for subset in ps.iter_set().unwrap() {
        let elems: Vec<i64> = subset
            .iter_set()
            .unwrap()
            .map(|v| match v {
                Value::SmallInt(n) => n,
                other => panic!("expected SmallInt, got {other:?}"),
            })
            .collect();
        let k = elems.len();

        match prev_k {
            None => {
                assert_eq!(k, 0);
                assert!(elems.is_empty());
            }
            Some(pk) => {
                assert!(k >= pk);
                if k != pk {
                    assert_eq!(k, pk + 1);
                    let expected_first: Vec<i64> = (1..=(k as i64)).collect();
                    assert_eq!(elems, expected_first);
                    prev_combo = None;
                }
            }
        }

        if let Some(prev) = &prev_combo {
            assert!(prev < &elems);
        }

        prev_k = Some(k);
        prev_combo = Some(elems);
        count += 1;
    }

    assert_eq!(count, 64);
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn choose_over_subset_prefers_smallest_cardinality_witness() {
    // With base S = {1,2,3}:
    // - Cardinality-first powerset order finds {3} before any 2-subset.
    // - Bitmask order would find {1,2} before {3}.
    //
    // Predicate holds for subsets containing 3 OR containing both 1 and 2.
    // TLC returns the first satisfying subset in normalized order, so the witness is {3}.
    //
    // Part of #980.
    let ctx = EvalCtx::new();
    let x = ident_expr("x");

    let base = Spanned::dummy(Expr::SetEnum(vec![int_expr(1), int_expr(2), int_expr(3)]));
    let domain = Spanned::dummy(Expr::Powerset(Box::new(base)));

    let in1 = Spanned::dummy(Expr::In(Box::new(int_expr(1)), Box::new(x.clone())));
    let in2 = Spanned::dummy(Expr::In(Box::new(int_expr(2)), Box::new(x.clone())));
    let in3 = Spanned::dummy(Expr::In(Box::new(int_expr(3)), Box::new(x.clone())));
    let in12 = Spanned::dummy(Expr::And(Box::new(in1), Box::new(in2)));
    let pred = Spanned::dummy(Expr::Or(Box::new(in3), Box::new(in12)));

    let bv = BoundVar {
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };

    let choose_expr = Spanned::dummy(Expr::Choose(bv, Box::new(pred)));
    let v = eval(&ctx, &choose_expr).expect("eval CHOOSE");
    assert_eq!(v, Value::set(vec![Value::SmallInt(3)]));
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn choose_over_subset_is_lexicographic_within_cardinality() {
    // For S = {1,2,3,4}, the first 2-subsets in TLC's normalized order are:
    //   {1,2}, {1,3}, {1,4}, {2,3}, ...
    //
    // Predicate holds for {1,4} OR {2,3}. This pins lexicographic ordering within the
    // 2-subset bucket: TLC should pick {1,4}.
    //
    // Part of #980, #985.
    let ctx = EvalCtx::new();
    let x = ident_expr("x");

    let base = Spanned::dummy(Expr::SetEnum(vec![
        int_expr(1),
        int_expr(2),
        int_expr(3),
        int_expr(4),
    ]));
    let domain = Spanned::dummy(Expr::Powerset(Box::new(base)));

    let in1 = Spanned::dummy(Expr::In(Box::new(int_expr(1)), Box::new(x.clone())));
    let in2 = Spanned::dummy(Expr::In(Box::new(int_expr(2)), Box::new(x.clone())));
    let in3 = Spanned::dummy(Expr::In(Box::new(int_expr(3)), Box::new(x.clone())));
    let in4 = Spanned::dummy(Expr::In(Box::new(int_expr(4)), Box::new(x.clone())));
    let in14 = Spanned::dummy(Expr::And(Box::new(in1), Box::new(in4)));
    let in23 = Spanned::dummy(Expr::And(Box::new(in2), Box::new(in3)));
    let pred = Spanned::dummy(Expr::Or(Box::new(in14), Box::new(in23)));

    let bv = BoundVar {
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };

    let choose_expr = Spanned::dummy(Expr::Choose(bv, Box::new(pred)));
    let v = eval(&ctx, &choose_expr).expect("eval CHOOSE");
    assert_eq!(v, Value::set(vec![Value::SmallInt(1), Value::SmallInt(4)]));
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn subset_iterator_uses_tlc_tuple_length_first_order_for_base_normalization() {
    // TLC tuple ordering is length-first, then element-wise. SUBSET inherits this ordering via
    // base-set normalization, which is parity-critical for bounded CHOOSE over SUBSET domains.
    //
    // Part of #980.
    let base = Value::set([
        Value::tuple([Value::SmallInt(0), Value::SmallInt(0)]),
        Value::tuple([Value::SmallInt(1)]),
        Value::tuple([Value::SmallInt(0)]),
    ]);
    let ps = Value::Subset(SubsetValue::new(base));

    let elems: Vec<Value> = ps.iter_set_tlc_normalized().unwrap().take(4).collect();

    let t0 = Value::tuple([Value::SmallInt(0)]);
    let t1 = Value::tuple([Value::SmallInt(1)]);
    let t00 = Value::tuple([Value::SmallInt(0), Value::SmallInt(0)]);
    let expected = vec![
        Value::empty_set(),
        Value::set([t0]),
        Value::set([t1]),
        Value::set([t00]),
    ];
    assert_eq!(elems, expected);
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn subset_iterator_uses_tlc_model_value_order_for_base_normalization() {
    // TLC compares untyped model values with non-model values (and orders model values first).
    // SUBSET inherits this ordering via base-set normalization, which is parity-critical for
    // bounded CHOOSE over SUBSET domains.
    //
    // Part of #980.
    // TLC orders model values by UniqueString token order (first-seen order), not lexicographic
    // order. Use two names where lexicographic order disagrees with creation order, and construct
    // them in a fixed sequence (avoid relying on Rust expression evaluation order).
    //
    // Also ensure these are *untyped* model values (typed model values have the form "<t>_<rest>").
    let mv_first = "mvZ_choose_subset_order_9b8a";
    let mv_second = "mvA_choose_subset_order_9b8a";
    let mv_first_val = Value::try_model_value(mv_first).unwrap();
    let mv_second_val = Value::try_model_value(mv_second).unwrap();
    let base = Value::set([Value::SmallInt(1), mv_first_val, mv_second_val]);
    let ps = Value::Subset(SubsetValue::new(base));

    let elems: Vec<Value> = ps.iter_set_tlc_normalized().unwrap().take(4).collect();
    let expected = vec![
        Value::empty_set(),
        Value::set([Value::try_model_value(mv_first).unwrap()]),
        Value::set([Value::try_model_value(mv_second).unwrap()]),
        Value::set([Value::SmallInt(1)]),
    ];
    assert_eq!(elems, expected);
}
