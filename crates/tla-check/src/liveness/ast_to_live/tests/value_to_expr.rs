// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Value-to-expression conversion tests: reification of runtime values back to AST
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::{assert_expr_range_int_bounds, make_ctx};
use super::*;

fn make_set_value(values: impl IntoIterator<Item = Value>) -> Value {
    let mut set = SetBuilder::new();
    for value in values {
        set.insert(value);
    }
    Value::Set(Arc::new(set.build()))
}

fn assert_subset_value_to_expr() {
    let subset = Value::Subset(SubsetValue::new(make_set_value([
        Value::SmallInt(1),
        Value::SmallInt(2),
    ])));
    let subset_expr = value_to_expr(&subset).unwrap();
    let Expr::Powerset(inner) = subset_expr else {
        panic!("Expected Powerset");
    };
    let Expr::SetEnum(elems) = inner.node else {
        panic!("Expected SetEnum inside Powerset");
    };
    assert_eq!(elems.len(), 2);
}

fn assert_funcset_value_to_expr() {
    let codomain = make_set_value([Value::String(Arc::<str>::from("a"))]);
    let funcset = Value::FuncSet(FuncSetValue::new(
        make_set_value([Value::SmallInt(1)]),
        codomain.clone(),
    ));
    let funcset_expr = value_to_expr(&funcset).unwrap();
    let Expr::FuncSet(dom, cod) = funcset_expr else {
        panic!("Expected FuncSet");
    };
    assert!(matches!(dom.node, Expr::SetEnum(_)));
    assert!(matches!(cod.node, Expr::SetEnum(_)));
}

fn assert_recordset_value_to_expr() {
    let recordset = Value::RecordSet(Arc::new(RecordSetValue::new([
        (
            Arc::<str>::from("a"),
            make_set_value([Value::SmallInt(1), Value::SmallInt(2)]),
        ),
        (
            Arc::<str>::from("b"),
            Value::Interval(Arc::new(IntervalValue::new(
                BigInt::from(3),
                BigInt::from(4),
            ))),
        ),
    ])));
    let recordset_expr = value_to_expr(&recordset).unwrap();
    let Expr::RecordSet(fields) = recordset_expr else {
        panic!("Expected RecordSet");
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].0.node, "a");
    assert_eq!(fields[1].0.node, "b");
}

fn assert_tupleset_value_to_expr() {
    let tupleset = Value::TupleSet(Arc::new(TupleSetValue::new([
        make_set_value([Value::SmallInt(1), Value::SmallInt(2)]),
        make_set_value([Value::String(Arc::<str>::from("a"))]),
    ])));
    let tupleset_expr = value_to_expr(&tupleset).unwrap();
    let Expr::Times(parts) = tupleset_expr else {
        panic!("Expected Times");
    };
    assert_eq!(parts.len(), 2);
}

fn assert_lazy_set_ops_value_to_expr() {
    let set_one = make_set_value([Value::SmallInt(1)]);
    let set_two = make_set_value([Value::SmallInt(2)]);

    let setcup = Value::SetCup(SetCupValue::new(set_one.clone(), set_two.clone()));
    assert!(matches!(value_to_expr(&setcup).unwrap(), Expr::Union(_, _)));

    let setcap = Value::SetCap(SetCapValue::new(set_one.clone(), set_two.clone()));
    assert!(matches!(
        value_to_expr(&setcap).unwrap(),
        Expr::Intersect(_, _)
    ));

    let setdiff = Value::SetDiff(SetDiffValue::new(set_one.clone(), set_two.clone()));
    assert!(matches!(
        value_to_expr(&setdiff).unwrap(),
        Expr::SetMinus(_, _)
    ));

    let big_union = Value::BigUnion(UnionValue::new(make_set_value([set_one, set_two])));
    assert!(matches!(
        value_to_expr(&big_union).unwrap(),
        Expr::BigUnion(_)
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_supports_lazy_set_values() {
    assert_subset_value_to_expr();
    assert_funcset_value_to_expr();
    assert_recordset_value_to_expr();
    assert_tupleset_value_to_expr();
    assert_lazy_set_ops_value_to_expr();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_supports_intfunc() {
    let f = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        3,
        4,
        vec![Value::SmallInt(10), Value::SmallInt(11)],
    )));
    let expr = value_to_expr(&f).unwrap();

    let Expr::Apply(op, args) = expr else {
        panic!("Expected Apply");
    };
    let Expr::Ident(op_name, _) = op.node else {
        panic!("Expected Ident operator");
    };
    assert_eq!(op_name, "@@");
    assert_eq!(args.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_bool_true() {
    let expr = value_to_expr(&Value::Bool(true)).unwrap();
    assert!(matches!(expr, Expr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_bool_false() {
    let expr = value_to_expr(&Value::Bool(false)).unwrap();
    assert!(matches!(expr, Expr::Bool(false)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_small_int() {
    let expr = value_to_expr(&Value::SmallInt(42)).unwrap();
    match expr {
        Expr::Int(n) => assert_eq!(n, BigInt::from(42)),
        _ => panic!("Expected Int"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_big_int() {
    let big = BigInt::from(1_000_000_000_000i64);
    let expr = value_to_expr(&Value::Int(Arc::new(big.clone()))).unwrap();
    match expr {
        Expr::Int(n) => assert_eq!(n, big),
        _ => panic!("Expected Int"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_string() {
    let expr = value_to_expr(&Value::String("hello".into())).unwrap();
    match expr {
        Expr::String(s) => assert_eq!(s, "hello"),
        _ => panic!("Expected String"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_model_value() {
    let expr = value_to_expr(&Value::ModelValue("m1".into())).unwrap();
    match expr {
        Expr::Ident(name, _) => assert_eq!(name, "m1"),
        _ => panic!("Expected Ident"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_tuple() {
    let tuple = Value::Tuple(vec![Value::SmallInt(1), Value::SmallInt(2)].into());
    let expr = value_to_expr(&tuple).unwrap();
    match expr {
        Expr::Tuple(elems) => {
            assert_eq!(elems.len(), 2);
        }
        _ => panic!("Expected Tuple"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_seq() {
    let seq = Value::seq([Value::SmallInt(1), Value::SmallInt(2)]);
    let expr = value_to_expr(&seq).unwrap();
    match expr {
        Expr::Tuple(elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(elems[0].node, Expr::Int(ref n) if *n == BigInt::from(1)));
            assert!(matches!(elems[1].node, Expr::Int(ref n) if *n == BigInt::from(2)));
        }
        _ => panic!("Expected Tuple (sequence reifies as tuple)"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_set() {
    let set = Value::set([Value::SmallInt(1), Value::SmallInt(2)]);
    let expr = value_to_expr(&set).unwrap();
    match expr {
        Expr::SetEnum(elems) => {
            assert_eq!(elems.len(), 2);
        }
        _ => panic!("Expected SetEnum"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_record() {
    let record = Value::record([("a", Value::SmallInt(1)), ("b", Value::SmallInt(2))]);
    let expr = value_to_expr(&record).unwrap();
    let Expr::Record(fields) = expr else {
        panic!("Expected Record");
    };
    assert_eq!(fields.len(), 2);
    let mut map = std::collections::BTreeMap::new();
    for (k, v) in fields {
        map.insert(k.node, v.node);
    }
    let Expr::Int(a) = map.remove("a").expect("missing field a") else {
        panic!("expected Int value for field a");
    };
    let Expr::Int(b) = map.remove("b").expect("missing field b") else {
        panic!("expected Int value for field b");
    };
    assert!(map.is_empty(), "unexpected extra record fields: {map:?}");
    assert_eq!(a, BigInt::from(1));
    assert_eq!(b, BigInt::from(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_record_roundtrip_eval() {
    let ctx = make_ctx();
    let record = Value::record([("a", Value::SmallInt(1)), ("b", Value::SmallInt(2))]);
    let expr = spanned(value_to_expr(&record).unwrap());
    let got = eval(&ctx, &expr).expect("eval(record)");
    assert_eq!(got, record);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_func_empty() {
    let f = Value::Func(Arc::new(FuncBuilder::new().build()));
    let expr = value_to_expr(&f).unwrap();

    let Expr::FuncDef(bounds, body) = expr else {
        panic!("Expected FuncDef for empty function");
    };
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].name.node, "_");
    assert!(
        bounds[0].pattern.is_none(),
        "Expected no pattern for empty func"
    );
    let domain = bounds[0]
        .domain
        .as_ref()
        .expect("Expected explicit empty domain");
    let Expr::SetEnum(domain_elems) = &domain.node else {
        panic!("Expected empty SetEnum domain");
    };
    assert!(domain_elems.is_empty());
    let Expr::Ident(name, _) = body.node else {
        panic!("Expected Ident body");
    };
    assert_eq!(name, "_");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_func_empty_roundtrip_eval() {
    let ctx = make_ctx();
    let f = Value::Func(Arc::new(FuncBuilder::new().build()));
    let expr = spanned(value_to_expr(&f).unwrap());
    let got = eval(&ctx, &expr).expect("eval(empty-func)");
    assert_eq!(got, f);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_func_non_empty() {
    let mut b = FuncBuilder::new();
    b.insert(Value::SmallInt(2), Value::Bool(true));
    b.insert(Value::SmallInt(1), Value::Bool(false));
    let f = Value::Func(Arc::new(b.build()));
    let expr = value_to_expr(&f).unwrap();

    let Expr::Apply(op, args) = expr else {
        panic!("Expected Apply");
    };
    let Expr::Ident(op_name, _) = op.node else {
        panic!("Expected Ident operator");
    };
    assert_eq!(op_name, "@@");
    assert_eq!(args.len(), 2);

    // (1 :> FALSE) @@ (2 :> TRUE)
    for (idx, (k, v)) in [(1, false), (2, true)].into_iter().enumerate() {
        let Expr::Apply(single_op, single_args) = &args[idx].node else {
            panic!("Expected :> Apply");
        };
        let Expr::Ident(single_op_name, _) = &single_op.node else {
            panic!("Expected Ident :> operator");
        };
        assert_eq!(single_op_name, ":>");
        assert_eq!(single_args.len(), 2);
        assert!(matches!(single_args[0].node, Expr::Int(ref n) if *n == BigInt::from(k)));
        assert!(matches!(single_args[1].node, Expr::Bool(b) if b == v));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_func_non_empty_roundtrip_eval() {
    let ctx = make_ctx();
    let mut b = FuncBuilder::new();
    b.insert(Value::SmallInt(2), Value::Bool(true));
    b.insert(Value::SmallInt(1), Value::Bool(false));
    let f = Value::Func(Arc::new(b.build()));
    let expr = spanned(value_to_expr(&f).unwrap());
    let got = eval(&ctx, &expr).expect("eval(non-empty-func)");
    assert_eq!(got, f);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_interval() {
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(6),
    )));
    let expr = value_to_expr(&interval).unwrap();
    assert_expr_range_int_bounds(expr, BigInt::from(1), BigInt::from(6));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_interval_roundtrip_eval() {
    let ctx = make_ctx();
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(6),
    )));
    let expr = spanned(value_to_expr(&interval).unwrap());
    let got = eval(&ctx, &expr).expect("eval(interval)");
    assert_eq!(got, interval);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_interval_negative() {
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(-3),
        BigInt::from(6),
    )));
    let expr = value_to_expr(&interval).unwrap();
    assert_expr_range_int_bounds(expr, BigInt::from(-3), BigInt::from(6));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_interval_empty() {
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(2),
        BigInt::from(1),
    )));
    let expr = value_to_expr(&interval).unwrap();
    assert_expr_range_int_bounds(expr, BigInt::from(2), BigInt::from(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_expr_unsupported_returns_error() {
    let result = value_to_expr(&Value::AnySet);
    assert!(result.is_err(), "AnySet should not be reifiable");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("AnySet"),
        "error message should name the variant: {}",
        err
    );
}
