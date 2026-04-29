// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use tla_check::{FuncSetValue, Value};

#[cfg_attr(test, timeout(10000))]
#[test]
fn func_set_iterator_order_domain_most_significant() {
    // Regression for MCNanoSmall parity (#804): CHOOSE over [S -> T] must enumerate in TLC order.
    //
    // We avoid hard-coding domain/codomain element order; instead, we derive the sorted order
    // that `[S -> T]` uses and assert that the *last* domain element changes fastest.
    let domain = Value::set([
        Value::try_model_value("d1").unwrap(),
        Value::try_model_value("d2").unwrap(),
    ]);
    let codomain = Value::set([
        Value::try_model_value("c1").unwrap(),
        Value::try_model_value("c2").unwrap(),
    ]);
    let fs = Value::FuncSet(FuncSetValue::new(domain.clone(), codomain.clone()));

    let dom: Vec<Value> = domain.iter_set().unwrap().collect();
    let cod: Vec<Value> = codomain.iter_set().unwrap().collect();
    assert_eq!(dom.len(), 2);
    assert_eq!(cod.len(), 2);

    let mut it = fs.iter_set().expect("function set must be enumerable");
    let f0 = it.next().unwrap().to_func_coerced().unwrap();
    let f1 = it.next().unwrap().to_func_coerced().unwrap();
    let f2 = it.next().unwrap().to_func_coerced().unwrap();
    let f3 = it.next().unwrap().to_func_coerced().unwrap();

    // Expected base-|T| counting with the *last* domain element as least significant:
    //   [0,0], [0,1], [1,0], [1,1]
    assert_eq!(f0.apply(&dom[0]), Some(&cod[0]));
    assert_eq!(f0.apply(&dom[1]), Some(&cod[0]));

    assert_eq!(f1.apply(&dom[0]), Some(&cod[0]));
    assert_eq!(f1.apply(&dom[1]), Some(&cod[1]));

    assert_eq!(f2.apply(&dom[0]), Some(&cod[1]));
    assert_eq!(f2.apply(&dom[1]), Some(&cod[0]));

    assert_eq!(f3.apply(&dom[0]), Some(&cod[1]));
    assert_eq!(f3.apply(&dom[1]), Some(&cod[1]));
}
