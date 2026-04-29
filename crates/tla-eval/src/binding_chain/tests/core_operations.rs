// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core BindingChain operations: empty, cons, lookup, shadowing, sharing, clone, default, debug.

use super::super::*;
use tla_core::name_intern::intern_name;
use tla_value::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_chain() {
    let chain = BindingChain::empty();
    assert!(chain.is_empty());
    assert_eq!(chain.depth(), 0);
    let id = intern_name("x");
    assert!(chain.lookup(id).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cons_and_lookup_eager() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_x");
    let y_id = intern_name("test_bc_y");

    let chain = chain.cons(x_id, BindingValue::eager(Value::int(42)));
    assert!(!chain.is_empty());
    assert_eq!(chain.depth(), 1);

    // Lookup existing binding
    let result = chain.lookup(x_id);
    assert!(result.is_some());
    let (bv, source) = result.unwrap();
    assert!(matches!(source, BindingSourceRef::None)); // cons() uses None
    match bv {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(42)),
        _ => panic!("expected Eager"),
    }

    // Lookup non-existing binding
    assert!(chain.lookup(y_id).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cons_shadows_earlier_binding() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_shadow_x");

    let chain = chain.cons(x_id, BindingValue::eager(Value::int(1)));
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(2)));
    assert_eq!(chain.depth(), 2);

    // Lookup finds the most recent (shadow) binding
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(2)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chain_sharing() {
    // Two chains sharing the same tail (immutable structure)
    let base = BindingChain::empty();
    let x_id = intern_name("test_bc_share_x");
    let y_id = intern_name("test_bc_share_y");
    let z_id = intern_name("test_bc_share_z");

    let base = base.cons(x_id, BindingValue::eager(Value::int(1)));

    // Two branches from the same base
    let branch_a = base.cons(y_id, BindingValue::eager(Value::int(2)));
    let branch_b = base.cons(z_id, BindingValue::eager(Value::int(3)));

    // branch_a sees x and y
    assert!(branch_a.lookup(x_id).is_some());
    assert!(branch_a.lookup(y_id).is_some());
    assert!(branch_a.lookup(z_id).is_none());

    // branch_b sees x and z
    assert!(branch_b.lookup(x_id).is_some());
    assert!(branch_b.lookup(z_id).is_some());
    assert!(branch_b.lookup(y_id).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clone_is_cheap() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_clone_x");
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(99)));

    // Clone should be just an Rc refcount bump
    let cloned = chain.clone();
    assert_eq!(cloned.depth(), 1);
    match cloned.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(99)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_is_empty() {
    let chain = BindingChain::default();
    assert!(chain.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_debug_format() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_dbg_x");
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(1)));
    let debug = format!("{:?}", chain);
    assert!(debug.starts_with("BindingChain["));
    assert!(debug.contains("eager"));
}
