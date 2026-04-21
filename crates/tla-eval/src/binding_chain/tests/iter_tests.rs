// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator tests: iter(), collect_local_bindings consistency, liveness bindings.
//! Part of #2962.

use super::super::*;
use crate::cache::StateLookupMode;
use std::sync::Arc;
use tla_core::name_intern::intern_name;
use tla_value::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_iter_empty_chain() {
    let chain = BindingChain::empty();
    assert_eq!(chain.iter().count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_iter_yields_all_bindings_newest_first() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_iter_x");
    let y_id = intern_name("test_bc_iter_y");
    let z_id = intern_name("test_bc_iter_z");

    // Build chain: x (oldest) -> y -> z (newest)
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(1)));
    let chain = chain.cons(y_id, BindingValue::eager(Value::int(2)));
    let chain = chain.cons(z_id, BindingValue::eager(Value::int(3)));

    let entries: Vec<_> = chain.iter().collect();
    assert_eq!(entries.len(), 3);

    // Newest first: z, y, x
    assert_eq!(entries[0].0, z_id);
    assert_eq!(entries[1].0, y_id);
    assert_eq!(entries[2].0, x_id);

    // Values match
    match entries[0].1 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(3)),
        _ => panic!("expected Eager"),
    }
    match entries[2].1 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_iter_mixed_binding_sources() {
    use super::super::super::OpEvalDeps;

    let chain = BindingChain::empty();
    let a_id = intern_name("test_bc_iter_mix_a");
    let b_id = intern_name("test_bc_iter_mix_b");
    let c_id = intern_name("test_bc_iter_mix_c");

    // None source (plain cons)
    let chain = chain.cons(a_id, BindingValue::eager(Value::int(10)));

    // Instance source (cons_with_deps)
    let deps = OpEvalDeps::default();
    let chain = chain.cons_with_deps(b_id, BindingValue::eager(Value::int(20)), deps);

    // Local source (cons_local)
    let chain = chain.cons_local(c_id, BindingValue::eager(Value::int(30)), 0);

    let entries: Vec<_> = chain.iter().collect();
    assert_eq!(entries.len(), 3);

    // c (Local), b (Instance), a (None) -- newest first
    assert!(matches!(entries[0].2, BindingSourceRef::Local(0)));
    assert!(matches!(entries[1].2, BindingSourceRef::Instance(_)));
    assert!(matches!(entries[2].2, BindingSourceRef::None));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_iter_consistent_with_collect_local_bindings() {
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_iter_clb_x");
    let y_id = intern_name("test_bc_iter_clb_y");
    let z_id = intern_name("test_bc_iter_clb_z");

    // Mix of local and non-local bindings
    let chain = chain.cons(x_id, BindingValue::eager(Value::int(1))); // None
    let chain = chain.cons_local(y_id, BindingValue::eager(Value::int(2)), 0); // Local
    let chain = chain.cons_local(z_id, BindingValue::eager(Value::int(3)), 1); // Local

    // collect_local_bindings returns oldest-first local-only bindings as (Arc<str>, Value, NameId)
    let collected = chain.collect_local_bindings();

    // iter() returns newest-first ALL bindings; filter and reverse to match
    let iter_locals: Vec<_> = chain
        .iter()
        .filter(|(_, _, source)| matches!(source, BindingSourceRef::Local(_)))
        .filter_map(|(name_id, value, source)| {
            value
                .get_if_ready(StateLookupMode::Current, source)
                .map(|v| (v, name_id))
        })
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();

    assert_eq!(collected.len(), iter_locals.len());
    for (c, i) in collected.iter().zip(iter_locals.iter()) {
        assert_eq!(c.1, i.0); // value
        assert_eq!(c.2, i.1); // name_id
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_bindings_participate_in_local_helpers() {
    let x_id = intern_name("test_bc_liveness_x");
    let p_id = intern_name("test_bc_liveness_p");
    let chain = BindingChain::empty()
        .cons_local(x_id, BindingValue::eager(Value::int(1)), 0)
        .cons_liveness_local(p_id, BindingValue::eager(Value::int(2)), 1);

    assert_eq!(chain.lookup_local_depth(p_id), Some(1));
    assert_eq!(chain.get_local_by_depth(0), Some(Value::int(2)));
    assert_eq!(chain.get_local_by_depth(1), Some(Value::int(1)));

    let locals = chain.collect_local_bindings();
    assert_eq!(
        locals,
        vec![
            (Arc::from("test_bc_liveness_x"), Value::int(1), x_id),
            (Arc::from("test_bc_liveness_p"), Value::int(2), p_id),
        ]
    );

    let mut env = crate::core::Env::default();
    chain.write_locals_to_env(&mut env);
    assert_eq!(env.get("test_bc_liveness_x"), Some(&Value::int(1)));
    assert_eq!(env.get("test_bc_liveness_p"), Some(&Value::int(2)));
}
