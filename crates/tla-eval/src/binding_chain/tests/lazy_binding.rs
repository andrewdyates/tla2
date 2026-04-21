// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy binding cache tests: OnceLock caching, dual-mode independence, idempotent set.

use super::super::*;
use crate::cache::StateLookupMode;
use std::sync::OnceLock;
use tla_core::name_intern::intern_name;
use tla_core::Spanned;
use tla_value::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_binding_cache() {
    // Part of #3465: local lazy bindings may populate the underlying OnceLock,
    // but ready-value reads remain disabled at the BindingValue layer.
    let chain = BindingChain::empty();
    let x_id = intern_name("test_bc_lazy_x");

    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding {
        expr_ptr: std::ptr::addr_of!(dummy_expr),
        enclosing: BindingChain::empty(),
        cached: OnceLock::new(),
        cached_primed: OnceLock::new(),
        forced_deps: OnceLock::new(),
        forced_deps_primed: OnceLock::new(),
    };

    let chain = chain.cons_local(x_id, BindingValue::Lazy(Box::new(lazy)), 0);

    // Lookup finds the lazy binding
    let (bv, source) = chain.lookup(x_id).unwrap();
    assert!(matches!(source, BindingSourceRef::Local(0)));
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());
    let lazy = bv.as_lazy().unwrap();

    // Before set_cached, OnceLock is empty and get_if_ready returns None.
    assert!(lazy.cached.get().is_none());
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());

    // After set_cached, the underlying OnceLock is populated but ready-value
    // reads remain disabled.
    lazy.set_cached(Value::Bool(true), StateLookupMode::Current);
    assert!(lazy.cached.get().is_some());
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_binding_dual_cache_mode_independence() {
    // Part of #3465: even with ready-value reads disabled, the underlying
    // Current/Next OnceLock slots remain independent.
    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding {
        expr_ptr: std::ptr::addr_of!(dummy_expr),
        enclosing: BindingChain::empty(),
        cached: OnceLock::new(),
        cached_primed: OnceLock::new(),
        forced_deps: OnceLock::new(),
        forced_deps_primed: OnceLock::new(),
    };

    // Both OnceLock slots start empty.
    assert!(lazy.cached.get().is_none());
    assert!(lazy.cached_primed.get().is_none());

    // Current and Next OnceLock slots populate independently.
    lazy.set_cached(Value::int(1), StateLookupMode::Current);
    assert_eq!(lazy.cached.get(), Some(&Value::int(1)));
    assert!(lazy.cached_primed.get().is_none());
    lazy.set_cached(Value::int(2), StateLookupMode::Next);
    assert_eq!(lazy.cached_primed.get(), Some(&Value::int(2)));
    assert_eq!(lazy.cached.get(), Some(&Value::int(1)));

    // `get_if_ready` remains disabled for Lazy variants regardless of source.
    let x_id = intern_name("test_bc_dual_cache_x");
    let chain = BindingChain::empty().cons(x_id, BindingValue::Lazy(Box::new(lazy)));
    let (bv, source) = chain.lookup(x_id).unwrap();
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());
    assert!(bv.get_if_ready(StateLookupMode::Next, source).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_source_skips_oncelock_reads() {
    let x_id = intern_name("test_bc_instance_lazy_x");
    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding {
        expr_ptr: std::ptr::addr_of!(dummy_expr),
        enclosing: BindingChain::empty(),
        cached: OnceLock::new(),
        cached_primed: OnceLock::new(),
        forced_deps: OnceLock::new(),
        forced_deps_primed: OnceLock::new(),
    };

    let chain = BindingChain::empty().cons_with_deps(
        x_id,
        BindingValue::Lazy(Box::new(lazy)),
        crate::OpEvalDeps::default(),
    );
    let (bv, source) = chain.lookup(x_id).unwrap();
    assert!(matches!(source, BindingSourceRef::Instance(_)));

    let lazy = bv.as_lazy().unwrap();
    lazy.set_cached(Value::int(42), StateLookupMode::Current);
    assert_eq!(lazy.cached.get(), Some(&Value::int(42)));
    // INSTANCE source: get_if_ready returns None despite OnceLock being populated.
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_binding_dual_deps_mode_independence() {
    use super::super::super::{OpEvalDeps, VarDepMap};
    use smallvec::smallvec;
    use tla_core::VarIndex;

    // Part of #3056 Phase 5: Verify forced_deps and forced_deps_primed are independent.
    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding {
        expr_ptr: std::ptr::addr_of!(dummy_expr),
        enclosing: BindingChain::empty(),
        cached: OnceLock::new(),
        cached_primed: OnceLock::new(),
        forced_deps: OnceLock::new(),
        forced_deps_primed: OnceLock::new(),
    };

    // Both start empty
    assert!(lazy.get_forced_deps(StateLookupMode::Current).is_none());
    assert!(lazy.get_forced_deps(StateLookupMode::Next).is_none());

    // Set deps for Current mode (reads state var 0)
    let deps_current = OpEvalDeps {
        local: smallvec![],
        state: VarDepMap::from_entries(&[(VarIndex::new(0), Value::int(10))]),
        next: VarDepMap::default(),
        inconsistent: false,
        ..Default::default()
    };
    lazy.set_forced_deps(deps_current, StateLookupMode::Current);
    assert!(lazy.get_forced_deps(StateLookupMode::Current).is_some());
    assert!(lazy.get_forced_deps(StateLookupMode::Next).is_none());

    // Set deps for Next mode (reads state var 1)
    let deps_next = OpEvalDeps {
        local: smallvec![],
        state: VarDepMap::default(),
        next: VarDepMap::from_entries(&[(VarIndex::new(1), Value::int(20))]),
        inconsistent: false,
        ..Default::default()
    };
    lazy.set_forced_deps(deps_next, StateLookupMode::Next);

    // Both are populated with independent data
    let current_deps = lazy.get_forced_deps(StateLookupMode::Current).unwrap();
    assert!(current_deps.state.contains_key(&VarIndex::new(0)));
    assert!(!current_deps.next.contains_key(&VarIndex::new(1)));

    let next_deps = lazy.get_forced_deps(StateLookupMode::Next).unwrap();
    assert!(next_deps.next.contains_key(&VarIndex::new(1)));
    assert!(!next_deps.state.contains_key(&VarIndex::new(0)));
}

// --- Arena escape promotion tests (Part of #3580 audit) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_binding_new_promotes_arena_enclosing_chain() {
    use crate::eval_arena::{init_thread_arena, ArenaStateGuard};

    init_thread_arena();
    let _guard = ArenaStateGuard::new();

    // Build an arena-backed chain.
    let x_id = intern_name("test_bc_lazy_arena_promote_x");
    let chain = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(42)));

    // Construct a LazyBinding via the new() constructor which should promote.
    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding::new(std::ptr::addr_of!(dummy_expr), &chain);

    // The stored enclosing chain must be fully heap-backed (no arena pointers).
    // Verify by looking up the value — it should still resolve correctly.
    match lazy.enclosing.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(42)),
        _ => panic!("expected Eager"),
    }

    // The promoted chain should survive arena reset. Drop the guard to end
    // the arena state, then verify the lazy binding's enclosing chain is
    // still valid (heap-backed nodes survive arena reset).
    drop(_guard);

    match lazy.enclosing.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(42)),
        _ => panic!("expected Eager after arena reset"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_binding_set_cached_idempotent() {
    // OnceLock remains first-writer-wins even though ready-value reads stay disabled.
    let dummy_expr = Spanned::dummy(tla_core::ast::Expr::Bool(true));
    let lazy = LazyBinding {
        expr_ptr: std::ptr::addr_of!(dummy_expr),
        enclosing: BindingChain::empty(),
        cached: OnceLock::new(),
        cached_primed: OnceLock::new(),
        forced_deps: OnceLock::new(),
        forced_deps_primed: OnceLock::new(),
    };
    let x_id = intern_name("test_bc_set_cached_idempotent");
    let chain = BindingChain::empty().cons_local(x_id, BindingValue::Lazy(Box::new(lazy)), 0);
    let (bv, source) = chain.lookup(x_id).unwrap();
    let lazy = bv.as_lazy().unwrap();

    // set_cached does not panic on multiple calls (OnceLock silently ignores).
    lazy.set_cached(Value::int(42), StateLookupMode::Current);
    lazy.set_cached(Value::int(99), StateLookupMode::Current);
    assert_eq!(lazy.cached.get(), Some(&Value::int(42)));
    assert!(bv.get_if_ready(StateLookupMode::Current, source).is_none());

    lazy.set_cached(Value::int(7), StateLookupMode::Next);
    lazy.set_cached(Value::int(100), StateLookupMode::Next);
    assert_eq!(lazy.cached_primed.get(), Some(&Value::int(7)));
    assert!(bv.get_if_ready(StateLookupMode::Next, source).is_none());
}
