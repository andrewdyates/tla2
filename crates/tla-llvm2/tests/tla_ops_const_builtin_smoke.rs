// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_*` const/builtin FFI surface.
//!
//! This test mirrors `tla_ops_set_smoke.rs` for the const_builtin family.
//! It exercises the four helpers (`tla_load_const`, `tla_cardinality`,
//! `tla_is_finite_set`, `tla_tostring`) **through the extern symbol map**
//! the JIT linker will actually use, catching symbol-name and ABI
//! mismatches the in-crate unit tests cannot see.
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI).

#![cfg(feature = "native")]

use tla_llvm2::extern_symbol_map_for_tests;
use tla_llvm2::runtime_abi::tla_ops::{
    clear_tla_arena, clear_tla_constant_pool, handle_from_value, handle_to_value,
    set_tla_constant_pool, TlaHandle, NIL_HANDLE,
};
use tla_value::value::Value;

/// Resolve a helper by name and transmute it to the given function type.
///
/// # Safety
///
/// Caller must ensure that `F` matches the registered helper's true
/// `extern "C"` signature. A mismatch is undefined behaviour.
unsafe fn lookup<F: Copy>(name: &str) -> F {
    let map = extern_symbol_map_for_tests();
    let addr = *map
        .get(name)
        .unwrap_or_else(|| panic!("missing extern symbol: {name}"));
    assert!(!addr.is_null(), "extern symbol {name} has null address");
    // SAFETY: caller guarantees F matches the registered signature.
    std::mem::transmute_copy::<*const u8, F>(&addr)
}

fn small_int_set(xs: &[i64]) -> TlaHandle {
    handle_from_value(&Value::set(
        xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>(),
    ))
}

// ---------------------------------------------------------------------------
// tla_load_const
// ---------------------------------------------------------------------------

#[test]
fn smoke_tla_load_const_empty_pool_returns_nil() {
    clear_tla_arena();
    clear_tla_constant_pool();
    type FnLoad = unsafe extern "C" fn(i64) -> TlaHandle;
    let f: FnLoad = unsafe { lookup("tla_load_const") };
    // Unwired pool → NIL (documented foundation behaviour).
    assert_eq!(unsafe { f(0) }, NIL_HANDLE);
    assert_eq!(unsafe { f(7) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_load_const_resolves_populated_pool() {
    clear_tla_arena();
    clear_tla_constant_pool();
    set_tla_constant_pool(vec![
        Value::SmallInt(21),
        Value::Bool(true),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]),
    ]);
    type FnLoad = unsafe extern "C" fn(i64) -> TlaHandle;
    let f: FnLoad = unsafe { lookup("tla_load_const") };

    let h0 = unsafe { f(0) };
    let h1 = unsafe { f(1) };
    let h2 = unsafe { f(2) };
    let h_oob = unsafe { f(99) };
    let h_neg = unsafe { f(-1) };

    assert_eq!(handle_to_value(h0), Value::SmallInt(21));
    assert_eq!(handle_to_value(h1), Value::Bool(true));
    assert_eq!(
        handle_to_value(h2),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)])
    );
    assert_eq!(h_oob, NIL_HANDLE);
    assert_eq!(h_neg, NIL_HANDLE);

    // Leave no pool residue for adjacent smoke tests.
    clear_tla_constant_pool();
}

// ---------------------------------------------------------------------------
// tla_cardinality
// ---------------------------------------------------------------------------

#[test]
fn smoke_tla_cardinality_matches_interpreter() {
    clear_tla_arena();
    type FnCard = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnCard = unsafe { lookup("tla_cardinality") };

    let empty = handle_from_value(&Value::empty_set());
    let five = small_int_set(&[1, 2, 3, 4, 5]);

    assert_eq!(handle_to_value(unsafe { f(empty) }), Value::SmallInt(0));
    assert_eq!(handle_to_value(unsafe { f(five) }), Value::SmallInt(5));
}

#[test]
fn smoke_tla_cardinality_non_set_returns_nil() {
    clear_tla_arena();
    type FnCard = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnCard = unsafe { lookup("tla_cardinality") };
    let not_a_set = handle_from_value(&Value::SmallInt(42));
    assert_eq!(unsafe { f(not_a_set) }, NIL_HANDLE);
}

// ---------------------------------------------------------------------------
// tla_is_finite_set
// ---------------------------------------------------------------------------

#[test]
fn smoke_tla_is_finite_set_matches_interpreter() {
    clear_tla_arena();
    type FnFin = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnFin = unsafe { lookup("tla_is_finite_set") };

    let literal = small_int_set(&[1, 2, 3]);
    assert_eq!(handle_to_value(unsafe { f(literal) }), Value::Bool(true));

    let string_set = handle_from_value(&Value::StringSet);
    assert_eq!(
        handle_to_value(unsafe { f(string_set) }),
        Value::Bool(false)
    );

    let non_set = handle_from_value(&Value::SmallInt(1));
    assert_eq!(handle_to_value(unsafe { f(non_set) }), Value::Bool(false));
}

// ---------------------------------------------------------------------------
// tla_tostring
// ---------------------------------------------------------------------------

#[test]
fn smoke_tla_tostring_matches_interpreter() {
    clear_tla_arena();
    type FnToStr = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnToStr = unsafe { lookup("tla_tostring") };

    for v in [
        Value::SmallInt(123),
        Value::Bool(false),
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(2)]),
    ] {
        let expected = format!("{v}");
        let h = handle_from_value(&v);
        let r = unsafe { f(h) };
        let Value::String(ref s) = handle_to_value(r) else {
            panic!("tla_tostring did not produce a string: {v:?}");
        };
        assert_eq!(s.as_ref(), expected.as_str());
    }
}
