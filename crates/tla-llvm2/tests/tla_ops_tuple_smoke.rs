// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_tuple_*` runtime FFI surface.
//!
//! Mirrors `tla_ops_set_smoke.rs`: exercises each tuple helper **through
//! the extern symbol map** the JIT linker will actually use, catching
//! symbol-name and ABI mismatches that pure in-crate unit tests cannot.
//!
//! 1. Builds the extern symbol map via `extern_symbol_map_for_tests`.
//! 2. Transmutes each registered function pointer back to its `extern "C"`
//!    prototype.
//! 3. Calls the helper with `TlaHandle` operands produced by
//!    `handle_from_value`.
//! 4. Decodes the result with `handle_to_value` and asserts semantic
//!    parity with `tla_value::Value` APIs.
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI — tuple family).

#![cfg(feature = "native")]

use tla_llvm2::extern_symbol_map_for_tests;
use tla_llvm2::runtime_abi::tla_ops::{
    clear_tla_arena, handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE,
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

fn int_handle(n: i64) -> TlaHandle {
    handle_from_value(&Value::SmallInt(n))
}

#[test]
fn smoke_tla_tuple_new_0_returns_empty_tuple() {
    clear_tla_arena();
    type Fn0 = unsafe extern "C" fn() -> TlaHandle;
    let f: Fn0 = unsafe { lookup("tla_tuple_new_0") };
    let h = unsafe { f() };
    let v = handle_to_value(h);
    let elems = v.as_tuple().expect("result should be a tuple");
    assert_eq!(elems.len(), 0);
}

#[test]
fn smoke_tla_tuple_new_3_preserves_order() {
    clear_tla_arena();
    type Fn3 = unsafe extern "C" fn(TlaHandle, TlaHandle, TlaHandle) -> TlaHandle;
    let f: Fn3 = unsafe { lookup("tla_tuple_new_3") };
    let a = int_handle(10);
    let b = int_handle(20);
    let c = int_handle(30);
    let h = unsafe { f(a, b, c) };
    let v = handle_to_value(h);
    let elems = v.as_tuple().expect("result should be a tuple");
    assert_eq!(elems.len(), 3);
    assert_eq!(elems[0], Value::SmallInt(10));
    assert_eq!(elems[1], Value::SmallInt(20));
    assert_eq!(elems[2], Value::SmallInt(30));
}

#[test]
fn smoke_tla_tuple_new_8_full_width() {
    clear_tla_arena();
    type Fn8 = unsafe extern "C" fn(
        TlaHandle,
        TlaHandle,
        TlaHandle,
        TlaHandle,
        TlaHandle,
        TlaHandle,
        TlaHandle,
        TlaHandle,
    ) -> TlaHandle;
    let f: Fn8 = unsafe { lookup("tla_tuple_new_8") };
    let handles: [TlaHandle; 8] = [
        int_handle(1),
        int_handle(2),
        int_handle(3),
        int_handle(4),
        int_handle(5),
        int_handle(6),
        int_handle(7),
        int_handle(8),
    ];
    let h = unsafe {
        f(
            handles[0], handles[1], handles[2], handles[3], handles[4], handles[5], handles[6],
            handles[7],
        )
    };
    let v = handle_to_value(h);
    let elems = v.as_tuple().expect("result should be a tuple");
    assert_eq!(elems.len(), 8);
    for (i, e) in elems.iter().enumerate() {
        assert_eq!(*e, Value::SmallInt((i + 1) as i64));
    }
}

#[test]
fn smoke_tla_tuple_get_1_indexed() {
    clear_tla_arena();
    type FnNew3 = unsafe extern "C" fn(TlaHandle, TlaHandle, TlaHandle) -> TlaHandle;
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let new3: FnNew3 = unsafe { lookup("tla_tuple_new_3") };
    let get: FnGet = unsafe { lookup("tla_tuple_get") };

    let tup = unsafe { new3(int_handle(100), int_handle(200), int_handle(300)) };
    assert_eq!(handle_to_value(unsafe { get(tup, 1) }), Value::SmallInt(100));
    assert_eq!(handle_to_value(unsafe { get(tup, 2) }), Value::SmallInt(200));
    assert_eq!(handle_to_value(unsafe { get(tup, 3) }), Value::SmallInt(300));
}

#[test]
fn smoke_tla_tuple_get_out_of_range_returns_nil() {
    clear_tla_arena();
    type FnNew2 = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let new2: FnNew2 = unsafe { lookup("tla_tuple_new_2") };
    let get: FnGet = unsafe { lookup("tla_tuple_get") };

    let tup = unsafe { new2(int_handle(10), int_handle(20)) };
    // TLA+ is 1-indexed — idx=0, idx=3 and negatives are all out of range.
    assert_eq!(unsafe { get(tup, 0) }, NIL_HANDLE);
    assert_eq!(unsafe { get(tup, -1) }, NIL_HANDLE);
    assert_eq!(unsafe { get(tup, 3) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_tuple_get_on_non_tuple_returns_nil() {
    clear_tla_arena();
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let get: FnGet = unsafe { lookup("tla_tuple_get") };
    let not_a_tuple = int_handle(7);
    assert_eq!(unsafe { get(not_a_tuple, 1) }, NIL_HANDLE);
}
