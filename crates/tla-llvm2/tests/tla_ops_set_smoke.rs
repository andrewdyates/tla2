// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_set_*` runtime FFI surface.
//!
//! Unlike the in-crate unit tests in `runtime_abi::tla_ops::set::tests`,
//! this test exercises the helpers **through the extern symbol map** the
//! JIT linker will actually use. It:
//!
//! 1. Builds the extern symbol map via `extern_symbol_map_for_tests`.
//! 2. Transmutes each registered function pointer back to its `extern "C"`
//!    prototype.
//! 3. Calls the helper with `TlaHandle` operands produced by
//!    `handle_from_value`.
//! 4. Decodes the result with `handle_to_value` and asserts semantic
//!    parity with `tla_value::Value` APIs.
//!
//! The test catches two failure modes the unit tests cannot:
//! - **Symbol name mismatch**: a helper exported with one `#[no_mangle]`
//!   name but registered under a different name in `register_tla_ops_symbols`.
//! - **ABI mismatch**: a registered pointer whose Rust signature does not
//!   match the `extern "C"` shape the JIT emits a call for.
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI).

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

fn small_int_set(xs: &[i64]) -> TlaHandle {
    handle_from_value(&Value::set(
        xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>(),
    ))
}

fn decode_set_ints(h: TlaHandle) -> Vec<i64> {
    let v = handle_to_value(h);
    let sorted = v.to_sorted_set().expect("decoded handle should be a set");
    sorted.iter().filter_map(|e| e.as_i64()).collect()
}

#[test]
fn smoke_tla_set_enum_0_returns_empty_set() {
    clear_tla_arena();
    type Fn0 = unsafe extern "C" fn() -> TlaHandle;
    let f: Fn0 = unsafe { lookup("tla_set_enum_0") };
    let h = unsafe { f() };
    assert_eq!(handle_to_value(h), Value::empty_set());
}

#[test]
fn smoke_tla_set_enum_3_builds_literal() {
    clear_tla_arena();
    type Fn3 = unsafe extern "C" fn(TlaHandle, TlaHandle, TlaHandle) -> TlaHandle;
    let f: Fn3 = unsafe { lookup("tla_set_enum_3") };
    let a = handle_from_value(&Value::SmallInt(10));
    let b = handle_from_value(&Value::SmallInt(20));
    let c = handle_from_value(&Value::SmallInt(30));
    let h = unsafe { f(a, b, c) };
    assert_eq!(decode_set_ints(h), vec![10, 20, 30]);
}

#[test]
fn smoke_tla_set_union_matches_interpreter() {
    clear_tla_arena();
    type FnUnion = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnUnion = unsafe { lookup("tla_set_union") };
    let a = small_int_set(&[1, 2, 3]);
    let b = small_int_set(&[3, 4, 5]);
    let u = unsafe { f(a, b) };
    assert_eq!(decode_set_ints(u), vec![1, 2, 3, 4, 5]);
}

#[test]
fn smoke_tla_set_in_returns_one_zero_nil() {
    clear_tla_arena();
    type FnIn = unsafe extern "C" fn(TlaHandle, TlaHandle) -> i64;
    let f: FnIn = unsafe { lookup("tla_set_in") };
    let s = small_int_set(&[1, 3, 5, 7]);
    let elem_hit = handle_from_value(&Value::SmallInt(3));
    let elem_miss = handle_from_value(&Value::SmallInt(4));
    assert_eq!(unsafe { f(elem_hit, s) }, 1);
    assert_eq!(unsafe { f(elem_miss, s) }, 0);
    // Non-set operand → NIL.
    let not_a_set = handle_from_value(&Value::SmallInt(42));
    let r = unsafe { f(elem_hit, not_a_set) };
    assert_eq!(r, NIL_HANDLE);
}

#[test]
fn smoke_tla_set_subseteq_returns_one_zero() {
    clear_tla_arena();
    type FnSub = unsafe extern "C" fn(TlaHandle, TlaHandle) -> i64;
    let f: FnSub = unsafe { lookup("tla_set_subseteq") };
    let a = small_int_set(&[1, 2]);
    let b = small_int_set(&[1, 2, 3]);
    assert_eq!(unsafe { f(a, b) }, 1);
    assert_eq!(unsafe { f(b, a) }, 0);
}

#[test]
fn smoke_tla_set_range_produces_interval() {
    clear_tla_arena();
    type FnRange = unsafe extern "C" fn(i64, i64) -> TlaHandle;
    let f: FnRange = unsafe { lookup("tla_set_range") };
    let h = unsafe { f(2, 5) };
    assert_eq!(decode_set_ints(h), vec![2, 3, 4, 5]);
}

#[test]
fn smoke_tla_set_powerset_cardinality() {
    clear_tla_arena();
    type FnPow = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnPow = unsafe { lookup("tla_set_powerset") };
    let base = small_int_set(&[1, 2, 3]);
    let ps = unsafe { f(base) };
    let v = handle_to_value(ps);
    let sorted = v.to_sorted_set().expect("powerset is enumerable");
    assert_eq!(sorted.len(), 8);
}

#[test]
fn smoke_tla_handle_nil_returns_nil() {
    clear_tla_arena();
    type FnNil = unsafe extern "C" fn() -> TlaHandle;
    let f: FnNil = unsafe { lookup("tla_handle_nil") };
    let h = unsafe { f() };
    assert_eq!(h, NIL_HANDLE);
}

#[test]
fn smoke_clear_tla_arena_via_extern_entry_runs() {
    // Pure smoke: confirm the function pointer is callable and non-null.
    // The arena-clearing behaviour itself is exercised by the unit tests
    // in `runtime_abi::tla_ops::handle::tests`.
    type FnClear = unsafe extern "C" fn();
    let f: FnClear = unsafe { lookup("clear_tla_arena") };
    unsafe { f() };
}
