// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_seq_*` runtime FFI surface.
//!
//! Unlike the in-crate unit tests in `runtime_abi::tla_ops::seq::tests`,
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

fn int_seq(xs: &[i64]) -> TlaHandle {
    handle_from_value(&Value::seq(
        xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>(),
    ))
}

fn decode_seq_ints(h: TlaHandle) -> Vec<i64> {
    let v = handle_to_value(h);
    let elems = v
        .as_seq_or_tuple_elements()
        .expect("decoded handle should be a seq or tuple");
    elems.iter().filter_map(|e| e.as_i64()).collect()
}

#[test]
fn smoke_tla_seq_new_0_returns_empty_seq() {
    clear_tla_arena();
    type Fn0 = unsafe extern "C" fn() -> TlaHandle;
    let f: Fn0 = unsafe { lookup("tla_seq_new_0") };
    let h = unsafe { f() };
    assert_eq!(handle_to_value(h), Value::seq(Vec::<Value>::new()));
}

#[test]
fn smoke_tla_seq_new_3_builds_literal() {
    clear_tla_arena();
    type Fn3 = unsafe extern "C" fn(TlaHandle, TlaHandle, TlaHandle) -> TlaHandle;
    let f: Fn3 = unsafe { lookup("tla_seq_new_3") };
    let a = handle_from_value(&Value::SmallInt(10));
    let b = handle_from_value(&Value::SmallInt(20));
    let c = handle_from_value(&Value::SmallInt(30));
    let h = unsafe { f(a, b, c) };
    assert_eq!(decode_seq_ints(h), vec![10, 20, 30]);
}

#[test]
fn smoke_tla_seq_concat_matches_interpreter() {
    clear_tla_arena();
    type FnConcat = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnConcat = unsafe { lookup("tla_seq_concat") };
    let a = int_seq(&[1, 2, 3]);
    let b = int_seq(&[4, 5]);
    let c = unsafe { f(a, b) };
    assert_eq!(decode_seq_ints(c), vec![1, 2, 3, 4, 5]);
}

#[test]
fn smoke_tla_seq_len_returns_i64() {
    clear_tla_arena();
    type FnLen = unsafe extern "C" fn(TlaHandle) -> i64;
    let f: FnLen = unsafe { lookup("tla_seq_len") };
    assert_eq!(unsafe { f(int_seq(&[])) }, 0);
    assert_eq!(unsafe { f(int_seq(&[9, 8, 7, 6, 5])) }, 5);
    // Non-seq operand → NIL.
    let not_a_seq = handle_from_value(&Value::Bool(true));
    assert_eq!(unsafe { f(not_a_seq) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_seq_head_returns_first() {
    clear_tla_arena();
    type FnHead = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnHead = unsafe { lookup("tla_seq_head") };
    let s = int_seq(&[11, 22, 33]);
    let h = unsafe { f(s) };
    assert_eq!(handle_to_value(h), Value::SmallInt(11));
    // Empty → NIL.
    let empty = int_seq(&[]);
    assert_eq!(unsafe { f(empty) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_seq_tail_drops_first() {
    clear_tla_arena();
    type FnTail = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnTail = unsafe { lookup("tla_seq_tail") };
    let s = int_seq(&[1, 2, 3, 4]);
    let t = unsafe { f(s) };
    assert_eq!(decode_seq_ints(t), vec![2, 3, 4]);
    // Empty → NIL.
    let empty = int_seq(&[]);
    assert_eq!(unsafe { f(empty) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_seq_append_adds_at_end() {
    clear_tla_arena();
    type FnAppend = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnAppend = unsafe { lookup("tla_seq_append") };
    let s = int_seq(&[1, 2, 3]);
    let x = handle_from_value(&Value::SmallInt(99));
    let a = unsafe { f(s, x) };
    assert_eq!(decode_seq_ints(a), vec![1, 2, 3, 99]);
}

#[test]
fn smoke_tla_seq_subseq_slices_1_indexed() {
    clear_tla_arena();
    type FnSubseq = unsafe extern "C" fn(TlaHandle, i64, i64) -> TlaHandle;
    let f: FnSubseq = unsafe { lookup("tla_seq_subseq") };
    let s = int_seq(&[10, 20, 30, 40, 50]);
    // SubSeq(s, 2, 4) = <<20, 30, 40>>
    let sub = unsafe { f(s, 2, 4) };
    assert_eq!(decode_seq_ints(sub), vec![20, 30, 40]);
}

#[test]
fn smoke_tla_seq_set_returns_seqset() {
    clear_tla_arena();
    type FnSeqSet = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnSeqSet = unsafe { lookup("tla_seq_set") };
    let base = handle_from_value(&Value::set(vec![Value::SmallInt(0), Value::SmallInt(1)]));
    let h = unsafe { f(base) };
    let v = handle_to_value(h);
    assert!(
        matches!(v, Value::SeqSet(_)),
        "tla_seq_set should produce a lazy SeqSet"
    );
}
