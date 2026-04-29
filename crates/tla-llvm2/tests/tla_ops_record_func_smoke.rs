// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_record_get` / `tla_func_apply` /
//! `tla_domain` runtime FFI surface.
//!
//! Mirrors `tla_ops_set_smoke.rs`: each helper is resolved through the
//! extern symbol map the JIT linker will actually use, transmuted to its
//! `extern "C"` prototype, and invoked with `TlaHandle` operands produced
//! by `handle_from_value`. This guards against symbol-name mismatches and
//! ABI drift in the record/function family that the in-crate unit tests
//! cannot detect.
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI, §2.4).

#![cfg(feature = "native")]

use std::sync::Arc;

use tla_core::intern_name;
use tla_llvm2::extern_symbol_map_for_tests;
use tla_llvm2::runtime_abi::tla_ops::{
    clear_tla_arena, handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE,
};
use tla_value::value::{FuncBuilder, RecordValue, SeqValue, Value};

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

fn record_ab() -> Value {
    Value::Record(RecordValue::from_sorted_str_entries(vec![
        (Arc::from("a"), Value::SmallInt(1)),
        (Arc::from("b"), Value::Bool(true)),
    ]))
}

fn func_from_pairs(pairs: Vec<(Value, Value)>) -> Value {
    let mut b = FuncBuilder::new();
    for (k, v) in pairs {
        b.insert(k, v);
    }
    Value::Func(Arc::new(b.build()))
}

#[test]
fn smoke_tla_record_get_returns_field() {
    clear_tla_arena();
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let f: FnGet = unsafe { lookup("tla_record_get") };
    let rec = handle_from_value(&record_ab());
    let a_id = intern_name("a").0 as i64;
    let b_id = intern_name("b").0 as i64;
    assert_eq!(handle_to_value(unsafe { f(rec, a_id) }), Value::SmallInt(1));
    assert_eq!(handle_to_value(unsafe { f(rec, b_id) }), Value::Bool(true));
}

#[test]
fn smoke_tla_record_get_missing_field_is_nil() {
    clear_tla_arena();
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let f: FnGet = unsafe { lookup("tla_record_get") };
    let rec = handle_from_value(&record_ab());
    let missing = intern_name("not_a_field").0 as i64;
    assert_eq!(unsafe { f(rec, missing) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_record_get_on_non_record_is_nil() {
    clear_tla_arena();
    type FnGet = unsafe extern "C" fn(TlaHandle, i64) -> TlaHandle;
    let f: FnGet = unsafe { lookup("tla_record_get") };
    let not_rec = handle_from_value(&Value::SmallInt(42));
    let id = intern_name("a").0 as i64;
    assert_eq!(unsafe { f(not_rec, id) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_func_apply_on_func_matches_interpreter() {
    clear_tla_arena();
    type FnApply = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnApply = unsafe { lookup("tla_func_apply") };
    let fh = handle_from_value(&func_from_pairs(vec![
        (Value::SmallInt(1), Value::SmallInt(10)),
        (Value::SmallInt(2), Value::SmallInt(20)),
    ]));
    let arg = handle_from_value(&Value::SmallInt(2));
    assert_eq!(handle_to_value(unsafe { f(fh, arg) }), Value::SmallInt(20));
}

#[test]
fn smoke_tla_func_apply_on_seq_uses_one_based_indexing() {
    clear_tla_arena();
    type FnApply = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnApply = unsafe { lookup("tla_func_apply") };
    let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![
        Value::SmallInt(100),
        Value::SmallInt(200),
        Value::SmallInt(300),
    ])));
    let sh = handle_from_value(&seq);
    let one = handle_from_value(&Value::SmallInt(1));
    let three = handle_from_value(&Value::SmallInt(3));
    let out_of_bounds = handle_from_value(&Value::SmallInt(4));
    assert_eq!(handle_to_value(unsafe { f(sh, one) }), Value::SmallInt(100));
    assert_eq!(
        handle_to_value(unsafe { f(sh, three) }),
        Value::SmallInt(300)
    );
    assert_eq!(unsafe { f(sh, out_of_bounds) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_func_apply_on_record_with_string_key() {
    clear_tla_arena();
    type FnApply = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnApply = unsafe { lookup("tla_func_apply") };
    let rh = handle_from_value(&record_ab());
    let key = handle_from_value(&Value::String(Arc::from("a")));
    assert_eq!(handle_to_value(unsafe { f(rh, key) }), Value::SmallInt(1));
}

#[test]
fn smoke_tla_func_apply_on_non_function_is_nil() {
    clear_tla_arena();
    type FnApply = unsafe extern "C" fn(TlaHandle, TlaHandle) -> TlaHandle;
    let f: FnApply = unsafe { lookup("tla_func_apply") };
    let not_callable = handle_from_value(&Value::SmallInt(5));
    let arg = handle_from_value(&Value::SmallInt(1));
    assert_eq!(unsafe { f(not_callable, arg) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_domain_of_func_matches_interpreter() {
    clear_tla_arena();
    type FnDom = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnDom = unsafe { lookup("tla_domain") };
    let fh = handle_from_value(&func_from_pairs(vec![
        (Value::SmallInt(3), Value::SmallInt(30)),
        (Value::SmallInt(1), Value::SmallInt(10)),
        (Value::SmallInt(2), Value::SmallInt(20)),
    ]));
    let d = unsafe { f(fh) };
    let v = handle_to_value(d);
    let sorted = v.to_sorted_set().expect("func domain is enumerable");
    let vals: Vec<i64> = sorted.iter().filter_map(|x| x.as_i64()).collect();
    assert_eq!(vals, vec![1, 2, 3]);
}

#[test]
fn smoke_tla_domain_of_seq_is_one_through_len() {
    clear_tla_arena();
    type FnDom = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnDom = unsafe { lookup("tla_domain") };
    let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![
        Value::SmallInt(10),
        Value::SmallInt(20),
        Value::SmallInt(30),
    ])));
    let sh = handle_from_value(&seq);
    let d = unsafe { f(sh) };
    let v = handle_to_value(d);
    let sorted = v.to_sorted_set().expect("seq domain is enumerable");
    let vals: Vec<i64> = sorted.iter().filter_map(|x| x.as_i64()).collect();
    assert_eq!(vals, vec![1, 2, 3]);
}

#[test]
fn smoke_tla_domain_of_non_function_is_nil() {
    clear_tla_arena();
    type FnDom = unsafe extern "C" fn(TlaHandle) -> TlaHandle;
    let f: FnDom = unsafe { lookup("tla_domain") };
    let not_a_fn = handle_from_value(&Value::SmallInt(42));
    assert_eq!(unsafe { f(not_a_fn) }, NIL_HANDLE);
}
