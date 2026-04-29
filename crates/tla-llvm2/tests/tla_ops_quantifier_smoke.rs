// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end smoke test for the `tla_quantifier_*` runtime FFI surface.
//!
//! Mirrors `tla_ops_set_smoke.rs` but for the quantifier iterator
//! helpers introduced by §2.6 of the R27 Option B design
//! (`designs/2026-04-20-llvm2-runtime-abi-scope.md`). The test
//! resolves each helper through `extern_symbol_map_for_tests`, transmutes
//! the raw pointer back to its `extern "C"` prototype, exercises it
//! with `TlaHandle` operands, and asserts semantic parity with
//! `tla_value::Value::iter_set` (the interpreter iteration order —
//! §7.1 R2 soundness contract).
//!
//! The four helpers exercised here:
//!
//! | Symbol | Rust signature |
//! |---|---|
//! | `tla_quantifier_iter_new` | `extern "C" fn(TlaHandle) -> i64` |
//! | `tla_quantifier_iter_done` | `extern "C" fn(i64) -> i64` |
//! | `tla_quantifier_iter_next` | `extern "C" fn(i64) -> TlaHandle` |
//! | `tla_quantifier_runtime_error` | `extern "C" fn() -> !` (NOT invoked — aborts) |
//!
//! `tla_quantifier_runtime_error` is NOT exercised dynamically: calling
//! it terminates the test process. We only confirm the symbol is
//! registered and non-null (same treatment the unit tests give it).
//!
//! Part of #4318 (R27 Option B handle-based runtime ABI).

#![cfg(feature = "native")]

use tla_llvm2::extern_symbol_map_for_tests;
use tla_llvm2::runtime_abi::tla_ops::{
    clear_tla_arena, clear_tla_iter_arena, handle_from_value, handle_to_value, TlaHandle,
    NIL_HANDLE,
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

fn fresh() {
    clear_tla_arena();
    clear_tla_iter_arena();
}

type FnNew = unsafe extern "C" fn(TlaHandle) -> i64;
type FnDone = unsafe extern "C" fn(i64) -> i64;
type FnNext = unsafe extern "C" fn(i64) -> TlaHandle;

#[test]
fn smoke_tla_quantifier_iter_yields_sorted_order_1357() {
    // §7.1 R2: the compiled-path iteration order must match
    // `Value::iter_set` (sorted normalized slice) for {1, 3, 5, 7}.
    fresh();
    let f_new: FnNew = unsafe { lookup("tla_quantifier_iter_new") };
    let f_done: FnDone = unsafe { lookup("tla_quantifier_iter_done") };
    let f_next: FnNext = unsafe { lookup("tla_quantifier_iter_next") };

    let set_h = small_int_set(&[7, 3, 5, 1]);
    let iter = unsafe { f_new(set_h) };

    let mut yielded: Vec<i64> = Vec::new();
    let mut guard = 0;
    while unsafe { f_done(iter) } == 0 {
        let h = unsafe { f_next(iter) };
        yielded.push(handle_to_value(h).as_i64().expect("int"));
        guard += 1;
        assert!(guard < 1024, "iterator ran away");
    }
    assert_eq!(yielded, vec![1, 3, 5, 7]);
}

#[test]
fn smoke_tla_quantifier_iter_matches_interpreter_iter_set() {
    // Direct parity check: interpreter-produced iteration order must
    // equal the compiled-helper sequence element-for-element.
    fresh();
    let f_new: FnNew = unsafe { lookup("tla_quantifier_iter_new") };
    let f_done: FnDone = unsafe { lookup("tla_quantifier_iter_done") };
    let f_next: FnNext = unsafe { lookup("tla_quantifier_iter_next") };

    let input = Value::set(vec![
        Value::SmallInt(7),
        Value::SmallInt(3),
        Value::SmallInt(5),
        Value::SmallInt(1),
    ]);
    let interpreter: Vec<Value> = input.iter_set().expect("set is enumerable").collect();

    let h = handle_from_value(&input);
    let iter = unsafe { f_new(h) };
    let mut compiled: Vec<Value> = Vec::new();
    while unsafe { f_done(iter) } == 0 {
        compiled.push(handle_to_value(unsafe { f_next(iter) }));
    }
    assert_eq!(compiled, interpreter);
}

#[test]
fn smoke_tla_quantifier_iter_on_empty_set_is_done_immediately() {
    fresh();
    let f_new: FnNew = unsafe { lookup("tla_quantifier_iter_new") };
    let f_done: FnDone = unsafe { lookup("tla_quantifier_iter_done") };
    let empty = handle_from_value(&Value::empty_set());
    let iter = unsafe { f_new(empty) };
    assert_eq!(unsafe { f_done(iter) }, 1);
}

#[test]
fn smoke_tla_quantifier_iter_on_non_set_is_done_immediately() {
    // A scalar operand is not a set. The helper must fall back to an
    // empty iterator so tir_lower's CHOOSE-runtime-error / vacuous-forall
    // / false-exists branches take the empty-domain path.
    fresh();
    let f_new: FnNew = unsafe { lookup("tla_quantifier_iter_new") };
    let f_done: FnDone = unsafe { lookup("tla_quantifier_iter_done") };
    let f_next: FnNext = unsafe { lookup("tla_quantifier_iter_next") };

    let not_a_set = handle_from_value(&Value::SmallInt(42));
    let iter = unsafe { f_new(not_a_set) };
    assert_eq!(unsafe { f_done(iter) }, 1);
    assert_eq!(unsafe { f_next(iter) }, NIL_HANDLE);
}

#[test]
fn smoke_tla_quantifier_iter_over_interval() {
    // Intervals are LazySet values — to_sorted_set() materialises them
    // in numeric order.
    fresh();
    let f_new: FnNew = unsafe { lookup("tla_quantifier_iter_new") };
    let f_done: FnDone = unsafe { lookup("tla_quantifier_iter_done") };
    let f_next: FnNext = unsafe { lookup("tla_quantifier_iter_next") };

    use num_bigint::BigInt;
    use tla_value::value::range_set;
    let lazy = range_set(&BigInt::from(3), &BigInt::from(6));
    let h = handle_from_value(&lazy);
    let iter = unsafe { f_new(h) };
    let mut ys: Vec<i64> = Vec::new();
    while unsafe { f_done(iter) } == 0 {
        ys.push(handle_to_value(unsafe { f_next(iter) }).as_i64().unwrap());
    }
    assert_eq!(ys, vec![3, 4, 5, 6]);
}

#[test]
fn smoke_tla_quantifier_runtime_error_symbol_registered() {
    // We deliberately DO NOT call the helper — it aborts the process.
    // The test only asserts the symbol is resolvable and non-null so
    // the JIT linker will find it at compile time.
    let map = extern_symbol_map_for_tests();
    let addr = map
        .get("tla_quantifier_runtime_error")
        .expect("missing extern symbol: tla_quantifier_runtime_error");
    assert!(
        !addr.is_null(),
        "tla_quantifier_runtime_error has null address"
    );
}
