// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_load_const` + builtin helpers — Option B foundation (R27, #4318).
//!
//! This module exposes four `#[no_mangle] pub extern "C"` helpers that
//! `tir_lower.rs` emits `call i64 @<sym>(...)` for:
//!
//! | Symbol | Signature | Semantics |
//! |--------|-----------|-----------|
//! | [`tla_load_const`] | `i64 (i64 idx)` | Lookup by index into per-worker pool |
//! | [`tla_cardinality`] | `i64 (i64 s)` | `Cardinality(s)` — returns INT handle |
//! | [`tla_is_finite_set`] | `i64 (i64 s)` | `IsFiniteSet(s)` — returns BOOL handle |
//! | [`tla_tostring`] | `i64 (i64 v)` | `ToString(v)` — returns STRING handle |
//!
//! # Soundness contract
//!
//! All four helpers follow the [`super::handle`] pattern — they unbox the
//! operand via [`handle_to_value`], call into `tla_value::Value`, and rebox
//! via [`handle_from_value`]. Error / "cannot compute" paths return
//! [`NIL_HANDLE`] so `tir_lower` can fall back to the interpreter.
//!
//! # Constant pool
//!
//! `tla_load_const(idx)` needs a per-worker-thread constant pool populated
//! by the BFS driver before JIT dispatch. tMIR already resolves
//! compile-time-scalar constants (`SmallInt`/`Bool`/`String`) directly via
//! [`tla_tmir::lower::constants`]; the remaining `LoadConst` calls that
//! survive to LLVM2 are compound constants (pre-materialised sets,
//! sequences, records, tuples). Those must be surfaced to the runtime.
//!
//! This foundation MVP ships the thread-local pool plus
//! [`set_tla_constant_pool`] / [`clear_tla_constant_pool`] hooks. The
//! BFS driver / compile wiring in `tir_lower.rs` → `compile.rs` will pre-load
//! the pool before each JIT call in a follow-up slice. Until that wiring
//! lands, `tla_load_const` returns [`NIL_HANDLE`] when the pool is empty or
//! the index is out of range — which `tir_lower` treats as "fall back to
//! interpreter", preserving correctness.
//!
//! Part of #4318.

use std::cell::RefCell;

use tla_value::intern_string;
use tla_value::value::Value;

use super::handle::{handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE};

// ============================================================================
// Per-worker constant pool (thread-local)
// ============================================================================
//
// The pool is a `RefCell<Vec<Value>>` — cheap to swap in from the compile
// driver via [`set_tla_constant_pool`] before dispatching a JIT-compiled
// action, and cleared via [`clear_tla_constant_pool`] at shutdown. Indices
// match `tla_tir::bytecode::ConstantPool::get_value` so compile-time
// `LoadConst { idx }` and runtime `tla_load_const(idx)` agree on addressing.

thread_local! {
    /// Per-worker constant pool backing [`tla_load_const`]. Populated by
    /// the BFS driver before dispatching a JIT-compiled function.
    static TLA_CONSTANT_POOL: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) };
}

/// Install a constant pool for the current worker.
///
/// Replaces any pool previously set on this thread. The caller owns the
/// pool contents — the runtime clones values into its own storage so the
/// caller's lifetime is irrelevant.
///
/// This is the wiring hook expected by `compile.rs` / the BFS driver.
/// Until the driver is updated (follow-up slice of #4318), the pool
/// remains empty and [`tla_load_const`] returns [`NIL_HANDLE`], which
/// `tir_lower` treats as "fall back to interpreter".
pub fn set_tla_constant_pool(values: Vec<Value>) {
    TLA_CONSTANT_POOL.with(|cell| {
        *cell.borrow_mut() = values;
    });
}

/// Drop the per-worker constant pool. Safe to call on a cold worker.
pub fn clear_tla_constant_pool() {
    TLA_CONSTANT_POOL.with(|cell| cell.borrow_mut().clear());
}

/// Number of constants currently loaded on this worker. Debug helper.
#[cfg(test)]
pub(crate) fn constant_pool_len() -> usize {
    TLA_CONSTANT_POOL.with(|cell| cell.borrow().len())
}

// ============================================================================
// tla_load_const — constant pool lookup
// ============================================================================

/// Load the constant at index `idx` into a [`TlaHandle`].
///
/// tMIR already resolves compile-time-scalar constants (`SmallInt`,
/// `Bool`, `String`, `ModelValue`, small `Interval`) directly in
/// `tla_tmir::lower::constants`. This runtime helper services the
/// remaining `LoadConst` calls — compound constants (general `Set`,
/// `Seq`, `Record`, `Tuple`, `FuncVal`, etc.) that survive to LLVM2.
///
/// Returns [`NIL_HANDLE`] when:
/// - The pool has not been populated on this worker (foundation MVP),
/// - `idx` is negative (malformed caller), or
/// - `idx` is out of range for the currently installed pool.
///
/// `tir_lower`'s contract for `NIL_HANDLE` is "fall back to interpreter",
/// so both the unwired and error paths preserve correctness.
#[no_mangle]
pub extern "C" fn tla_load_const(idx: i64) -> TlaHandle {
    if idx < 0 {
        return NIL_HANDLE;
    }
    let Ok(idx_usize) = usize::try_from(idx) else {
        return NIL_HANDLE;
    };
    TLA_CONSTANT_POOL.with(|cell| {
        let pool = cell.borrow();
        match pool.get(idx_usize) {
            Some(v) => handle_from_value(v),
            None => NIL_HANDLE,
        }
    })
}

// ============================================================================
// tla_cardinality — Cardinality(s)
// ============================================================================

/// `Cardinality(s)` — returns a handle encoding the set's size as INT.
///
/// Maps to `Value::set_len` (which returns `Option<BigInt>`). The INT
/// handle is produced via [`handle_from_value`] so i61-range results stay
/// inline and overflows box into the arena.
///
/// Falls through to [`NIL_HANDLE`] when the operand is not an enumerable
/// set (e.g. `SetPred` without eval context, infinite `StringSet`).
#[no_mangle]
pub extern "C" fn tla_cardinality(s: TlaHandle) -> TlaHandle {
    let v = handle_to_value(s);
    match v.set_len() {
        Some(n) => handle_from_value(&Value::big_int(n)),
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_is_finite_set — IsFiniteSet(s)
// ============================================================================

/// `IsFiniteSet(s)` — returns a BOOL handle (1 = finite, 0 = infinite or
/// non-set).
///
/// Delegates to [`Value::is_finite_set`], which matches TLC's recursive
/// `isFinite()` semantics (#1508). Never returns [`NIL_HANDLE`] — the
/// predicate is total over all `Value` variants.
#[no_mangle]
pub extern "C" fn tla_is_finite_set(s: TlaHandle) -> TlaHandle {
    let v = handle_to_value(s);
    handle_from_value(&Value::Bool(v.is_finite_set()))
}

// ============================================================================
// tla_tostring — ToString(v)
// ============================================================================

/// `ToString(v)` — returns a STRING handle containing the formatted
/// representation of `v`.
///
/// Mirrors the interpreter's implementation in
/// `tla_eval::bytecode_vm::execute_compound::BuiltinOp::ToString`:
/// `Value::String(intern_string(&format!("{v}")))`. `handle_from_value`
/// then maps the interned [`tla_core::NameId`] into the inline
/// `H_TAG_STRING` handle without touching the arena.
#[no_mangle]
pub extern "C" fn tla_tostring(v: TlaHandle) -> TlaHandle {
    let value = handle_to_value(v);
    let formatted = format!("{value}");
    let interned = intern_string(&formatted);
    handle_from_value(&Value::String(interned))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::{clear_tla_arena, H_TAG_BOOL, H_TAG_INT, H_TAG_STRING};
    use super::*;
    use num_bigint::BigInt;
    use std::sync::Arc;
    use tla_value::value::{SortedSet, Value};

    fn small_int_set(xs: &[i64]) -> Value {
        Value::set(xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>())
    }

    // ------------------------------------------------------------------
    // tla_load_const
    // ------------------------------------------------------------------

    #[test]
    fn load_const_empty_pool_returns_nil() {
        clear_tla_arena();
        clear_tla_constant_pool();
        assert_eq!(tla_load_const(0), NIL_HANDLE);
        assert_eq!(tla_load_const(42), NIL_HANDLE);
    }

    #[test]
    fn load_const_negative_index_returns_nil() {
        clear_tla_arena();
        clear_tla_constant_pool();
        set_tla_constant_pool(vec![Value::SmallInt(7)]);
        assert_eq!(tla_load_const(-1), NIL_HANDLE);
        assert_eq!(tla_load_const(i64::MIN), NIL_HANDLE);
    }

    #[test]
    fn load_const_out_of_range_returns_nil() {
        clear_tla_arena();
        clear_tla_constant_pool();
        set_tla_constant_pool(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        assert_eq!(tla_load_const(2), NIL_HANDLE);
        assert_eq!(tla_load_const(1000), NIL_HANDLE);
    }

    #[test]
    fn load_const_scalar_roundtrips_inline() {
        clear_tla_arena();
        clear_tla_constant_pool();
        set_tla_constant_pool(vec![
            Value::SmallInt(11),
            Value::Bool(true),
            Value::SmallInt(-5),
        ]);
        assert_eq!(constant_pool_len(), 3);

        let h0 = tla_load_const(0);
        let h1 = tla_load_const(1);
        let h2 = tla_load_const(2);
        assert_eq!(handle_to_value(h0), Value::SmallInt(11));
        assert_eq!(handle_to_value(h1), Value::Bool(true));
        assert_eq!(handle_to_value(h2), Value::SmallInt(-5));
    }

    #[test]
    fn load_const_compound_boxes_to_arena() {
        clear_tla_arena();
        clear_tla_constant_pool();
        let set = small_int_set(&[1, 2, 3]);
        set_tla_constant_pool(vec![set.clone()]);
        let h = tla_load_const(0);
        assert_eq!(handle_to_value(h), set);
    }

    #[test]
    fn set_tla_constant_pool_replaces_previous() {
        clear_tla_arena();
        clear_tla_constant_pool();
        set_tla_constant_pool(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        assert_eq!(constant_pool_len(), 2);
        set_tla_constant_pool(vec![Value::SmallInt(99)]);
        assert_eq!(constant_pool_len(), 1);
        assert_eq!(handle_to_value(tla_load_const(0)), Value::SmallInt(99));
        assert_eq!(tla_load_const(1), NIL_HANDLE);
    }

    // ------------------------------------------------------------------
    // tla_cardinality
    // ------------------------------------------------------------------

    #[test]
    fn cardinality_empty_set_is_zero() {
        clear_tla_arena();
        let h = handle_from_value(&Value::empty_set());
        let card = tla_cardinality(h);
        assert_eq!(handle_to_value(card), Value::SmallInt(0));
    }

    #[test]
    fn cardinality_literal_set_matches_interpreter() {
        clear_tla_arena();
        for xs in [
            vec![],
            vec![42],
            vec![1, 2, 3],
            vec![5, 5, 5, 5], // dedupes to one element
            vec![1, 3, 5, 7, 9, 11],
        ] {
            let v = small_int_set(&xs);
            let expected = v.set_len().expect("literal set is enumerable");
            let h = handle_from_value(&v);
            let card = tla_cardinality(h);
            assert_eq!(
                handle_to_value(card),
                Value::big_int(expected),
                "cardinality({xs:?})"
            );
        }
    }

    #[test]
    fn cardinality_interval_matches_interpreter() {
        clear_tla_arena();
        use tla_value::value::range_set;
        // 2..7 = {2,3,4,5,6,7} → |.| = 6
        let v = range_set(&BigInt::from(2), &BigInt::from(7));
        let h = handle_from_value(&v);
        let card = tla_cardinality(h);
        assert_eq!(handle_to_value(card), Value::SmallInt(6));
    }

    #[test]
    fn cardinality_non_set_returns_nil() {
        clear_tla_arena();
        let h = handle_from_value(&Value::SmallInt(7));
        assert_eq!(tla_cardinality(h), NIL_HANDLE);
    }

    #[test]
    fn cardinality_returns_int_tag() {
        clear_tla_arena();
        let h = handle_from_value(&small_int_set(&[1, 2, 3, 4, 5]));
        let card = tla_cardinality(h);
        // Result should be an inline i64 (H_TAG_INT), not boxed.
        assert_eq!(card & super::super::handle::HANDLE_TAG_MASK, H_TAG_INT);
    }

    // ------------------------------------------------------------------
    // tla_is_finite_set
    // ------------------------------------------------------------------

    #[test]
    fn is_finite_set_literal_set_is_true() {
        clear_tla_arena();
        let h = handle_from_value(&small_int_set(&[1, 2, 3]));
        let r = tla_is_finite_set(h);
        assert_eq!(r & super::super::handle::HANDLE_TAG_MASK, H_TAG_BOOL);
        assert_eq!(handle_to_value(r), Value::Bool(true));
    }

    #[test]
    fn is_finite_set_empty_set_is_true() {
        clear_tla_arena();
        let h = handle_from_value(&Value::empty_set());
        assert_eq!(handle_to_value(tla_is_finite_set(h)), Value::Bool(true));
    }

    #[test]
    fn is_finite_set_nat_is_false() {
        clear_tla_arena();
        let nat = Value::ModelValue(Arc::from("Nat"));
        let h = handle_from_value(&nat);
        assert_eq!(handle_to_value(tla_is_finite_set(h)), Value::Bool(false));
    }

    #[test]
    fn is_finite_set_string_set_is_false() {
        clear_tla_arena();
        let h = handle_from_value(&Value::StringSet);
        assert_eq!(handle_to_value(tla_is_finite_set(h)), Value::Bool(false));
    }

    #[test]
    fn is_finite_set_non_set_is_false() {
        // Per Value::is_finite_set: non-set values return false.
        clear_tla_arena();
        let h = handle_from_value(&Value::SmallInt(123));
        assert_eq!(handle_to_value(tla_is_finite_set(h)), Value::Bool(false));
    }

    #[test]
    fn is_finite_set_interval_is_true() {
        clear_tla_arena();
        use tla_value::value::range_set;
        let v = range_set(&BigInt::from(1), &BigInt::from(10));
        let h = handle_from_value(&v);
        assert_eq!(handle_to_value(tla_is_finite_set(h)), Value::Bool(true));
    }

    // ------------------------------------------------------------------
    // tla_tostring
    // ------------------------------------------------------------------

    #[test]
    fn tostring_int_matches_interpreter() {
        clear_tla_arena();
        let v = Value::SmallInt(42);
        let expected = format!("{v}");
        let h = handle_from_value(&v);
        let r = tla_tostring(h);
        assert_eq!(r & super::super::handle::HANDLE_TAG_MASK, H_TAG_STRING);
        let Value::String(ref s) = handle_to_value(r) else {
            panic!("expected Value::String");
        };
        assert_eq!(s.as_ref(), expected.as_str());
    }

    #[test]
    fn tostring_bool_matches_interpreter() {
        clear_tla_arena();
        for b in [false, true] {
            let v = Value::Bool(b);
            let expected = format!("{v}");
            let h = handle_from_value(&v);
            let r = tla_tostring(h);
            let Value::String(ref s) = handle_to_value(r) else {
                panic!("expected Value::String");
            };
            assert_eq!(s.as_ref(), expected.as_str());
        }
    }

    #[test]
    fn tostring_set_matches_interpreter() {
        clear_tla_arena();
        let v = small_int_set(&[1, 2, 3]);
        let expected = format!("{v}");
        let h = handle_from_value(&v);
        let r = tla_tostring(h);
        let Value::String(ref s) = handle_to_value(r) else {
            panic!("expected Value::String");
        };
        assert_eq!(s.as_ref(), expected.as_str());
    }

    #[test]
    fn tostring_roundtrips_via_handle_shape() {
        clear_tla_arena();
        // Double-apply ToString — the second call should yield
        // ToString("<first_output>") which is "\"<first_output>\"".
        let v = Value::SmallInt(7);
        let h = handle_from_value(&v);
        let r1 = tla_tostring(h);
        let r2 = tla_tostring(r1);
        // r2 should be a well-formed STRING handle.
        assert_eq!(r2 & super::super::handle::HANDLE_TAG_MASK, H_TAG_STRING);
        let Value::String(_) = handle_to_value(r2) else {
            panic!("expected Value::String");
        };
    }

    #[test]
    fn tostring_preserves_set_content() {
        // Equivalent sets must format identically (relies on SortedSet
        // canonicalization).
        clear_tla_arena();
        let a = Value::Set(Arc::new(SortedSet::from_vec(vec![
            Value::SmallInt(3),
            Value::SmallInt(1),
            Value::SmallInt(2),
        ])));
        let b = small_int_set(&[1, 2, 3]);
        let s_a = handle_to_value(tla_tostring(handle_from_value(&a)));
        let s_b = handle_to_value(tla_tostring(handle_from_value(&b)));
        assert_eq!(s_a, s_b);
    }
}
