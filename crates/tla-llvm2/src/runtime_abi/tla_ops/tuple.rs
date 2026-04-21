// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_tuple_*` runtime helpers — handle-based FFI for TLA+ tuple ops.
//!
//! Exposes the 9 monomorphic `tla_tuple_new_N` constructors (N = 0..=8)
//! plus `tla_tuple_get` for 1-indexed element access. Every helper is a
//! thin wrapper around [`Value::tuple`] / tuple indexing so semantic
//! parity with the interpreter is inherited by construction.
//!
//! | Helper | Mapping |
//! |--------|---------|
//! | `tla_tuple_new_N` | `Value::tuple([h_1, …, h_N].map(handle_to_value))` |
//! | `tla_tuple_get` | `tup[idx]` (1-indexed per TLA+) via `Value::Tuple` |
//!
//! # Encoding rationale
//!
//! The N-arity monomorphs avoid a variadic FFI shim for spec-declared
//! tuple literals `<<e_1, …, e_N>>`. `tir_lower` emits
//! `tla_tuple_new_N` for N <= 8 and falls back to the interpreter (or a
//! variadic helper added later) for larger literals.
//!
//! `tla_tuple_get` takes the index as a raw `i64` (not a handle) because
//! tuple indices are always integer literals in TLA+ bytecode emit
//! sites — TIR surfaces them as `IntLit` constants already lowered to
//! i64 scalars. Mirrors the rationale used by `tla_set_range` and
//! `tla_set_ksubset`.
//!
//! # Soundness contract
//!
//! - Helpers that cannot compute their result (index out of bounds,
//!   non-tuple operand) return [`NIL_HANDLE`]. `tir_lower` emits a
//!   guard that falls back to the interpreter on NIL. This keeps the
//!   FFI surface panic-free without silently corrupting results.
//! - The caller must [`clear_tla_arena`](super::handle::clear_tla_arena)
//!   at action boundaries; otherwise arena handles accumulate.
//!
//! Part of #4318.

use tla_value::value::Value;

use super::handle::{handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE};

// ============================================================================
// tla_tuple_new_N (N = 0..=8) — build a literal tuple from N element handles
// ============================================================================

/// `<<>>` — the empty tuple.
#[no_mangle]
pub extern "C" fn tla_tuple_new_0() -> TlaHandle {
    handle_from_value(&Value::tuple(std::iter::empty::<Value>()))
}

/// `<<e_1>>` — one-element tuple.
#[no_mangle]
pub extern "C" fn tla_tuple_new_1(h0: TlaHandle) -> TlaHandle {
    tuple_new_from_handles(&[h0])
}

/// `<<e_1, e_2>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_2(h0: TlaHandle, h1: TlaHandle) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1])
}

/// `<<e_1, e_2, e_3>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_3(h0: TlaHandle, h1: TlaHandle, h2: TlaHandle) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2])
}

/// `<<e_1, …, e_4>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_4(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2, h3])
}

/// `<<e_1, …, e_5>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_5(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2, h3, h4])
}

/// `<<e_1, …, e_6>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_6(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2, h3, h4, h5])
}

/// `<<e_1, …, e_7>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_7(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2, h3, h4, h5, h6])
}

/// `<<e_1, …, e_8>>`.
#[no_mangle]
pub extern "C" fn tla_tuple_new_8(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
    h7: TlaHandle,
) -> TlaHandle {
    tuple_new_from_handles(&[h0, h1, h2, h3, h4, h5, h6, h7])
}

#[inline]
fn tuple_new_from_handles(handles: &[TlaHandle]) -> TlaHandle {
    let values: Vec<Value> = handles.iter().copied().map(handle_to_value).collect();
    handle_from_value(&Value::tuple(values))
}

// ============================================================================
// tla_tuple_get — 1-indexed element access
// ============================================================================

/// `tup[idx]` — returns the element handle at 1-indexed position `idx`.
///
/// Returns [`NIL_HANDLE`] if:
/// - `tup` is not a `Value::Tuple` (e.g. scalar or other compound type),
/// - `idx` is out of bounds (`idx < 1` or `idx > len`).
///
/// The NIL result lets `tir_lower` fall back to the full interpreter path
/// for non-tuple aggregates (Seq / Func / Record / IntFunc), which share
/// the TLA+ `f[x]` syntax but have distinct indexing semantics.
///
/// `idx` is a raw `i64` (not a handle) because TIR emit sites derive it
/// from `IntLit` directly — the literal is already an i64 scalar. This
/// mirrors the convention used by `tla_set_range` and `tla_set_ksubset`.
#[no_mangle]
pub extern "C" fn tla_tuple_get(tup: TlaHandle, idx: i64) -> TlaHandle {
    let tup_v = handle_to_value(tup);
    let Some(elems) = tup_v.as_tuple() else {
        return NIL_HANDLE;
    };
    if idx < 1 {
        return NIL_HANDLE;
    }
    let Ok(idx_usize) = usize::try_from(idx) else {
        return NIL_HANDLE;
    };
    // TLA+ tuples are 1-indexed; the underlying `Arc<[Value]>` is 0-indexed.
    let Some(elem) = elems.get(idx_usize - 1) else {
        return NIL_HANDLE;
    };
    handle_from_value(elem)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::clear_tla_arena;
    use super::*;

    fn int_handle(n: i64) -> TlaHandle {
        handle_from_value(&Value::SmallInt(n))
    }

    #[test]
    fn tuple_new_0_is_empty() {
        clear_tla_arena();
        let h = tla_tuple_new_0();
        assert_eq!(
            handle_to_value(h),
            Value::tuple(std::iter::empty::<Value>())
        );
    }

    #[test]
    fn tuple_new_1_builds_single_element_tuple() {
        clear_tla_arena();
        let h = tla_tuple_new_1(int_handle(42));
        assert_eq!(handle_to_value(h), Value::tuple([Value::SmallInt(42)]));
    }

    #[test]
    fn tuple_new_3_builds_triple() {
        clear_tla_arena();
        let h = tla_tuple_new_3(int_handle(1), int_handle(2), int_handle(3));
        assert_eq!(
            handle_to_value(h),
            Value::tuple([
                Value::SmallInt(1),
                Value::SmallInt(2),
                Value::SmallInt(3),
            ])
        );
    }

    #[test]
    fn tuple_new_preserves_order_and_duplicates() {
        // Unlike sets, tuples preserve element order AND keep duplicates.
        clear_tla_arena();
        let h = tla_tuple_new_4(
            int_handle(7),
            int_handle(3),
            int_handle(7),
            int_handle(3),
        );
        let v = handle_to_value(h);
        let elems = v.as_tuple().expect("tuple");
        assert_eq!(elems.len(), 4);
        assert_eq!(elems[0], Value::SmallInt(7));
        assert_eq!(elems[1], Value::SmallInt(3));
        assert_eq!(elems[2], Value::SmallInt(7));
        assert_eq!(elems[3], Value::SmallInt(3));
    }

    #[test]
    fn tuple_new_8_builds_full_width_tuple() {
        clear_tla_arena();
        let h = tla_tuple_new_8(
            int_handle(1),
            int_handle(2),
            int_handle(3),
            int_handle(4),
            int_handle(5),
            int_handle(6),
            int_handle(7),
            int_handle(8),
        );
        let v = handle_to_value(h);
        let elems = v.as_tuple().expect("tuple");
        assert_eq!(elems.len(), 8);
        for (i, e) in elems.iter().enumerate() {
            assert_eq!(*e, Value::SmallInt((i + 1) as i64));
        }
    }

    #[test]
    fn tuple_new_accepts_mixed_types() {
        clear_tla_arena();
        let h = tla_tuple_new_3(
            int_handle(1),
            handle_from_value(&Value::Bool(true)),
            handle_from_value(&Value::string("hello")),
        );
        let v = handle_to_value(h);
        let elems = v.as_tuple().expect("tuple");
        assert_eq!(elems[0], Value::SmallInt(1));
        assert_eq!(elems[1], Value::Bool(true));
        assert_eq!(elems[2], Value::string("hello"));
    }

    #[test]
    fn tuple_get_1_indexed_in_range() {
        clear_tla_arena();
        let h = tla_tuple_new_3(int_handle(10), int_handle(20), int_handle(30));
        assert_eq!(handle_to_value(tla_tuple_get(h, 1)), Value::SmallInt(10));
        assert_eq!(handle_to_value(tla_tuple_get(h, 2)), Value::SmallInt(20));
        assert_eq!(handle_to_value(tla_tuple_get(h, 3)), Value::SmallInt(30));
    }

    #[test]
    fn tuple_get_zero_index_is_nil() {
        // TLA+ is 1-indexed; idx=0 is out of bounds.
        clear_tla_arena();
        let h = tla_tuple_new_2(int_handle(10), int_handle(20));
        assert_eq!(tla_tuple_get(h, 0), NIL_HANDLE);
    }

    #[test]
    fn tuple_get_negative_index_is_nil() {
        clear_tla_arena();
        let h = tla_tuple_new_2(int_handle(10), int_handle(20));
        assert_eq!(tla_tuple_get(h, -1), NIL_HANDLE);
    }

    #[test]
    fn tuple_get_past_end_is_nil() {
        clear_tla_arena();
        let h = tla_tuple_new_2(int_handle(10), int_handle(20));
        assert_eq!(tla_tuple_get(h, 3), NIL_HANDLE);
        assert_eq!(tla_tuple_get(h, i64::MAX), NIL_HANDLE);
    }

    #[test]
    fn tuple_get_on_empty_tuple_is_nil() {
        clear_tla_arena();
        let h = tla_tuple_new_0();
        assert_eq!(tla_tuple_get(h, 1), NIL_HANDLE);
    }

    #[test]
    fn tuple_get_on_non_tuple_is_nil() {
        // Scalars and other compounds are not tuples; fall back to
        // interpreter. `as_tuple()` returns None on Seq/Func/Record/etc.
        clear_tla_arena();
        let not_a_tuple = int_handle(7);
        assert_eq!(tla_tuple_get(not_a_tuple, 1), NIL_HANDLE);
    }

    #[test]
    fn tuple_get_roundtrips_mixed_values() {
        clear_tla_arena();
        let h = tla_tuple_new_3(
            int_handle(99),
            handle_from_value(&Value::Bool(false)),
            handle_from_value(&Value::string("tag")),
        );
        assert_eq!(handle_to_value(tla_tuple_get(h, 1)), Value::SmallInt(99));
        assert_eq!(handle_to_value(tla_tuple_get(h, 2)), Value::Bool(false));
        assert_eq!(handle_to_value(tla_tuple_get(h, 3)), Value::string("tag"));
    }
}
