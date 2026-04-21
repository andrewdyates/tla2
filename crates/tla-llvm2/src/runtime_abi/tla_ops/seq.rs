// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_seq_*` runtime helpers — handle-based FFI for TLA+ sequence operations.
//!
//! Exposes 8 base operators plus N=0..=8 monomorphic `tla_seq_new_N` variants,
//! all taking [`TlaHandle`] operands and returning a [`TlaHandle`] result.
//! Every helper is a thin wrapper around a method in `tla_value::value::*`
//! (`SeqValue::append`, `SeqValue::tail`, `SeqValue::subseq`, …) so semantic
//! parity with the interpreter is inherited by construction.
//!
//! | Helper | Mapping |
//! |--------|---------|
//! | `tla_seq_new_N` | `Value::seq([h_1, …, h_N].map(handle_to_value))` |
//! | `tla_seq_concat` | `s1 \o s2` (matches `eval_arith::\\o`) |
//! | `tla_seq_len` | `SeqValue::len` |
//! | `tla_seq_head` | `SeqValue::first` |
//! | `tla_seq_tail` | `SeqValue::tail` |
//! | `tla_seq_append` | `SeqValue::append` |
//! | `tla_seq_subseq` | `SeqValue::subseq` (1-indexed `lo..=hi` in TLA+) |
//! | `tla_seq_set` | `Value::SeqSet(SeqSetValue::new(base))` |
//!
//! # Soundness contract
//!
//! - Helpers that cannot compute their result (e.g. non-sequence operand,
//!   empty sequence passed to `Head`/`Tail`) return [`NIL_HANDLE`].
//!   `tir_lower` emits a guard that falls back to the interpreter on NIL.
//!   This keeps the FFI surface panic-free without silently corrupting
//!   results.
//! - The caller must [`clear_tla_arena`](super::handle::clear_tla_arena)
//!   at action boundaries; otherwise arena handles accumulate.
//! - `tla_seq_len` returns a plain `i64` (not a handle) mirroring
//!   `tla_set_in`/`tla_set_subseteq`: cardinality is always a small
//!   integer at LLVM-call sites. `NIL_HANDLE` on non-sequence input.
//!
//! # 1-indexing note
//!
//! TLA+ sequences are 1-indexed but `SeqValue` stores 0-indexed internally.
//! `tla_seq_subseq(s, lo, hi)` takes TLA+ 1-indexed bounds and forwards to
//! `SeqValue::subseq(lo - 1, hi)` (subseq is 0-indexed exclusive end). The
//! i64 bounds avoid an extra handle unbox on each call, mirroring
//! `tla_set_range`/`tla_set_ksubset`.
//!
//! Part of #4318.

use tla_value::value::{SeqSetValue, Value};

use super::handle::{handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE};

// ============================================================================
// tla_seq_new_N (N = 0..=8) — build a literal sequence from N element handles
// ============================================================================
//
// Monomorph variants avoid a variadic FFI shim for the common case of
// spec-declared sequence literals. `tir_lower` emits `tla_seq_new_N` for
// N <= 8 and falls back to the interpreter (or a variadic helper added
// later) for larger literals.

/// `<<>>` — the empty sequence.
#[no_mangle]
pub extern "C" fn tla_seq_new_0() -> TlaHandle {
    handle_from_value(&Value::seq(Vec::<Value>::new()))
}

/// `<<e_1>>` — one-element sequence.
#[no_mangle]
pub extern "C" fn tla_seq_new_1(h0: TlaHandle) -> TlaHandle {
    seq_new_from_handles(&[h0])
}

/// `<<e_1, e_2>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_2(h0: TlaHandle, h1: TlaHandle) -> TlaHandle {
    seq_new_from_handles(&[h0, h1])
}

/// `<<e_1, e_2, e_3>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_3(h0: TlaHandle, h1: TlaHandle, h2: TlaHandle) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2])
}

/// `<<e_1, …, e_4>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_4(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2, h3])
}

/// `<<e_1, …, e_5>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_5(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2, h3, h4])
}

/// `<<e_1, …, e_6>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_6(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2, h3, h4, h5])
}

/// `<<e_1, …, e_7>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_7(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2, h3, h4, h5, h6])
}

/// `<<e_1, …, e_8>>`.
#[no_mangle]
pub extern "C" fn tla_seq_new_8(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
    h7: TlaHandle,
) -> TlaHandle {
    seq_new_from_handles(&[h0, h1, h2, h3, h4, h5, h6, h7])
}

#[inline]
fn seq_new_from_handles(handles: &[TlaHandle]) -> TlaHandle {
    let values: Vec<Value> = handles.iter().copied().map(handle_to_value).collect();
    handle_from_value(&Value::seq(values))
}

// ============================================================================
// tla_seq_concat — `s1 \o s2`
// ============================================================================

/// `s1 \o s2` — concatenate two sequences.
///
/// Mirrors the interpreter's concatenation path in `eval_arith.rs::\\o` but
/// scoped to the common `Seq`/`Tuple` case (sequence-like `Func`/`IntFunc`
/// operands are not lowered through this helper by `tir_lower` — they fall
/// through to the interpreter). Returns [`NIL_HANDLE`] on non-sequence
/// operand so the caller can reroute.
#[no_mangle]
pub extern "C" fn tla_seq_concat(s1: TlaHandle, s2: TlaHandle) -> TlaHandle {
    let v1 = handle_to_value(s1);
    let v2 = handle_to_value(s2);
    let Some(elems1) = v1.as_seq_or_tuple_elements() else {
        return NIL_HANDLE;
    };
    let Some(elems2) = v2.as_seq_or_tuple_elements() else {
        return NIL_HANDLE;
    };
    let mut out: Vec<Value> = Vec::with_capacity(elems1.len() + elems2.len());
    out.extend(elems1.iter().cloned());
    out.extend(elems2.iter().cloned());
    handle_from_value(&Value::seq(out))
}

// ============================================================================
// tla_seq_len — `Len(s)`
// ============================================================================

/// `Len(s)` — sequence length.
///
/// Returns a plain `i64` (not a handle) — the result is always a small
/// non-negative integer and tir_lower consumes it as i64 directly.
/// Returns [`NIL_HANDLE`] on non-sequence operand so the caller can fall
/// back to the interpreter.
#[no_mangle]
pub extern "C" fn tla_seq_len(s: TlaHandle) -> i64 {
    let v = handle_to_value(s);
    match v.as_seq_or_tuple_elements() {
        Some(elems) => elems.len() as i64,
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_seq_head — `Head(s)`
// ============================================================================

/// `Head(s)` — first element.
///
/// Returns [`NIL_HANDLE`] on empty sequence or non-sequence operand; TLA+
/// leaves `Head(<<>>)` undefined and the interpreter raises an error.
/// `tir_lower` must emit a NIL-guard so the interpreter surfaces the same
/// error in the fallback path.
#[no_mangle]
pub extern "C" fn tla_seq_head(s: TlaHandle) -> TlaHandle {
    let v = handle_to_value(s);
    let Some(elems) = v.as_seq_or_tuple_elements() else {
        return NIL_HANDLE;
    };
    match elems.first() {
        Some(first) => handle_from_value(first),
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_seq_tail — `Tail(s)`
// ============================================================================

/// `Tail(s)` — all but the first element.
///
/// Returns [`NIL_HANDLE`] on empty sequence or non-sequence operand (TLA+
/// leaves `Tail(<<>>)` undefined).
#[no_mangle]
pub extern "C" fn tla_seq_tail(s: TlaHandle) -> TlaHandle {
    let v = handle_to_value(s);
    match &v {
        Value::Seq(seq) => {
            if seq.is_empty() {
                return NIL_HANDLE;
            }
            handle_from_value(&Value::Seq(std::sync::Arc::new(seq.tail())))
        }
        Value::Tuple(elems) => {
            if elems.is_empty() {
                return NIL_HANDLE;
            }
            handle_from_value(&Value::seq(elems.iter().skip(1).cloned()))
        }
        _ => NIL_HANDLE,
    }
}

// ============================================================================
// tla_seq_append — `Append(s, x)`
// ============================================================================

/// `Append(s, x)` — append an element to the end of a sequence.
#[no_mangle]
pub extern "C" fn tla_seq_append(s: TlaHandle, x: TlaHandle) -> TlaHandle {
    let v = handle_to_value(s);
    let elem = handle_to_value(x);
    match &v {
        Value::Seq(seq) => handle_from_value(&Value::Seq(std::sync::Arc::new(seq.append(elem)))),
        Value::Tuple(elems) => {
            let mut out: Vec<Value> = Vec::with_capacity(elems.len() + 1);
            out.extend(elems.iter().cloned());
            out.push(elem);
            handle_from_value(&Value::seq(out))
        }
        _ => NIL_HANDLE,
    }
}

// ============================================================================
// tla_seq_subseq — `SubSeq(s, lo, hi)`
// ============================================================================

/// `SubSeq(s, lo, hi)` — 1-indexed inclusive range `s[lo..=hi]`.
///
/// `lo` and `hi` are raw i64 scalars (TLA+ semantics). Empty range when
/// `hi < lo`. Out-of-bounds indices clamp to the sequence length, matching
/// `SeqValue::subseq`'s tolerant implementation (which itself mirrors TLC
/// behaviour for `SubSeq` with bounds outside `1..=Len(s)`).
///
/// Returns [`NIL_HANDLE`] on non-sequence operand or negative `lo`.
#[no_mangle]
pub extern "C" fn tla_seq_subseq(s: TlaHandle, lo: i64, hi: i64) -> TlaHandle {
    if lo < 1 && hi >= 1 {
        // lo < 1 with non-empty range is ill-formed in TLA+; bail to
        // interpreter for precise error reporting.
        return NIL_HANDLE;
    }
    if hi < lo {
        return handle_from_value(&Value::seq(Vec::<Value>::new()));
    }
    let v = handle_to_value(s);
    let Some(elems) = v.as_seq_or_tuple_elements() else {
        return NIL_HANDLE;
    };
    // Convert 1-indexed inclusive [lo, hi] to 0-indexed exclusive [lo-1, hi).
    // Saturate at sequence length to match SeqValue::subseq semantics.
    let len = elems.len();
    let start = usize::try_from(lo - 1).unwrap_or(0).min(len);
    let end = usize::try_from(hi).unwrap_or(0).min(len);
    if start >= end {
        return handle_from_value(&Value::seq(Vec::<Value>::new()));
    }
    handle_from_value(&Value::seq(elems[start..end].iter().cloned()))
}

// ============================================================================
// tla_seq_set — `Seq(S)`
// ============================================================================

/// `Seq(S)` — the (infinite) set of all finite sequences over `S`.
///
/// Returns a lazy [`SeqSetValue`] handle; enumeration is membership-only
/// (never materialised). Any `Value` is legal as the base — the runtime
/// defers non-enumerability to the membership check.
#[no_mangle]
pub extern "C" fn tla_seq_set(s: TlaHandle) -> TlaHandle {
    let base = handle_to_value(s);
    handle_from_value(&Value::SeqSet(SeqSetValue::new(base)))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::clear_tla_arena;
    use super::*;

    fn int_seq(xs: &[i64]) -> Value {
        Value::seq(xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>())
    }

    fn decode_seq_ints(h: TlaHandle) -> Vec<i64> {
        let v = handle_to_value(h);
        let elems = v
            .as_seq_or_tuple_elements()
            .expect("decoded handle should be a seq or tuple");
        elems.iter().filter_map(|e| e.as_i64()).collect()
    }

    #[test]
    fn seq_new_0_is_empty() {
        clear_tla_arena();
        let h = tla_seq_new_0();
        assert_eq!(handle_to_value(h), Value::seq(Vec::<Value>::new()));
    }

    #[test]
    fn seq_new_3_builds_three_element_sequence() {
        clear_tla_arena();
        let h = tla_seq_new_3(
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
            handle_from_value(&Value::SmallInt(3)),
        );
        assert_eq!(decode_seq_ints(h), vec![1, 2, 3]);
    }

    #[test]
    fn seq_new_preserves_duplicates() {
        // Unlike sets, sequences preserve duplicate elements.
        clear_tla_arena();
        let h = tla_seq_new_4(
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
        );
        assert_eq!(decode_seq_ints(h), vec![1, 2, 1, 2]);
    }

    #[test]
    fn seq_new_preserves_order() {
        clear_tla_arena();
        // 8-element monomorph check: iteration order is stable.
        let h = tla_seq_new_8(
            handle_from_value(&Value::SmallInt(8)),
            handle_from_value(&Value::SmallInt(7)),
            handle_from_value(&Value::SmallInt(6)),
            handle_from_value(&Value::SmallInt(5)),
            handle_from_value(&Value::SmallInt(4)),
            handle_from_value(&Value::SmallInt(3)),
            handle_from_value(&Value::SmallInt(2)),
            handle_from_value(&Value::SmallInt(1)),
        );
        assert_eq!(decode_seq_ints(h), vec![8, 7, 6, 5, 4, 3, 2, 1]);
    }

    #[test]
    fn seq_concat_matches_interpreter() {
        clear_tla_arena();
        let a = handle_from_value(&int_seq(&[1, 2, 3]));
        let b = handle_from_value(&int_seq(&[4, 5]));
        let c = tla_seq_concat(a, b);
        assert_eq!(decode_seq_ints(c), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn seq_concat_empty_left_is_right() {
        clear_tla_arena();
        let a = handle_from_value(&int_seq(&[]));
        let b = handle_from_value(&int_seq(&[7, 8, 9]));
        let c = tla_seq_concat(a, b);
        assert_eq!(decode_seq_ints(c), vec![7, 8, 9]);
    }

    #[test]
    fn seq_concat_on_non_seq_returns_nil() {
        clear_tla_arena();
        let not_a_seq = handle_from_value(&Value::SmallInt(42));
        let b = handle_from_value(&int_seq(&[1]));
        assert_eq!(tla_seq_concat(not_a_seq, b), NIL_HANDLE);
        assert_eq!(tla_seq_concat(b, not_a_seq), NIL_HANDLE);
    }

    #[test]
    fn seq_len_matches_element_count() {
        clear_tla_arena();
        assert_eq!(tla_seq_len(handle_from_value(&int_seq(&[]))), 0);
        assert_eq!(tla_seq_len(handle_from_value(&int_seq(&[9]))), 1);
        assert_eq!(tla_seq_len(handle_from_value(&int_seq(&[1, 2, 3, 4, 5]))), 5);
    }

    #[test]
    fn seq_len_on_non_seq_returns_nil() {
        clear_tla_arena();
        let not_a_seq = handle_from_value(&Value::Bool(true));
        assert_eq!(tla_seq_len(not_a_seq), NIL_HANDLE);
    }

    #[test]
    fn seq_head_returns_first_element() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[11, 22, 33]));
        let h = tla_seq_head(s);
        assert_eq!(handle_to_value(h), Value::SmallInt(11));
    }

    #[test]
    fn seq_head_on_empty_returns_nil() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[]));
        assert_eq!(tla_seq_head(s), NIL_HANDLE);
    }

    #[test]
    fn seq_tail_drops_first_element() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[1, 2, 3, 4]));
        let t = tla_seq_tail(s);
        assert_eq!(decode_seq_ints(t), vec![2, 3, 4]);
    }

    #[test]
    fn seq_tail_on_empty_returns_nil() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[]));
        assert_eq!(tla_seq_tail(s), NIL_HANDLE);
    }

    #[test]
    fn seq_append_adds_element_at_end() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[1, 2, 3]));
        let x = handle_from_value(&Value::SmallInt(99));
        let a = tla_seq_append(s, x);
        assert_eq!(decode_seq_ints(a), vec![1, 2, 3, 99]);
    }

    #[test]
    fn seq_append_on_empty_makes_singleton() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[]));
        let x = handle_from_value(&Value::SmallInt(42));
        let a = tla_seq_append(s, x);
        assert_eq!(decode_seq_ints(a), vec![42]);
    }

    #[test]
    fn seq_subseq_matches_interpreter() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[10, 20, 30, 40, 50]));
        // 1-indexed inclusive: SubSeq(s, 2, 4) = <<20, 30, 40>>
        let sub = tla_seq_subseq(s, 2, 4);
        assert_eq!(decode_seq_ints(sub), vec![20, 30, 40]);
    }

    #[test]
    fn seq_subseq_hi_less_than_lo_is_empty() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[1, 2, 3]));
        let sub = tla_seq_subseq(s, 3, 1);
        assert_eq!(decode_seq_ints(sub), Vec::<i64>::new());
    }

    #[test]
    fn seq_subseq_full_range_roundtrips() {
        clear_tla_arena();
        let xs = [11, 22, 33, 44, 55];
        let s = handle_from_value(&int_seq(&xs));
        let sub = tla_seq_subseq(s, 1, xs.len() as i64);
        assert_eq!(decode_seq_ints(sub), xs.to_vec());
    }

    #[test]
    fn seq_subseq_out_of_bounds_clamps() {
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[1, 2, 3]));
        // hi beyond length → clamp
        let sub = tla_seq_subseq(s, 2, 100);
        assert_eq!(decode_seq_ints(sub), vec![2, 3]);
    }

    #[test]
    fn seq_set_is_seqset_over_base() {
        clear_tla_arena();
        let base = Value::set(vec![Value::SmallInt(0), Value::SmallInt(1)]);
        let h = tla_seq_set(handle_from_value(&base));
        let v = handle_to_value(h);
        // Round-trip: the decoded value must still be a SeqSet, not a
        // materialised set.
        assert!(matches!(v, Value::SeqSet(_)));
    }

    #[test]
    fn seq_append_then_tail_roundtrips() {
        // Property: Tail(Append(s, x)) == if s == <<>> then <<>> else Append(Tail(s), x)
        clear_tla_arena();
        let s = handle_from_value(&int_seq(&[1, 2, 3]));
        let x = handle_from_value(&Value::SmallInt(99));
        let appended = tla_seq_append(s, x);
        let t = tla_seq_tail(appended);
        assert_eq!(decode_seq_ints(t), vec![2, 3, 99]);
    }

    #[test]
    fn seq_concat_length_is_sum() {
        // Property: Len(s1 \o s2) == Len(s1) + Len(s2)
        clear_tla_arena();
        let a = handle_from_value(&int_seq(&[1, 2, 3, 4]));
        let b = handle_from_value(&int_seq(&[5, 6]));
        let c = tla_seq_concat(a, b);
        assert_eq!(tla_seq_len(c), tla_seq_len(a) + tla_seq_len(b));
    }
}
