// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_set_*` runtime helpers — handle-based FFI for TLA+ set operations.
//!
//! Exposes 10 base operators plus N=0..=8 monomorphic `tla_set_enum_N`
//! variants, all taking [`TlaHandle`] operands and returning a
//! [`TlaHandle`] result. Every helper is a thin wrapper around a method
//! in `tla_value::value::*` so semantic parity with the interpreter is
//! inherited by construction.
//!
//! | Helper | Mapping |
//! |--------|---------|
//! | `tla_set_enum_N` | `Value::set([h_1, …, h_N].map(handle_to_value))` |
//! | `tla_set_in` | `Value::set_contains` |
//! | `tla_set_union` | `SortedSet::union` (via `to_sorted_set`) |
//! | `tla_set_intersect` | `SortedSet::intersection` |
//! | `tla_set_diff` | `SortedSet::difference` |
//! | `tla_set_subseteq` | `SortedSet::is_subset` |
//! | `tla_set_powerset` | `value::powerset` |
//! | `tla_set_big_union` | `value::big_union` |
//! | `tla_set_range` | `value::range_set` (lazy interval) |
//! | `tla_set_ksubset` | `KSubsetValue::new` |
//!
//! # Soundness contract
//!
//! - Helpers that cannot compute their result (e.g. non-enumerable operands,
//!   cardinality bounds exceeded) return [`NIL_HANDLE`]. `tir_lower`
//!   emits a guard that falls back to the interpreter on NIL. This keeps
//!   the FFI surface panic-free without silently corrupting results.
//! - The caller must [`clear_tla_arena`](super::handle::clear_tla_arena)
//!   at action boundaries; otherwise arena handles accumulate.
//!
//! Part of #4318.

use num_bigint::BigInt;
use tla_value::value::{powerset as value_powerset, range_set, KSubsetValue, SortedSet, Value};

use super::handle::{handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE};

// ============================================================================
// tla_set_enum_N (N = 0..=8) — build a literal set from N element handles
// ============================================================================
//
// The N-arity monomorphs avoid the need for a variadic FFI shim for the
// common case of spec-declared set literals. `tir_lower` emits
// `tla_set_enum_N` for N <= 8 and falls back to the interpreter (or a
// variadic helper added later) for larger literals.

/// `{}` — the empty set.
#[no_mangle]
pub extern "C" fn tla_set_enum_0() -> TlaHandle {
    handle_from_value(&Value::empty_set())
}

/// `{e_1}` — one-element set.
#[no_mangle]
pub extern "C" fn tla_set_enum_1(h0: TlaHandle) -> TlaHandle {
    set_enum_from_handles(&[h0])
}

/// `{e_1, e_2}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_2(h0: TlaHandle, h1: TlaHandle) -> TlaHandle {
    set_enum_from_handles(&[h0, h1])
}

/// `{e_1, e_2, e_3}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_3(h0: TlaHandle, h1: TlaHandle, h2: TlaHandle) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2])
}

/// `{e_1, …, e_4}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_4(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2, h3])
}

/// `{e_1, …, e_5}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_5(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2, h3, h4])
}

/// `{e_1, …, e_6}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_6(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2, h3, h4, h5])
}

/// `{e_1, …, e_7}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_7(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2, h3, h4, h5, h6])
}

/// `{e_1, …, e_8}`.
#[no_mangle]
pub extern "C" fn tla_set_enum_8(
    h0: TlaHandle,
    h1: TlaHandle,
    h2: TlaHandle,
    h3: TlaHandle,
    h4: TlaHandle,
    h5: TlaHandle,
    h6: TlaHandle,
    h7: TlaHandle,
) -> TlaHandle {
    set_enum_from_handles(&[h0, h1, h2, h3, h4, h5, h6, h7])
}

#[inline]
fn set_enum_from_handles(handles: &[TlaHandle]) -> TlaHandle {
    let values: Vec<Value> = handles.iter().copied().map(handle_to_value).collect();
    handle_from_value(&Value::set(values))
}

// ============================================================================
// tla_set_in — element-of test
// ============================================================================

/// `elem \in set` — returns 1 (true), 0 (false), or [`NIL_HANDLE`] if the
/// query cannot be answered without an evaluation context (e.g. SetPred).
///
/// The 1/0 return encodes a boolean as a raw `i64`, not a handle. Callers
/// (tir_lower) interpret the low bit as the boolean result directly.
#[no_mangle]
pub extern "C" fn tla_set_in(elem: TlaHandle, set: TlaHandle) -> i64 {
    let set_v = handle_to_value(set);
    let elem_v = handle_to_value(elem);
    match set_v.set_contains(&elem_v) {
        Some(true) => 1,
        Some(false) => 0,
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_set_union / intersect / diff — binary set algebra
// ============================================================================

/// `set1 \cup set2` — returns a fresh set handle, or [`NIL_HANDLE`] on
/// non-enumerable operands.
#[no_mangle]
pub extern "C" fn tla_set_union(set1: TlaHandle, set2: TlaHandle) -> TlaHandle {
    binary_set_op(set1, set2, |a, b| a.union(&b))
}

/// `set1 \cap set2`.
#[no_mangle]
pub extern "C" fn tla_set_intersect(set1: TlaHandle, set2: TlaHandle) -> TlaHandle {
    binary_set_op(set1, set2, |a, b| a.intersection(&b))
}

/// `set1 \ set2`.
#[no_mangle]
pub extern "C" fn tla_set_diff(set1: TlaHandle, set2: TlaHandle) -> TlaHandle {
    binary_set_op(set1, set2, |a, b| a.difference(&b))
}

#[inline]
fn binary_set_op<F>(set1: TlaHandle, set2: TlaHandle, op: F) -> TlaHandle
where
    F: FnOnce(SortedSet, SortedSet) -> SortedSet,
{
    let Some(a) = handle_to_value(set1).to_sorted_set() else {
        return NIL_HANDLE;
    };
    let Some(b) = handle_to_value(set2).to_sorted_set() else {
        return NIL_HANDLE;
    };
    handle_from_value(&Value::from_sorted_set(op(a, b)))
}

// ============================================================================
// tla_set_subseteq — returns 1/0
// ============================================================================

/// `set1 \subseteq set2` — returns 1 (true), 0 (false), or [`NIL_HANDLE`]
/// if either operand cannot be materialised.
#[no_mangle]
pub extern "C" fn tla_set_subseteq(set1: TlaHandle, set2: TlaHandle) -> i64 {
    let Some(a) = handle_to_value(set1).to_sorted_set() else {
        return NIL_HANDLE;
    };
    let Some(b) = handle_to_value(set2).to_sorted_set() else {
        return NIL_HANDLE;
    };
    if a.is_subset(&b) {
        1
    } else {
        0
    }
}

// ============================================================================
// tla_set_powerset — SUBSET s
// ============================================================================

/// `SUBSET s` — returns a handle to the materialised powerset.
///
/// Falls through to [`NIL_HANDLE`] on non-enumerable operands or when the
/// cardinality bound (`Value::powerset` rejects > 20 elements) is
/// exceeded. tir_lower must fall back to the interpreter's lazy
/// [`tla_value::SubsetValue`] for larger bases.
#[no_mangle]
pub extern "C" fn tla_set_powerset(s: TlaHandle) -> TlaHandle {
    let Some(sorted) = handle_to_value(s).to_sorted_set() else {
        return NIL_HANDLE;
    };
    match value_powerset(&sorted) {
        Ok(v) => handle_from_value(&v),
        Err(_) => NIL_HANDLE,
    }
}

// ============================================================================
// tla_set_big_union — UNION s
// ============================================================================

/// `UNION s` — flatten a set-of-sets into a single set.
#[no_mangle]
pub extern "C" fn tla_set_big_union(s: TlaHandle) -> TlaHandle {
    let Some(sorted) = handle_to_value(s).to_sorted_set() else {
        return NIL_HANDLE;
    };
    match tla_value::value::big_union(&sorted) {
        Some(v) => handle_from_value(&v),
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_set_range — lo..hi integer range
// ============================================================================

/// `lo..hi` — returns a lazy interval handle.
///
/// `lo` and `hi` are i64 scalars (not handles) because the TIR emit site
/// produces them from `IntLit` directly. `tir_lower` is expected to encode
/// the inputs as raw i64 values.
#[no_mangle]
pub extern "C" fn tla_set_range(lo: i64, hi: i64) -> TlaHandle {
    let v = range_set(&BigInt::from(lo), &BigInt::from(hi));
    handle_from_value(&v)
}

// ============================================================================
// tla_set_ksubset — {s \in SUBSET base : Cardinality(s) = k}
// ============================================================================

/// `Ksubsets(base, k)` — `k`-element subsets of `base`.
///
/// Produces the lazy [`KSubsetValue`] representation so enumeration is
/// pay-as-you-go. `k` is passed as a raw i64 (see `tla_set_range`
/// rationale).
#[no_mangle]
pub extern "C" fn tla_set_ksubset(base: TlaHandle, k: i64) -> TlaHandle {
    let base_v = handle_to_value(base);
    if !base_v.is_set() {
        return NIL_HANDLE;
    }
    if k < 0 {
        return NIL_HANDLE;
    }
    let k_usize = match usize::try_from(k) {
        Ok(n) => n,
        Err(_) => return NIL_HANDLE,
    };
    handle_from_value(&Value::KSubset(KSubsetValue::new(base_v, k_usize)))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::clear_tla_arena;
    use super::*;

    fn set_of_ints(xs: &[i64]) -> Value {
        Value::set(xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>())
    }

    #[test]
    fn set_enum_0_is_empty() {
        clear_tla_arena();
        let h = tla_set_enum_0();
        assert_eq!(handle_to_value(h), Value::empty_set());
    }

    #[test]
    fn set_enum_3_builds_three_element_set() {
        clear_tla_arena();
        let h = tla_set_enum_3(
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
            handle_from_value(&Value::SmallInt(3)),
        );
        assert_eq!(handle_to_value(h), set_of_ints(&[1, 2, 3]));
    }

    #[test]
    fn set_enum_deduplicates() {
        clear_tla_arena();
        let h = tla_set_enum_4(
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
            handle_from_value(&Value::SmallInt(1)),
            handle_from_value(&Value::SmallInt(2)),
        );
        assert_eq!(handle_to_value(h), set_of_ints(&[1, 2]));
    }

    #[test]
    fn set_in_matches_interpreter() {
        clear_tla_arena();
        let s = handle_from_value(&set_of_ints(&[1, 3, 5, 7]));
        for (elem, expected) in [(1, 1), (3, 1), (5, 1), (7, 1), (0, 0), (2, 0), (8, 0)] {
            let e = handle_from_value(&Value::SmallInt(elem));
            assert_eq!(
                tla_set_in(e, s),
                expected,
                "set_in mismatch for elem {elem}"
            );
        }
    }

    #[test]
    fn set_union_matches_interpreter() {
        clear_tla_arena();
        let a = handle_from_value(&set_of_ints(&[1, 2, 3]));
        let b = handle_from_value(&set_of_ints(&[3, 4, 5]));
        let u = tla_set_union(a, b);
        assert_eq!(handle_to_value(u), set_of_ints(&[1, 2, 3, 4, 5]));
    }

    #[test]
    fn set_intersect_matches_interpreter() {
        clear_tla_arena();
        let a = handle_from_value(&set_of_ints(&[1, 2, 3, 4]));
        let b = handle_from_value(&set_of_ints(&[3, 4, 5, 6]));
        let i = tla_set_intersect(a, b);
        assert_eq!(handle_to_value(i), set_of_ints(&[3, 4]));
    }

    #[test]
    fn set_diff_matches_interpreter() {
        clear_tla_arena();
        let a = handle_from_value(&set_of_ints(&[1, 2, 3, 4]));
        let b = handle_from_value(&set_of_ints(&[2, 4, 6]));
        let d = tla_set_diff(a, b);
        assert_eq!(handle_to_value(d), set_of_ints(&[1, 3]));
    }

    #[test]
    fn set_subseteq_matches_interpreter() {
        clear_tla_arena();
        let a = handle_from_value(&set_of_ints(&[1, 2]));
        let b = handle_from_value(&set_of_ints(&[1, 2, 3]));
        let c = handle_from_value(&set_of_ints(&[1, 4]));
        assert_eq!(tla_set_subseteq(a, b), 1);
        assert_eq!(tla_set_subseteq(b, a), 0);
        assert_eq!(tla_set_subseteq(c, b), 0);
    }

    #[test]
    fn set_powerset_cardinality_is_2_to_the_n() {
        clear_tla_arena();
        for n in 0..=5 {
            let base: Vec<i64> = (0..n).collect();
            let base_h = handle_from_value(&set_of_ints(&base));
            let ps = tla_set_powerset(base_h);
            let ps_v = handle_to_value(ps);
            let sorted = ps_v
                .to_sorted_set()
                .expect("powerset of enumerable is enumerable");
            assert_eq!(sorted.len(), 1usize << n, "SUBSET cardinality for n={n}");
        }
    }

    #[test]
    fn set_big_union_flattens() {
        clear_tla_arena();
        // { {1, 2}, {2, 3}, {4} } → {1, 2, 3, 4}
        let inner1 = set_of_ints(&[1, 2]);
        let inner2 = set_of_ints(&[2, 3]);
        let inner3 = set_of_ints(&[4]);
        let outer = Value::set(vec![inner1, inner2, inner3]);
        let h = handle_from_value(&outer);
        let flat = tla_set_big_union(h);
        assert_eq!(handle_to_value(flat), set_of_ints(&[1, 2, 3, 4]));
    }

    #[test]
    fn set_range_matches_interval() {
        clear_tla_arena();
        let h = tla_set_range(2, 5);
        let v = handle_to_value(h);
        let sorted = v.to_sorted_set().expect("interval is enumerable");
        assert_eq!(sorted.len(), 4);
        let vals: Vec<i64> = sorted.iter().filter_map(|x| x.as_i64()).collect();
        assert_eq!(vals, vec![2, 3, 4, 5]);
    }

    #[test]
    fn set_range_empty_when_hi_lt_lo() {
        clear_tla_arena();
        let h = tla_set_range(5, 2);
        let v = handle_to_value(h);
        assert_eq!(v, Value::empty_set());
    }

    #[test]
    fn set_ksubset_cardinality_is_binomial() {
        clear_tla_arena();
        let base = handle_from_value(&set_of_ints(&[1, 2, 3, 4]));
        let h = tla_set_ksubset(base, 2);
        let v = handle_to_value(h);
        // KSubsetValue is lazy — use set_len() to read cardinality without
        // materialising all 6 subsets.
        let n = v.set_len().expect("k-subset is enumerable");
        assert_eq!(n, BigInt::from(6));
    }

    #[test]
    fn set_in_on_non_set_returns_nil() {
        // `SmallInt` is not a set; set_contains returns None, which maps
        // to NIL_HANDLE. This is the "fall back to interpreter" path.
        clear_tla_arena();
        let not_a_set = handle_from_value(&Value::SmallInt(7));
        let elem = handle_from_value(&Value::SmallInt(1));
        let r = tla_set_in(elem, not_a_set);
        assert_eq!(r, NIL_HANDLE);
    }

    #[test]
    fn union_intersect_diff_consistency() {
        // Property: |A ∪ B| + |A ∩ B| == |A| + |B|
        clear_tla_arena();
        let a_set = set_of_ints(&[1, 2, 3, 5, 7]);
        let b_set = set_of_ints(&[2, 3, 4, 6, 7, 8]);
        let a = handle_from_value(&a_set);
        let b = handle_from_value(&b_set);
        let u = handle_to_value(tla_set_union(a, b))
            .to_sorted_set()
            .unwrap();
        let i = handle_to_value(tla_set_intersect(a, b))
            .to_sorted_set()
            .unwrap();
        let a_sz = a_set.to_sorted_set().unwrap().len();
        let b_sz = b_set.to_sorted_set().unwrap().len();
        assert_eq!(u.len() + i.len(), a_sz + b_sz);
        // Property: A \ B is disjoint from B (every elem of diff is not in B)
        let d = handle_to_value(tla_set_diff(a, b)).to_sorted_set().unwrap();
        let b_sorted = b_set.to_sorted_set().unwrap();
        for elem in d.iter() {
            assert!(
                !b_sorted.contains(elem),
                "A \\ B contains {elem:?} which is in B"
            );
        }
    }
}
