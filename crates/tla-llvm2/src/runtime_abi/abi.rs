// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable ABI types + runtime helpers for LLVM2-compiled code.
//!
//! The pure ABI types ([`JitCallOut`], [`JitStatus`], [`JitRuntimeErrorKind`],
//! [`JitRuntimeError`], and the function-pointer aliases) are defined in the
//! `tla-jit-abi` leaf crate and re-exported here so existing
//! `runtime_abi::{JitCallOut, ...}` call sites keep working. `tla-jit-abi`
//! exists to break the `tla-tmir` -> `tla-jit` cargo cycle — see #4265 /
//! `designs/2026-04-19-stage-2-deletion-plan.md` §Phase C.
//!
//! The **runtime helpers** below (`jit_set_contains_i64`, `jit_record_get_i64`,
//! `jit_set_union_i64`, the compound scratch buffer, ...) cannot live in
//! `tla-jit-abi` because they depend on `super::compound_layout` (the tag
//! constants describing the serialized i64 state layout). They stay inside
//! `tla-llvm2::runtime_abi` where `compound_layout` is owned.
//!
//! # Overflow Strategy
//!
//! LLVM2-compiled code uses **i64-only with overflow rejection** (Part of #746):
//!
//! | Implementation | Strategy     | Behavior on Overflow               |
//! |----------------|--------------|------------------------------------|
//! | TLC (baseline) | 32-bit int   | Runtime error                      |
//! | tla-check      | i64 + BigInt | Silent promotion to BigInt         |
//! | tla-llvm2      | i64 only     | `ArithmeticOverflow` runtime error |

// Re-export stable ABI types from the leaf crate so in-tree call sites
// (runtime_abi::JitCallOut, runtime_abi::JitStatus, ...) keep working.
pub use tla_jit_abi::{
    JitCallOut, JitExprFn, JitFn0, JitInvariantFn, JitNextStateFn, JitRuntimeError,
    JitRuntimeErrorKind, JitStatus,
};

// ============================================================================
// Runtime helpers for JIT-compiled code
// ============================================================================
// These `extern "C"` functions are called from compiled native code via
// LLVM2's ImportLinkage. They bridge the gap between the flat i64 state buffer
// and compound TLA+ value operations that cannot be expressed as simple i64
// loads.
//
// Part of #3909 Phase 2: native runtime helpers for compound operations.

/// Search a serialized set in the flat i64 state buffer for a scalar element.
///
/// The set is serialized as:
///   `[TAG_SET, count, TAG_0, val_0, TAG_1, val_1, ...]`
/// where each element occupies 2 slots (TAG + value) for scalar elements.
///
/// Parameters:
///   - `state_ptr`: pointer to the start of the flat i64 state buffer
///   - `set_base_slot`: the slot index where TAG_SET begins
///   - `elem_value`: the scalar value to search for (raw i64)
///
/// Returns: 1 if found, 0 if not found. Returns 0 (not found) if the set
/// contains compound elements (records, sequences, sets, functions, tuples)
/// since their serialized size is variable and cannot be iterated with the
/// fixed 2-slot stride. The caller should fall back to the interpreter for
/// compound-element sets.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation. The caller guarantees `state_ptr` points to a valid
/// i64 buffer with at least `set_base_slot + 2 + count * 2` slots (for
/// scalar sets).
///
/// Part of #3999: guard against compound-element sets with variable stride.
pub extern "C" fn jit_set_contains_i64(
    state_ptr: *const i64,
    set_base_slot: i64,
    elem_value: i64,
) -> i64 {
    // SAFETY: state_ptr is a valid pointer to the flat i64 state buffer,
    // guaranteed by the JIT caller. The buffer is immutable during evaluation.
    unsafe {
        let base = set_base_slot as usize;
        // slot[base + 1] = element count
        let count = *state_ptr.add(base + 1);

        // Empty set: trivially not found.
        if count <= 0 {
            return 0;
        }

        // Guard: check the first element's tag. Scalar tags (TAG_INT=5,
        // TAG_BOOL=6, TAG_STRING=7) occupy exactly 2 slots each. Compound
        // tags (TAG_RECORD=1, TAG_SEQ=2, TAG_SET=3, TAG_FUNC=4, TAG_TUPLE=8)
        // have variable-length serialization and cannot be iterated with a
        // fixed 2-slot stride. Return 0 to signal the caller should fall back
        // to the interpreter for compound-element sets.
        // Part of #3999.
        let first_tag = *state_ptr.add(base + 2);
        if !is_scalar_tag(first_tag) {
            return 0;
        }

        let mut offset = base + 2; // first element starts after TAG_SET + count
        for _ in 0..count {
            // Each scalar element: [TAG, value]
            // The value is at offset + 1
            let val = *state_ptr.add(offset + 1);
            if val == elem_value {
                return 1;
            }
            offset += 2; // skip TAG + value
        }
        0
    }
}

/// Check if a type tag represents a scalar value (fixed 2-slot stride).
///
/// Scalar tags: TAG_INT (5), TAG_BOOL (6), TAG_STRING (7).
/// Compound tags: TAG_RECORD (1), TAG_SEQ (2), TAG_SET (3), TAG_FUNC (4), TAG_TUPLE (8).
#[inline]
fn is_scalar_tag(tag: i64) -> bool {
    tag == super::compound_layout::TAG_INT
        || tag == super::compound_layout::TAG_BOOL
        || tag == super::compound_layout::TAG_STRING
}

/// Get a field value from a serialized record in the flat i64 state buffer.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
pub extern "C" fn jit_record_get_i64(
    state_ptr: *const i64,
    record_base_slot: i64,
    field_name_id: i64,
    found_out: *mut i64,
) -> i64 {
    unsafe {
        let base = record_base_slot as usize;
        let field_count = *state_ptr.add(base + 1);
        let mut offset = base + 2;
        for _ in 0..field_count {
            let name_id = *state_ptr.add(offset);
            if name_id == field_name_id {
                *found_out = 1;
                return *state_ptr.add(offset + 2);
            }
            offset += 3;
        }
        *found_out = 0;
        0
    }
}

/// Apply a serialized function (lookup by key) in the flat i64 state buffer.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
pub extern "C" fn jit_func_apply_i64(
    state_ptr: *const i64,
    func_base_slot: i64,
    key_value: i64,
    found_out: *mut i64,
) -> i64 {
    unsafe {
        let base = func_base_slot as usize;
        let pair_count = *state_ptr.add(base + 1);
        let mut offset = base + 2;
        for _ in 0..pair_count {
            let key_val = *state_ptr.add(offset + 1);
            if key_val == key_value {
                *found_out = 1;
                return *state_ptr.add(offset + 3);
            }
            offset += 4;
        }
        *found_out = 0;
        0
    }
}

/// Get the element count from a serialized compound value (set, sequence, or function).
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
pub extern "C" fn jit_compound_count(state_ptr: *const i64, base_slot: i64) -> i64 {
    unsafe { *state_ptr.add(base_slot as usize + 1) }
}

/// Get an element from a serialized sequence at a given 0-based index.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
pub extern "C" fn jit_seq_get_i64(
    state_ptr: *const i64,
    seq_base_slot: i64,
    index: i64,
    found_out: *mut i64,
) -> i64 {
    unsafe {
        let base = seq_base_slot as usize;
        let count = *state_ptr.add(base + 1);
        if index < 0 || index >= count {
            *found_out = 0;
            return 0;
        }
        let slot = base + 2 + (index as usize) * 2 + 1;
        *found_out = 1;
        *state_ptr.add(slot)
    }
}

/// Runtime helper for FuncSet membership tests (JIT peephole optimization).
///
/// # Safety
///
/// All pointers must be valid for the duration of the call.
pub extern "C" fn jit_func_set_membership_check(
    state_ptr: *const i64,
    func_base_slot: i64,
    domain_elems_ptr: *const i64,
    domain_count: i64,
    range_kind: i64,
    range_lo_or_ptr: i64,
    range_hi_or_count: i64,
) -> i64 {
    unsafe {
        let base = func_base_slot as usize;

        let tag = *state_ptr.add(base);
        if tag != super::compound_layout::TAG_FUNC {
            return 0;
        }

        let pair_count = *state_ptr.add(base + 1);
        if pair_count != domain_count {
            return 0;
        }

        let d_count = domain_count as usize;
        let mut offset = base + 2;

        for _ in 0..d_count {
            let key_val = *state_ptr.add(offset + 1);

            let mut key_found = false;
            for j in 0..d_count {
                if *domain_elems_ptr.add(j) == key_val {
                    key_found = true;
                    break;
                }
            }
            if !key_found {
                return 0;
            }

            let range_val = *state_ptr.add(offset + 3);
            let val_in_range = match range_kind {
                0 => {
                    let range_ptr = range_lo_or_ptr as *const i64;
                    let range_count = range_hi_or_count as usize;
                    let mut found = false;
                    for k in 0..range_count {
                        if *range_ptr.add(k) == range_val {
                            found = true;
                            break;
                        }
                    }
                    found
                }
                1 => {
                    let lo = range_lo_or_ptr;
                    let hi = range_hi_or_count;
                    range_val >= lo && range_val <= hi
                }
                _ => false,
            };

            if !val_in_range {
                return 0;
            }

            offset += 4;
        }

        1
    }
}

/// Compute the set difference of two serialized sets.
///
/// # Safety
///
/// All pointers must be valid. `out_ptr` must have room for at least
/// `2 + count1 * 2` i64 slots (same size as set1).
pub extern "C" fn jit_set_diff_i64(
    set1_ptr: *const i64,
    set1_base: i64,
    set2_ptr: *const i64,
    set2_base: i64,
    out_ptr: *mut i64,
) -> i64 {
    unsafe {
        let base1 = set1_base as usize;
        let base2 = set2_base as usize;
        let count1 = *set1_ptr.add(base1 + 1) as usize;
        let count2 = *set2_ptr.add(base2 + 1) as usize;

        if count1 > 0 && !is_scalar_tag(*set1_ptr.add(base1 + 2)) {
            *out_ptr = super::compound_layout::TAG_SET;
            *out_ptr.add(1) = 0;
            return 2;
        }
        if count2 > 0 && !is_scalar_tag(*set2_ptr.add(base2 + 2)) {
            *out_ptr = super::compound_layout::TAG_SET;
            *out_ptr.add(1) = 0;
            return 2;
        }

        *out_ptr = super::compound_layout::TAG_SET;

        let mut result_count: usize = 0;
        let mut out_offset: usize = 2;

        for i in 0..count1 {
            let elem_tag_offset = base1 + 2 + i * 2;
            let elem_tag = *set1_ptr.add(elem_tag_offset);
            let elem_val = *set1_ptr.add(elem_tag_offset + 1);

            let mut found_in_set2 = false;
            for j in 0..count2 {
                let s2_val = *set2_ptr.add(base2 + 2 + j * 2 + 1);
                if s2_val == elem_val {
                    found_in_set2 = true;
                    break;
                }
            }

            if !found_in_set2 {
                *out_ptr.add(out_offset) = elem_tag;
                *out_ptr.add(out_offset + 1) = elem_val;
                out_offset += 2;
                result_count += 1;
            }
        }

        *out_ptr.add(1) = result_count as i64;

        out_offset as i64
    }
}

// ============================================================================
// Compound scratch buffer for JIT-constructed compound values
// ============================================================================

/// Sentinel base offset for compound scratch buffer references.
pub const COMPOUND_SCRATCH_BASE: i64 = 0x7FFF_0000_0000_0000_u64 as i64;

thread_local! {
    /// Thread-local scratch buffer for JIT-constructed compound values.
    static COMPOUND_SCRATCH: std::cell::RefCell<Vec<i64>> =
        std::cell::RefCell::new(Vec::with_capacity(64));
}

/// Clear the compound scratch buffer before each action evaluation.
pub fn clear_compound_scratch() {
    COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().clear());
}

/// RAII guard that clears the compound scratch buffer on drop.
pub struct CompoundScratchGuard;

impl Drop for CompoundScratchGuard {
    fn drop(&mut self) {
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().clear());
    }
}

/// Acquire a guard that will clear the compound scratch buffer when dropped.
#[must_use]
pub fn compound_scratch_guard() -> CompoundScratchGuard {
    clear_compound_scratch();
    CompoundScratchGuard
}

/// Read from the compound scratch buffer.
pub fn read_compound_scratch() -> Vec<i64> {
    COMPOUND_SCRATCH.with(|buf| buf.borrow().clone())
}

/// Runtime helper: construct a serialized record with all-scalar fields
/// and write it to the compound scratch buffer.
///
/// # Safety
///
/// All pointers must be valid for `count` elements.
pub extern "C" fn jit_record_new_scalar(
    name_ids_ptr: *const i64,
    values_ptr: *const i64,
    tags_ptr: *const i64,
    count: i64,
) -> i64 {
    let n = count as usize;
    COMPOUND_SCRATCH.with(|buf| {
        let mut scratch = buf.borrow_mut();
        let start_pos = scratch.len();

        scratch.push(super::compound_layout::TAG_RECORD);
        scratch.push(count);

        for i in 0..n {
            unsafe {
                let name_id = *name_ids_ptr.add(i);
                let tag = *tags_ptr.add(i);
                let value = *values_ptr.add(i);
                scratch.push(name_id);
                scratch.push(tag);
                scratch.push(value);
            }
        }

        COMPOUND_SCRATCH_BASE + start_pos as i64
    })
}

/// Runtime helper: construct a Tail sequence and write it to the compound scratch buffer.
///
/// # Safety
///
/// `state_ptr` must be valid.
pub extern "C" fn jit_seq_tail(
    state_ptr: *const i64,
    seq_base_slot: i64,
    is_direct_ptr: i64,
) -> i64 {
    unsafe {
        let ptr = if is_direct_ptr != 0 {
            state_ptr.add(seq_base_slot as usize)
        } else {
            state_ptr.add(seq_base_slot as usize)
        };

        let tag = *ptr;
        if tag != super::compound_layout::TAG_SEQ {
            return 0;
        }
        let count = *ptr.add(1) as usize;
        if count == 0 {
            return 0;
        }

        if count > 0 && !is_scalar_tag(*ptr.add(2)) {
            return 0;
        }

        let new_count = count - 1;

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            scratch.push(super::compound_layout::TAG_SEQ);
            scratch.push(new_count as i64);

            for i in 1..count {
                let elem_offset = 2 + i * 2;
                let elem_tag = *ptr.add(elem_offset);
                let elem_val = *ptr.add(elem_offset + 1);
                scratch.push(elem_tag);
                scratch.push(elem_val);
            }

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}

/// Runtime helper: construct an Append sequence and write it to the compound scratch buffer.
///
/// # Safety
///
/// `state_ptr` must be valid.
pub extern "C" fn jit_seq_append(
    state_ptr: *const i64,
    seq_base_slot: i64,
    is_direct_ptr: i64,
    elem_tag: i64,
    elem_val: i64,
) -> i64 {
    unsafe {
        let ptr = if is_direct_ptr != 0 {
            state_ptr.add(seq_base_slot as usize)
        } else {
            state_ptr.add(seq_base_slot as usize)
        };

        let tag = *ptr;
        if tag != super::compound_layout::TAG_SEQ {
            return 0;
        }
        let count = *ptr.add(1) as usize;

        if count > 0 && !is_scalar_tag(*ptr.add(2)) {
            return 0;
        }

        let new_count = count + 1;

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            scratch.push(super::compound_layout::TAG_SEQ);
            scratch.push(new_count as i64);

            for i in 0..count {
                let elem_offset = 2 + i * 2;
                let t = *ptr.add(elem_offset);
                let v = *ptr.add(elem_offset + 1);
                scratch.push(t);
                scratch.push(v);
            }

            scratch.push(elem_tag);
            scratch.push(elem_val);

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}

/// Runtime helper: compute the union of two serialized sets.
///
/// # Safety
///
/// All pointers must be valid.
pub extern "C" fn jit_set_union_i64(
    set1_ptr: *const i64,
    set1_base: i64,
    set2_ptr: *const i64,
    set2_base: i64,
) -> i64 {
    unsafe {
        let base1 = set1_base as usize;
        let base2 = set2_base as usize;
        let count1 = *set1_ptr.add(base1 + 1) as usize;
        let count2 = *set2_ptr.add(base2 + 1) as usize;

        if count1 > 0 && !is_scalar_tag(*set1_ptr.add(base1 + 2)) {
            return 0;
        }
        if count2 > 0 && !is_scalar_tag(*set2_ptr.add(base2 + 2)) {
            return 0;
        }

        let mut pairs: Vec<(i64, i64)> = Vec::with_capacity(count1 + count2);
        for i in 0..count1 {
            let offset = base1 + 2 + i * 2;
            let t = *set1_ptr.add(offset);
            let v = *set1_ptr.add(offset + 1);
            pairs.push((t, v));
        }

        for j in 0..count2 {
            let offset = base2 + 2 + j * 2;
            let t = *set2_ptr.add(offset);
            let v = *set2_ptr.add(offset + 1);
            let already_present = pairs.iter().any(|&(_, existing_v)| existing_v == v);
            if !already_present {
                pairs.push((t, v));
            }
        }

        pairs.sort_by_key(|&(_, v)| v);

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            scratch.push(super::compound_layout::TAG_SET);
            scratch.push(pairs.len() as i64);

            for (t, v) in &pairs {
                scratch.push(*t);
                scratch.push(*v);
            }

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}

/// External helper for integer exponentiation.
///
/// TLA+ semantics: 0^0 = 1, negative exponents return 0.
/// Uses binary exponentiation with wrapping multiplication
/// (overflow is not checked — matches TLC behavior for large results).
///
/// This mirrors the Cranelift-side helper in `tla-jit` (scalar_ops).
/// LLVM2 takes the function pointer directly when building its extern symbol
/// map, so this helper does not need a second exported `jit_pow_i64` symbol in
/// the final process image.
pub extern "C" fn jit_pow_i64(base: i64, exp: i64) -> i64 {
    if exp < 0 {
        return 0; // TLA+ convention: negative exponents yield 0
    }
    let mut result: i64 = 1;
    let mut b = base;
    let mut e = exp as u64;
    while e > 0 {
        if e & 1 == 1 {
            result = result.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compound_scratch_guard_clears_on_drop() {
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().push(42));
        {
            let _guard = CompoundScratchGuard;
            let scratch = read_compound_scratch();
            assert_eq!(scratch, vec![42]);
        }
        let scratch = read_compound_scratch();
        assert!(scratch.is_empty(), "scratch not cleared after guard drop");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compound_scratch_guard_fn_clears_and_returns() {
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().push(99));
        let _guard = compound_scratch_guard();
        let scratch = read_compound_scratch();
        assert!(
            scratch.is_empty(),
            "compound_scratch_guard() should clear on acquisition"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_scalar_elements() {
        use super::super::compound_layout::{TAG_INT, TAG_SET};
        let buf: Vec<i64> = vec![TAG_SET, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 10), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 20), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 30), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 99), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_empty_set() {
        use super::super::compound_layout::TAG_SET;
        let buf: Vec<i64> = vec![TAG_SET, 0];
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 42), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_compound_elements_returns_zero() {
        use super::super::compound_layout::{TAG_INT, TAG_RECORD, TAG_SET};
        let buf: Vec<i64> = vec![TAG_SET, 1, TAG_RECORD, 1, 100, TAG_INT, 1];
        assert_eq!(
            jit_set_contains_i64(buf.as_ptr(), 0, 1),
            0,
            "compound-element set should return 0 (fall back to interpreter)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_scalar_tag() {
        use super::super::compound_layout::*;
        assert!(is_scalar_tag(TAG_INT));
        assert!(is_scalar_tag(TAG_BOOL));
        assert!(is_scalar_tag(TAG_STRING));
        assert!(!is_scalar_tag(TAG_RECORD));
        assert!(!is_scalar_tag(TAG_SEQ));
        assert!(!is_scalar_tag(TAG_SET));
        assert!(!is_scalar_tag(TAG_FUNC));
        assert!(!is_scalar_tag(TAG_TUPLE));
        assert!(!is_scalar_tag(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_diff_compound_elements_returns_empty() {
        use super::super::compound_layout::{TAG_INT, TAG_RECORD, TAG_SET};
        let set1: Vec<i64> = vec![TAG_SET, 1, TAG_RECORD, 1, 100, TAG_INT, 1];
        let set2: Vec<i64> = vec![TAG_SET, 1, TAG_INT, 42];
        let mut out = vec![0i64; 10];
        let slots = jit_set_diff_i64(set1.as_ptr(), 0, set2.as_ptr(), 0, out.as_mut_ptr());
        assert_eq!(slots, 2);
        assert_eq!(out[0], TAG_SET);
        assert_eq!(out[1], 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_pow_i64_basic() {
        assert_eq!(jit_pow_i64(2, 10), 1024);
        assert_eq!(jit_pow_i64(3, 4), 81);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_pow_i64_zero_zero_equals_one() {
        // TLA+ convention: 0^0 = 1.
        assert_eq!(jit_pow_i64(0, 0), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_pow_i64_negative_exp_returns_zero() {
        assert_eq!(jit_pow_i64(5, -1), 0);
        assert_eq!(jit_pow_i64(2, -100), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_pow_i64_identity_exp_one() {
        assert_eq!(jit_pow_i64(7, 1), 7);
        assert_eq!(jit_pow_i64(-3, 1), -3);
    }
}
