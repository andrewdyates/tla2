// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stable ABI types for JIT function calls.
//!
//! This module defines the stable `extern "C"` interface between compiled JIT code
//! and the Rust runtime. The key types are:
//!
//! - [`JitStatus`] - Success or runtime error indicator
//! - [`JitRuntimeErrorKind`] - Enumeration of runtime error types
//! - [`JitCallOut`] - Output struct written by JIT'd functions
//!
//! # Design
//!
//! See `designs/2026-01-31-tla-jit-abi-and-runtime-errors.md` for the full design.
//!
//! # Overflow Strategy
//!
//! tla-jit uses **i64-only with overflow rejection** (Part of #746):
//!
//! | Implementation | Strategy | Behavior on Overflow |
//! |---------------|----------|---------------------|
//! | TLC (baseline) | 32-bit int | Runtime error |
//! | tla-check | i64 + BigInt | Silent promotion to BigInt |
//! | tla-jit | i64 only | `ArithmeticOverflow` runtime error |
//!
//! Current implementation (constant-only): preflight checks detect overflow at compile-time.
//! Future implementation (with variables): Cranelift overflow-detecting instructions.

/// Status indicator for JIT function calls.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JitStatus {
    /// Function completed successfully; value field is valid.
    Ok = 0,
    /// Runtime error occurred; err_kind and span fields are valid.
    RuntimeError = 1,
    /// JIT code hit a compound-value opcode (FuncApply, RecordGet, etc.)
    /// that cannot be evaluated natively. The caller must fall back to
    /// the bytecode VM or tree-walker for this state.
    /// Part of #3798.
    FallbackNeeded = 2,

    /// JIT code evaluated some scalar conjuncts of an invariant conjunction
    /// and they all passed, but could not evaluate the remaining compound
    /// conjuncts. The `conjuncts_passed` field indicates how many top-level
    /// conjuncts were verified by JIT. The caller should tree-walk only the
    /// compound conjuncts, skipping the already-verified scalar ones.
    ///
    /// This is returned when an invariant is a conjunction (And chain / short-
    /// circuit JumpFalse pattern) and the JIT can compile some conjuncts but
    /// not others. Unlike `FallbackNeeded` which requires full re-evaluation,
    /// `PartialPass` means the JIT-checked conjuncts definitively passed.
    PartialPass = 3,
}

/// Runtime error kinds that can occur during JIT'd expression evaluation.
///
/// These map to `EvalError` variants in `tla-check`:
/// - `DivisionByZero` → `EvalError::DivisionByZero`
/// - `ModulusNotPositive` → `EvalError::ModulusNotPositive`
/// - `TypeMismatch` → `EvalError::TypeError`
/// - `ArithmeticOverflow` → `EvalError::ArithmeticOverflow` (to be added)
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JitRuntimeErrorKind {
    /// Division by zero (x / 0 or x \div 0).
    /// TLC: EC.TLC_MODULE_DIVISION_BY_ZERO
    DivisionByZero = 1,

    /// Modulus with non-positive divisor (x % y where y <= 0).
    /// TLC: EC.TLC_MODULE_ARGUMENT_ERROR for "%"
    ModulusNotPositive = 2,

    /// Type mismatch (e.g., integer operation on boolean).
    /// TLC: EC.TLC_MODULE_ARGUMENT_ERROR
    TypeMismatch = 3,

    /// Arithmetic overflow (i64 bounds exceeded).
    /// TLC: EC.TLC_MODULE_OVERFLOW
    /// Part of #746 - matches TLC's overflow-as-error semantics.
    ArithmeticOverflow = 4,
}

impl JitRuntimeErrorKind {
    /// Returns a human-readable name for the error kind.
    pub fn name(&self) -> &'static str {
        match self {
            JitRuntimeErrorKind::DivisionByZero => "division by zero",
            JitRuntimeErrorKind::ModulusNotPositive => "modulus with non-positive divisor",
            JitRuntimeErrorKind::TypeMismatch => "type mismatch",
            JitRuntimeErrorKind::ArithmeticOverflow => "arithmetic overflow",
        }
    }
}

/// Output struct for JIT'd functions.
///
/// JIT'd functions write their result to this struct via an out-pointer.
/// This avoids relying on Rust ABI for the return value.
///
/// # Memory Layout
///
/// Uses `#[repr(C)]` for stable, portable layout across the JIT boundary.
/// Field offsets should be computed using `std::mem::offset_of!` when
/// generating Cranelift store instructions.
///
/// # Usage
///
/// ```text
/// let mut out = JitCallOut::default();
/// unsafe { jit_fn(&mut out); }
/// match out.status {
///     JitStatus::Ok => println!("Result: {}", out.value),
///     JitStatus::RuntimeError => println!("Error: {:?}", out.err_kind),
/// }
/// ```
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JitCallOut {
    /// Status indicator (ok vs runtime error vs partial pass).
    pub status: JitStatus,
    /// Result value (valid when status == Ok).
    pub value: i64,
    /// Runtime error kind (valid when status == RuntimeError).
    pub err_kind: JitRuntimeErrorKind,
    /// Span start byte offset (valid when status == RuntimeError).
    pub err_span_start: u32,
    /// Span end byte offset (valid when status == RuntimeError).
    pub err_span_end: u32,
    /// File ID for span (valid when status == RuntimeError).
    pub err_file_id: u32,
    /// Number of top-level conjuncts verified by JIT (valid when status == PartialPass).
    /// The caller can skip these conjuncts when falling back to the interpreter.
    pub conjuncts_passed: u32,
}

impl Default for JitCallOut {
    fn default() -> Self {
        JitCallOut {
            status: JitStatus::Ok,
            value: 0,
            err_kind: JitRuntimeErrorKind::DivisionByZero, // placeholder
            err_span_start: 0,
            err_span_end: 0,
            err_file_id: 0,
            conjuncts_passed: 0,
        }
    }
}

impl JitCallOut {
    /// Create a successful result.
    pub fn ok(value: i64) -> Self {
        JitCallOut {
            status: JitStatus::Ok,
            value,
            ..Default::default()
        }
    }

    /// Create a runtime error result.
    pub fn error(kind: JitRuntimeErrorKind, file_id: u32, span_start: u32, span_end: u32) -> Self {
        JitCallOut {
            status: JitStatus::RuntimeError,
            value: 0,
            err_kind: kind,
            err_span_start: span_start,
            err_span_end: span_end,
            err_file_id: file_id,
            conjuncts_passed: 0,
        }
    }

    /// Check if this result is successful.
    pub fn is_ok(&self) -> bool {
        self.status == JitStatus::Ok
    }

    /// Check if this result is an error.
    pub fn is_err(&self) -> bool {
        self.status == JitStatus::RuntimeError
    }

    /// Check if fallback to interpreter is needed.
    ///
    /// Returned when JIT code encounters a compound-value opcode
    /// (FuncApply, RecordGet) that cannot be evaluated natively.
    /// The caller should re-evaluate this state using the bytecode VM
    /// or tree-walker.
    /// Part of #3798.
    pub fn needs_fallback(&self) -> bool {
        self.status == JitStatus::FallbackNeeded || self.status == JitStatus::PartialPass
    }

    /// Check if the JIT evaluated some but not all conjuncts.
    ///
    /// Returned when an invariant is a conjunction and the JIT successfully
    /// verified the scalar conjuncts but could not evaluate compound ones.
    /// The `conjuncts_passed` field tells the caller how many top-level
    /// conjuncts were verified by JIT.
    pub fn is_partial_pass(&self) -> bool {
        self.status == JitStatus::PartialPass
    }

    /// Create a partial-pass result indicating how many conjuncts were verified.
    pub fn partial_pass(conjuncts_passed: u32) -> Self {
        JitCallOut {
            status: JitStatus::PartialPass,
            conjuncts_passed,
            ..Default::default()
        }
    }
}

// ============================================================================
// Runtime helpers for JIT-compiled code
// ============================================================================
// These `extern "C"` functions are called from JIT-generated native code via
// Cranelift's Import linkage. They bridge the gap between the flat i64 state
// buffer and compound TLA+ value operations that cannot be expressed as
// simple i64 loads.
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
/// This performs a linear scan over the serialized set. For small sets (typical
/// in TLA+ model checking: 2-20 elements), this is faster than hash lookup due
/// to no allocation overhead and good cache locality.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation. The caller guarantees `state_ptr` points to a valid
/// i64 buffer with at least `set_base_slot + 2 + count * 2` slots (for
/// scalar sets).
///
/// Part of #3999: guard against compound-element sets with variable stride.
#[no_mangle]
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
    tag == crate::compound_layout::TAG_INT
        || tag == crate::compound_layout::TAG_BOOL
        || tag == crate::compound_layout::TAG_STRING
}

/// Get a field value from a serialized record in the flat i64 state buffer.
///
/// The record is serialized as:
///   `[TAG_RECORD, field_count, name_id_0, TAG_0, val_0, name_id_1, TAG_1, val_1, ...]`
/// where each field occupies 1 (name_id) + 2 (TAG + value) = 3 slots for scalar fields.
///
/// Parameters:
///   - `state_ptr`: pointer to the start of the flat i64 state buffer
///   - `record_base_slot`: the slot index where TAG_RECORD begins
///   - `field_name_id`: the NameId (as i64) of the field to retrieve
///   - `found_out`: pointer to an i64; set to 1 if field found, 0 if not
///
/// Returns: the field's scalar value on success, or 0 if not found (check found_out).
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
#[no_mangle]
pub extern "C" fn jit_record_get_i64(
    state_ptr: *const i64,
    record_base_slot: i64,
    field_name_id: i64,
    found_out: *mut i64,
) -> i64 {
    // SAFETY: state_ptr is a valid pointer to the flat i64 state buffer,
    // guaranteed by the JIT caller. found_out is a valid stack-allocated i64.
    unsafe {
        let base = record_base_slot as usize;
        let field_count = *state_ptr.add(base + 1);
        let mut offset = base + 2;
        for _ in 0..field_count {
            let name_id = *state_ptr.add(offset);
            if name_id == field_name_id {
                // Found: value is at offset + 2 (skip name_id + TAG)
                *found_out = 1;
                return *state_ptr.add(offset + 2);
            }
            // Skip name_id (1) + TAG (1) + value (1) = 3 slots for scalar fields
            offset += 3;
        }
        *found_out = 0;
        0
    }
}

/// Apply a serialized function (lookup by key) in the flat i64 state buffer.
///
/// The function is serialized as:
///   `[TAG_FUNC, pair_count, key_TAG_0, key_val_0, val_TAG_0, val_val_0, ...]`
/// where each pair occupies 4 slots: key_TAG + key_val + val_TAG + val_val.
///
/// Parameters:
///   - `state_ptr`: pointer to the start of the flat i64 state buffer
///   - `func_base_slot`: the slot index where TAG_FUNC begins
///   - `key_value`: the scalar key to look up
///   - `found_out`: pointer to an i64; set to 1 if key found, 0 if not
///
/// Returns: the value associated with the key, or 0 if not found (check found_out).
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
#[no_mangle]
pub extern "C" fn jit_func_apply_i64(
    state_ptr: *const i64,
    func_base_slot: i64,
    key_value: i64,
    found_out: *mut i64,
) -> i64 {
    // SAFETY: state_ptr is a valid pointer to the flat i64 state buffer,
    // guaranteed by the JIT caller. found_out is a valid stack-allocated i64.
    unsafe {
        let base = func_base_slot as usize;
        let pair_count = *state_ptr.add(base + 1);
        let mut offset = base + 2;
        for _ in 0..pair_count {
            // key: [TAG, value] at offset, offset+1
            let key_val = *state_ptr.add(offset + 1);
            if key_val == key_value {
                // value: [TAG, value] at offset+2, offset+3
                *found_out = 1;
                return *state_ptr.add(offset + 3);
            }
            offset += 4; // skip key_TAG + key_val + val_TAG + val_val
        }
        *found_out = 0;
        0
    }
}

/// Get the element count from a serialized compound value (set, sequence, or function).
///
/// All compound types store their count at base_slot + 1:
///   `[TAG, count, ...]`
///
/// Parameters:
///   - `state_ptr`: pointer to the flat i64 state buffer
///   - `base_slot`: slot index where the compound value begins
///
/// Returns: the element/pair count.
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
#[no_mangle]
pub extern "C" fn jit_compound_count(state_ptr: *const i64, base_slot: i64) -> i64 {
    // SAFETY: state_ptr is valid, base_slot + 1 is within bounds.
    unsafe { *state_ptr.add(base_slot as usize + 1) }
}

/// Get an element from a serialized sequence at a given 0-based index.
///
/// Sequence format: `[TAG_SEQ, count, TAG_0, val_0, TAG_1, val_1, ...]`
/// Each scalar element occupies 2 slots (TAG + value).
///
/// Parameters:
///   - `state_ptr`: pointer to the flat i64 state buffer
///   - `seq_base_slot`: slot index where TAG_SEQ begins
///   - `index`: 0-based element index
///   - `found_out`: pointer to an i64; set to 1 if index is in bounds, 0 if not
///
/// Returns: the element's scalar value, or 0 if out of bounds (check found_out).
///
/// # Safety
///
/// TlaValue is heap-allocated and immutable; pointer valid for duration of
/// state evaluation.
#[no_mangle]
pub extern "C" fn jit_seq_get_i64(
    state_ptr: *const i64,
    seq_base_slot: i64,
    index: i64,
    found_out: *mut i64,
) -> i64 {
    // SAFETY: state_ptr is valid, bounds checked below. found_out is a valid
    // stack-allocated i64 guaranteed by the JIT caller.
    unsafe {
        let base = seq_base_slot as usize;
        let count = *state_ptr.add(base + 1);
        if index < 0 || index >= count {
            *found_out = 0;
            return 0; // out of bounds
        }
        // Element at 0-based index i is at: base + 2 + i * 2 + 1 (skip TAG)
        let slot = base + 2 + (index as usize) * 2 + 1;
        *found_out = 1;
        *state_ptr.add(slot)
    }
}

/// Runtime helper for FuncSet membership tests (JIT peephole optimization).
///
/// Checks whether a function value stored at `func_base_slot` in the JIT state
/// buffer belongs to `[domain -> range]`, where domain and range are described
/// by the remaining arguments.
///
/// # Safety
///
/// All pointers must be valid for the duration of the call. `state_ptr` points
/// to the JIT state buffer; `domain_elems_ptr` and (if range_kind == 0)
/// `range_lo_or_ptr` point to stack-allocated arrays from the JIT caller.
#[no_mangle]
pub extern "C" fn jit_func_set_membership_check(
    state_ptr: *const i64,
    func_base_slot: i64,
    domain_elems_ptr: *const i64,
    domain_count: i64,
    range_kind: i64,
    range_lo_or_ptr: i64,
    range_hi_or_count: i64,
) -> i64 {
    // SAFETY: state_ptr, domain_elems_ptr are valid pointers guaranteed by
    // the JIT caller. The state buffer is immutable during evaluation.
    unsafe {
        let base = func_base_slot as usize;

        // 1. Check TAG_FUNC
        let tag = *state_ptr.add(base);
        if tag != crate::compound_layout::TAG_FUNC {
            return 0;
        }

        // 2. Check pair count matches domain count
        let pair_count = *state_ptr.add(base + 1);
        if pair_count != domain_count {
            return 0;
        }

        let d_count = domain_count as usize;

        let mut offset = base + 2; // first pair starts here

        for _ in 0..d_count {
            let key_val = *state_ptr.add(offset + 1);

            // Check key is in domain
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

            // Check value is in range
            let range_val = *state_ptr.add(offset + 3);
            let val_in_range = match range_kind {
                0 => {
                    // Enum: range_lo_or_ptr is a pointer, range_hi_or_count is count
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
                    // Range: lo <= val <= hi
                    let lo = range_lo_or_ptr;
                    let hi = range_hi_or_count;
                    range_val >= lo && range_val <= hi
                }
                _ => false,
            };

            if !val_in_range {
                return 0;
            }

            offset += 4; // next pair: key_TAG + key_val + val_TAG + val_val
        }

        1 // all checks passed
    }
}

/// Compute the set difference of two serialized sets, writing the result into
/// a caller-provided output buffer.
///
/// Both sets are serialized as `[TAG_SET, count, TAG_0, val_0, TAG_1, val_1, ...]`
/// where each scalar element occupies 2 slots (TAG + value).
///
/// Parameters:
///   - `set1_ptr`: pointer to the first set's serialized buffer
///   - `set1_base`: slot offset of the first set within set1_ptr
///   - `set2_ptr`: pointer to the second set's serialized buffer
///   - `set2_base`: slot offset of the second set within set2_ptr
///   - `out_ptr`: pointer to the output buffer (must have space for set1's full serialized size)
///
/// Returns: the number of i64 slots written to `out_ptr` (always >= 2 for TAG_SET + count).
///
/// The result is `set1 \ set2`: elements in set1 that are not in set2.
/// Elements are compared by their scalar value (the value slot, not the tag).
///
/// # Safety
///
/// All pointers must be valid. `out_ptr` must have room for at least
/// `2 + count1 * 2` i64 slots (same size as set1).
#[no_mangle]
pub extern "C" fn jit_set_diff_i64(
    set1_ptr: *const i64,
    set1_base: i64,
    set2_ptr: *const i64,
    set2_base: i64,
    out_ptr: *mut i64,
) -> i64 {
    // SAFETY: All pointers guaranteed valid by JIT caller. Buffers are
    // thread-local or stack-allocated and immutable during evaluation.
    unsafe {
        let base1 = set1_base as usize;
        let base2 = set2_base as usize;
        let count1 = *set1_ptr.add(base1 + 1) as usize;
        let count2 = *set2_ptr.add(base2 + 1) as usize;

        // Guard: if either set contains compound elements, return an empty set
        // (count = 0). The 2-slot stride assumption only holds for scalar elements.
        // Part of #3999.
        if count1 > 0 && !is_scalar_tag(*set1_ptr.add(base1 + 2)) {
            *out_ptr = crate::compound_layout::TAG_SET;
            *out_ptr.add(1) = 0;
            return 2;
        }
        if count2 > 0 && !is_scalar_tag(*set2_ptr.add(base2 + 2)) {
            *out_ptr = crate::compound_layout::TAG_SET;
            *out_ptr.add(1) = 0;
            return 2;
        }

        // Write TAG_SET; count will be patched after we know result size
        *out_ptr = crate::compound_layout::TAG_SET;

        let mut result_count: usize = 0;
        let mut out_offset: usize = 2; // skip TAG_SET + count

        for i in 0..count1 {
            let elem_tag_offset = base1 + 2 + i * 2;
            let elem_tag = *set1_ptr.add(elem_tag_offset);
            let elem_val = *set1_ptr.add(elem_tag_offset + 1);

            // Check if elem_val is in set2
            let mut found_in_set2 = false;
            for j in 0..count2 {
                let s2_val = *set2_ptr.add(base2 + 2 + j * 2 + 1);
                if s2_val == elem_val {
                    found_in_set2 = true;
                    break;
                }
            }

            if !found_in_set2 {
                // Include this element in the result
                *out_ptr.add(out_offset) = elem_tag;
                *out_ptr.add(out_offset + 1) = elem_val;
                out_offset += 2;
                result_count += 1;
            }
        }

        // Patch the count field
        *out_ptr.add(1) = result_count as i64;

        out_offset as i64
    }
}

/// Function pointer type for JIT-compiled constant expressions (Phase 0 ABI).
///
/// Returns a single i64 value. Used by `JitContext::compile_expr` for
/// constant-folded TLA+ expressions with no state variables.
///
/// Uses `extern "C"` to match Cranelift's default calling convention
/// (`isa().default_call_conv()` = SystemV on Linux, AppleAarch64 on macOS).
pub type JitExprFn = unsafe extern "C" fn() -> i64;

/// Function pointer type for JIT'd expressions (Phase 1 ABI).
///
/// The function writes its output to the provided `JitCallOut` pointer.
/// This is the stable ABI boundary; callers should use a safe wrapper.
pub type JitFn0 = unsafe extern "C" fn(out: *mut JitCallOut);

/// Function pointer type for JIT'd invariant functions (Phase B2 ABI).
///
/// Parameters:
///   out: result output struct
///   state: pointer to current state array (array of i64, one per state variable)
///   state_len: number of state variables
///
/// The state array is a flattened representation: each state variable that is
/// Int is stored as its i64 value; Bool is stored as 0/1. Variable ordering
/// matches `VarIdx` from the bytecode compiler.
pub type JitInvariantFn =
    unsafe extern "C" fn(out: *mut JitCallOut, state: *const i64, state_len: u32);

/// Function pointer for JIT-compiled next-state relation.
///
/// The function evaluates the action and, if enabled, writes the primed
/// variable values to `state_out`. Returns 1 (TRUE/enabled) or 0 (FALSE/disabled)
/// in `out.value`.
pub type JitNextStateFn = unsafe extern "C" fn(
    out: *mut JitCallOut,
    state_in: *const i64,
    state_out: *mut i64,
    state_len: u32,
);

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_status_repr() {
        // Verify repr(u8) discriminants
        assert_eq!(JitStatus::Ok as u8, 0);
        assert_eq!(JitStatus::RuntimeError as u8, 1);
        assert_eq!(JitStatus::FallbackNeeded as u8, 2);
        assert_eq!(JitStatus::PartialPass as u8, 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_runtime_error_kind_repr() {
        // Verify repr(u8) discriminants match design doc
        assert_eq!(JitRuntimeErrorKind::DivisionByZero as u8, 1);
        assert_eq!(JitRuntimeErrorKind::ModulusNotPositive as u8, 2);
        assert_eq!(JitRuntimeErrorKind::TypeMismatch as u8, 3);
        assert_eq!(JitRuntimeErrorKind::ArithmeticOverflow as u8, 4);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_call_out_layout() {
        // Verify the struct has reasonable size
        // The exact size depends on alignment/padding, but should be <= 48 bytes
        // (added conjuncts_passed field)
        assert!(mem::size_of::<JitCallOut>() <= 48);

        // Verify alignment is suitable for C interop (at least 8-byte aligned for i64)
        assert!(mem::align_of::<JitCallOut>() >= 8);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_call_out_ok() {
        let out = JitCallOut::ok(42);
        assert!(out.is_ok());
        assert!(!out.is_err());
        assert_eq!(out.value, 42);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_jit_call_out_error() {
        let out = JitCallOut::error(JitRuntimeErrorKind::ArithmeticOverflow, 1, 10, 20);
        assert!(!out.is_ok());
        assert!(out.is_err());
        assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
        assert_eq!(out.err_file_id, 1);
        assert_eq!(out.err_span_start, 10);
        assert_eq!(out.err_span_end, 20);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_error_kind_names() {
        assert_eq!(
            JitRuntimeErrorKind::DivisionByZero.name(),
            "division by zero"
        );
        assert_eq!(
            JitRuntimeErrorKind::ArithmeticOverflow.name(),
            "arithmetic overflow"
        );
    }

    // ====================================================================
    // CompoundScratchGuard tests (Part of #3998)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compound_scratch_guard_clears_on_drop() {
        // Populate scratch, then drop guard — buffer should be empty.
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().push(42));
        {
            let _guard = CompoundScratchGuard;
            // Guard exists; scratch still has data
            let scratch = read_compound_scratch();
            assert_eq!(scratch, vec![42]);
        }
        // Guard dropped — scratch should be empty
        let scratch = read_compound_scratch();
        assert!(scratch.is_empty(), "scratch not cleared after guard drop");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compound_scratch_guard_fn_clears_and_returns() {
        // compound_scratch_guard() should clear first, then return guard.
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().push(99));
        let _guard = compound_scratch_guard();
        // Guard constructor clears existing data
        let scratch = read_compound_scratch();
        assert!(
            scratch.is_empty(),
            "compound_scratch_guard() should clear on acquisition"
        );
    }

    // ====================================================================
    // jit_set_contains_i64 compound guard tests (Part of #3999)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_scalar_elements() {
        use crate::compound_layout::{TAG_INT, TAG_SET};
        // Set: {10, 20, 30}
        let buf: Vec<i64> = vec![TAG_SET, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 10), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 20), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 30), 1);
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 99), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_empty_set() {
        use crate::compound_layout::TAG_SET;
        let buf: Vec<i64> = vec![TAG_SET, 0];
        assert_eq!(jit_set_contains_i64(buf.as_ptr(), 0, 42), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_contains_compound_elements_returns_zero() {
        use crate::compound_layout::{TAG_INT, TAG_RECORD, TAG_SET};
        // Set containing a record element: {[a |-> 1]}
        // TAG_SET, count=1, TAG_RECORD, 1(field_count), name_id, TAG_INT, 1
        let buf: Vec<i64> = vec![TAG_SET, 1, TAG_RECORD, 1, 100, TAG_INT, 1];
        // Should return 0 (not found) because first element tag is compound
        assert_eq!(
            jit_set_contains_i64(buf.as_ptr(), 0, 1),
            0,
            "compound-element set should return 0 (fall back to interpreter)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_scalar_tag() {
        use crate::compound_layout::*;
        assert!(is_scalar_tag(TAG_INT));
        assert!(is_scalar_tag(TAG_BOOL));
        assert!(is_scalar_tag(TAG_STRING));
        assert!(!is_scalar_tag(TAG_RECORD));
        assert!(!is_scalar_tag(TAG_SEQ));
        assert!(!is_scalar_tag(TAG_SET));
        assert!(!is_scalar_tag(TAG_FUNC));
        assert!(!is_scalar_tag(TAG_TUPLE));
        assert!(!is_scalar_tag(0)); // unknown tag
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_diff_compound_elements_returns_empty() {
        use crate::compound_layout::{TAG_INT, TAG_RECORD, TAG_SET};
        // set1 contains a compound element
        let set1: Vec<i64> = vec![TAG_SET, 1, TAG_RECORD, 1, 100, TAG_INT, 1];
        // set2 is scalar
        let set2: Vec<i64> = vec![TAG_SET, 1, TAG_INT, 42];
        let mut out = vec![0i64; 10];
        let slots = jit_set_diff_i64(set1.as_ptr(), 0, set2.as_ptr(), 0, out.as_mut_ptr());
        // Should return empty set (2 slots: TAG_SET + 0 count)
        assert_eq!(slots, 2);
        assert_eq!(out[0], TAG_SET);
        assert_eq!(out[1], 0); // 0 elements
    }
}

// ============================================================================
// Compound scratch buffer for JIT-constructed compound values
// ============================================================================
// When the JIT constructs a NEW compound value (e.g., RecordNew), it can't
// write into state_in (which has a fixed layout) or state_out (which holds
// scalar offsets). Instead, it writes serialized data to a thread-local
// scratch buffer. The unflatten path reads from this buffer for compound
// variable write-back.
//
// Offset encoding: offsets into the scratch buffer are stored as
// `COMPOUND_SCRATCH_BASE + position`. The unflatten path detects this
// sentinel range and reads from the scratch buffer instead of state_in.

/// Sentinel base offset for compound scratch buffer references.
///
/// Any offset >= this value indicates a reference into the thread-local
/// compound scratch buffer at position `offset - COMPOUND_SCRATCH_BASE`.
pub const COMPOUND_SCRATCH_BASE: i64 = 0x7FFF_0000_0000_0000_u64 as i64;

thread_local! {
    /// Thread-local scratch buffer for JIT-constructed compound values.
    ///
    /// Cleared before each action evaluation via `clear_compound_scratch()`.
    /// Runtime helpers like `jit_record_new_scalar` append serialized data
    /// here and return the offset (encoded with `COMPOUND_SCRATCH_BASE`).
    static COMPOUND_SCRATCH: std::cell::RefCell<Vec<i64>> =
        std::cell::RefCell::new(Vec::with_capacity(64));
}

/// Clear the compound scratch buffer before each action evaluation.
///
/// Called from the BFS hot path before each JIT action dispatch. Must be
/// called to prevent stale data from previous evaluations leaking into
/// the current one.
pub fn clear_compound_scratch() {
    COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().clear());
}

/// RAII guard that clears the compound scratch buffer on drop.
///
/// Ensures cleanup even if the caller panics between populating and consuming
/// the scratch buffer. Acquire via [`compound_scratch_guard()`] before any path
/// that writes to `COMPOUND_SCRATCH`.
///
/// Part of #3998: prevents stale scratch data from leaking across evaluations
/// when caller discipline fails (e.g., early return, panic).
pub(crate) struct CompoundScratchGuard;

impl Drop for CompoundScratchGuard {
    fn drop(&mut self) {
        COMPOUND_SCRATCH.with(|buf| buf.borrow_mut().clear());
    }
}

/// Acquire a guard that will clear the compound scratch buffer when dropped.
///
/// Usage:
/// ```ignore
/// let _guard = compound_scratch_guard();
/// // ... populate and read from COMPOUND_SCRATCH ...
/// // buffer is cleared when _guard goes out of scope, even on panic
/// ```
#[must_use]
pub(crate) fn compound_scratch_guard() -> CompoundScratchGuard {
    clear_compound_scratch();
    CompoundScratchGuard
}

/// Read from the compound scratch buffer at the given position.
///
/// Returns `None` if the position is out of bounds.
/// Used by the unflatten path to deserialize JIT-constructed compound values.
pub fn read_compound_scratch() -> Vec<i64> {
    COMPOUND_SCRATCH.with(|buf| buf.borrow().clone())
}

/// Runtime helper: construct a serialized record with all-scalar fields
/// and write it to the compound scratch buffer.
///
/// Parameters:
///   - `name_ids_ptr`: pointer to an array of `count` field name IDs (i64, sorted by NameId)
///   - `values_ptr`: pointer to an array of `count` field values (i64, scalar)
///   - `tags_ptr`: pointer to an array of `count` field type tags (i64)
///   - `count`: number of fields
///
/// Returns: the encoded offset (`COMPOUND_SCRATCH_BASE + start_pos`) where
/// the serialized record begins in the scratch buffer.
///
/// # Serialized format
///
/// ```text
/// slot[0] = TAG_RECORD (1)
/// slot[1] = field_count
/// slot[2] = name_id_0
/// slot[3] = tag_0
/// slot[4] = value_0
/// slot[5] = name_id_1
/// slot[6] = tag_1
/// slot[7] = value_1
/// ...
/// ```
///
/// # Safety
///
/// All pointers must be valid for `count` elements. Called from JIT-compiled
/// code via Cranelift's Import linkage.
#[no_mangle]
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

        // Write TAG_RECORD + field_count
        scratch.push(crate::compound_layout::TAG_RECORD);
        scratch.push(count);

        // Write each field: name_id, tag, value
        for i in 0..n {
            // SAFETY: pointers are valid for `count` elements, guaranteed by JIT caller.
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

/// Runtime helper: construct a Tail sequence (all elements except the first)
/// and write it to the compound scratch buffer.
///
/// Parameters:
///   - `state_ptr`: pointer to the flat i64 state buffer (or direct ptr)
///   - `seq_base_slot`: slot offset where TAG_SEQ begins
///   - `is_direct_ptr`: 1 if `state_ptr` IS the direct pointer to sequence data,
///     0 if `state_ptr` is the state buffer and `seq_base_slot` is the offset
///
/// Returns: encoded offset (`COMPOUND_SCRATCH_BASE + start_pos`) for the new sequence,
/// or 0 if the input sequence is empty (caller should emit FallbackNeeded).
///
/// Scalar-element sequences only: each element is TAG + value = 2 slots.
/// For compound elements, returns 0 (caller falls back to interpreter).
///
/// # Safety
///
/// `state_ptr` must be valid. Called from JIT-compiled code via Cranelift Import.
/// Part of #4030: JIT native Tail support.
#[no_mangle]
pub extern "C" fn jit_seq_tail(
    state_ptr: *const i64,
    seq_base_slot: i64,
    is_direct_ptr: i64,
) -> i64 {
    // SAFETY: state_ptr is valid, guaranteed by JIT caller.
    unsafe {
        let base = if is_direct_ptr != 0 {
            0usize
        } else {
            seq_base_slot as usize
        };
        let ptr = if is_direct_ptr != 0 {
            // Direct pointer: seq_base_slot encodes the slot offset from the pointer
            state_ptr.add(seq_base_slot as usize)
        } else {
            state_ptr.add(base)
        };

        let tag = *ptr;
        if tag != crate::compound_layout::TAG_SEQ {
            return 0;
        }
        let count = *ptr.add(1) as usize;
        if count == 0 {
            return 0; // empty sequence — Tail is an error
        }

        // Guard: only handle scalar elements (2-slot stride)
        if count > 0 && !is_scalar_tag(*ptr.add(2)) {
            return 0;
        }

        let new_count = count - 1;

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            // Write TAG_SEQ + new_count
            scratch.push(crate::compound_layout::TAG_SEQ);
            scratch.push(new_count as i64);

            // Copy elements 1..count (skip element 0)
            for i in 1..count {
                let elem_offset = 2 + i * 2; // each scalar element = 2 slots
                let elem_tag = *ptr.add(elem_offset);
                let elem_val = *ptr.add(elem_offset + 1);
                scratch.push(elem_tag);
                scratch.push(elem_val);
            }

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}

/// Runtime helper: construct an Append sequence (original + new element)
/// and write it to the compound scratch buffer.
///
/// Parameters:
///   - `state_ptr`: pointer to the flat i64 state buffer (or direct ptr)
///   - `seq_base_slot`: slot offset where TAG_SEQ begins
///   - `is_direct_ptr`: 1 if direct pointer mode, 0 if state buffer offset mode
///   - `elem_tag`: type tag for the new element (TAG_INT, TAG_BOOL, TAG_STRING)
///   - `elem_val`: the scalar value to append
///
/// Returns: encoded offset (`COMPOUND_SCRATCH_BASE + start_pos`) for the new sequence,
/// or 0 if the input is not a scalar-element sequence.
///
/// # Safety
///
/// `state_ptr` must be valid. Called from JIT-compiled code via Cranelift Import.
/// Part of #4030: JIT native Append support.
#[no_mangle]
pub extern "C" fn jit_seq_append(
    state_ptr: *const i64,
    seq_base_slot: i64,
    is_direct_ptr: i64,
    elem_tag: i64,
    elem_val: i64,
) -> i64 {
    // SAFETY: state_ptr is valid, guaranteed by JIT caller.
    unsafe {
        let ptr = if is_direct_ptr != 0 {
            state_ptr.add(seq_base_slot as usize)
        } else {
            state_ptr.add(seq_base_slot as usize)
        };

        let tag = *ptr;
        if tag != crate::compound_layout::TAG_SEQ {
            return 0;
        }
        let count = *ptr.add(1) as usize;

        // Guard: only handle scalar elements (2-slot stride)
        if count > 0 && !is_scalar_tag(*ptr.add(2)) {
            return 0;
        }

        let new_count = count + 1;

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            // Write TAG_SEQ + new_count
            scratch.push(crate::compound_layout::TAG_SEQ);
            scratch.push(new_count as i64);

            // Copy all existing elements
            for i in 0..count {
                let elem_offset = 2 + i * 2;
                let t = *ptr.add(elem_offset);
                let v = *ptr.add(elem_offset + 1);
                scratch.push(t);
                scratch.push(v);
            }

            // Append the new element
            scratch.push(elem_tag);
            scratch.push(elem_val);

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}

/// Runtime helper: compute the union of two serialized sets and write
/// the result to the compound scratch buffer.
///
/// Parameters:
///   - `set1_ptr`: pointer to the first set's buffer
///   - `set1_base`: slot offset of the first set within set1_ptr
///   - `set2_ptr`: pointer to the second set's buffer
///   - `set2_base`: slot offset of the second set within set2_ptr
///
/// Returns: encoded offset (`COMPOUND_SCRATCH_BASE + start_pos`) for the result set,
/// or 0 if either set contains compound elements.
///
/// The result is `set1 \union set2`: all elements from both sets, deduplicated
/// by scalar value. Elements are sorted by value for canonical ordering.
///
/// # Safety
///
/// All pointers must be valid. Called from JIT-compiled code via Cranelift Import.
/// Part of #4030: JIT native SetUnion support.
#[no_mangle]
pub extern "C" fn jit_set_union_i64(
    set1_ptr: *const i64,
    set1_base: i64,
    set2_ptr: *const i64,
    set2_base: i64,
) -> i64 {
    // SAFETY: All pointers guaranteed valid by JIT caller.
    unsafe {
        let base1 = set1_base as usize;
        let base2 = set2_base as usize;
        let count1 = *set1_ptr.add(base1 + 1) as usize;
        let count2 = *set2_ptr.add(base2 + 1) as usize;

        // Guard: compound elements not supported
        if count1 > 0 && !is_scalar_tag(*set1_ptr.add(base1 + 2)) {
            return 0;
        }
        if count2 > 0 && !is_scalar_tag(*set2_ptr.add(base2 + 2)) {
            return 0;
        }

        // Collect all (tag, val) pairs from set1
        let mut pairs: Vec<(i64, i64)> = Vec::with_capacity(count1 + count2);
        for i in 0..count1 {
            let offset = base1 + 2 + i * 2;
            let t = *set1_ptr.add(offset);
            let v = *set1_ptr.add(offset + 1);
            pairs.push((t, v));
        }

        // Add elements from set2 that are not already in the result
        for j in 0..count2 {
            let offset = base2 + 2 + j * 2;
            let t = *set2_ptr.add(offset);
            let v = *set2_ptr.add(offset + 1);
            let already_present = pairs.iter().any(|&(_, existing_v)| existing_v == v);
            if !already_present {
                pairs.push((t, v));
            }
        }

        // Sort by value for canonical ordering (TLA+ sets are sorted)
        pairs.sort_by_key(|&(_, v)| v);

        COMPOUND_SCRATCH.with(|buf| {
            let mut scratch = buf.borrow_mut();
            let start_pos = scratch.len();

            scratch.push(crate::compound_layout::TAG_SET);
            scratch.push(pairs.len() as i64);

            for (t, v) in &pairs {
                scratch.push(*t);
                scratch.push(*v);
            }

            COMPOUND_SCRATCH_BASE + start_pos as i64
        })
    }
}
