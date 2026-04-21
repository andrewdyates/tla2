// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Flat state buffer — maps TLA+ state variables to contiguous i64 arrays.
//!
//! JIT-compiled code operates on flat `[i64]` arrays where each state variable
//! occupies a fixed region of i64 slots. This module provides:
//!
//! 1. **`FlatStateSchema`** — computed at spec load time, maps each variable
//!    index to its starting offset and encoding strategy.
//! 2. **`FlatState`** — a typed wrapper around `Vec<i64>` that knows its schema.
//! 3. **Conversion functions** — `state_to_flat()` and `flat_to_state()` bridge
//!    between tree-structured `Value` states and flat i64 representations.
//!
//! # Encoding Strategy
//!
//! - **Booleans**: 0 (false) or 1 (true) — 1 slot
//! - **Integers**: direct i64 value — 1 slot (BigInts that overflow i64 cause error)
//! - **Strings/ModelValues**: interned NameId as i64 — 1 slot
//! - **Compound types** (records, sets, sequences, functions, tuples): serialized
//!   inline using the self-describing tagged format from [`crate::compound_layout`].
//!   The first slot at the variable's offset is a pointer (byte offset) into
//!   the compound region at the end of the buffer.
//!
//! # Layout
//!
//! ```text
//! [ var_0 | var_1 | ... | var_N-1 | compound_region... ]
//!   ^                                ^
//!   |                                |
//!   Fixed-size index region          Variable-size compound data
//!   (one i64 per variable)           (tagged serialized values)
//! ```
//!
//! For specs with only scalar state variables (booleans and integers), the
//! compound region is empty and the total buffer length equals the variable
//! count. This is the fast path — no serialization overhead.
//!
//! Part of #3986: JIT V2 Phase 3 — Flat State Buffer.

use super::compound_layout::{
    deserialize_value, infer_var_layout, serialize_value, CompoundLayout, StateLayout, VarLayout,
};
use super::error::JitRuntimeError;
use tla_value::Value;

// ============================================================================
// FlatStateSchema — compile-time descriptor
// ============================================================================

/// Per-variable encoding in the flat state buffer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarEncoding {
    /// Boolean: 0 or 1 in a single i64 slot.
    Bool,
    /// Integer: direct i64 value in a single i64 slot.
    Int,
    /// String or ModelValue: interned NameId stored as i64 in a single slot.
    String,
    /// Compound value: the index slot holds a byte offset into the compound
    /// region. The actual data is serialized inline at that offset using the
    /// tagged format from `compound_layout`.
    Compound,
}

/// Schema for converting TLA+ states to flat i64 buffers.
///
/// Computed once from the initial state's variable types. Each variable gets
/// a `VarEncoding` that determines how it is read/written in the flat buffer.
/// The schema also tracks whether all variables are scalar (enabling the
/// zero-serialization fast path).
#[derive(Debug, Clone)]
pub struct FlatStateSchema {
    /// Per-variable encoding, indexed by variable position.
    encodings: Vec<VarEncoding>,
    /// True when all variables are Bool/Int/String (no compound serialization needed).
    all_scalar: bool,
    /// Total number of variables (equals buffer length for all-scalar specs).
    var_count: usize,
}

impl FlatStateSchema {
    /// Build a schema from the initial state values.
    ///
    /// Inspects each value to determine its encoding. This is called once
    /// during model checking initialization, not on every state.
    pub fn from_initial_state(values: &[Value]) -> Self {
        let mut encodings = Vec::with_capacity(values.len());
        let mut all_scalar = true;

        for value in values {
            let encoding = match infer_var_layout(value) {
                VarLayout::ScalarBool => VarEncoding::Bool,
                VarLayout::ScalarInt => VarEncoding::Int,
                VarLayout::Compound(CompoundLayout::String) => VarEncoding::String,
                VarLayout::Compound(_) => {
                    all_scalar = false;
                    VarEncoding::Compound
                }
            };
            encodings.push(encoding);
        }

        FlatStateSchema {
            var_count: encodings.len(),
            all_scalar,
            encodings,
        }
    }

    /// Build a schema from an existing `StateLayout`.
    pub fn from_state_layout(layout: &StateLayout) -> Self {
        let mut encodings = Vec::with_capacity(layout.var_count());
        let mut all_scalar = true;

        for var_layout in layout.iter() {
            let encoding = match var_layout {
                VarLayout::ScalarBool => VarEncoding::Bool,
                VarLayout::ScalarInt => VarEncoding::Int,
                VarLayout::Compound(CompoundLayout::String) => VarEncoding::String,
                VarLayout::Compound(_) => {
                    all_scalar = false;
                    VarEncoding::Compound
                }
            };
            encodings.push(encoding);
        }

        FlatStateSchema {
            var_count: encodings.len(),
            all_scalar,
            encodings,
        }
    }

    /// Number of state variables.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.var_count
    }

    /// True when all variables are scalar (Bool/Int/String).
    ///
    /// When true, the flat buffer is exactly `var_count` i64 slots with no
    /// compound region, enabling the zero-serialization fast path.
    #[must_use]
    pub fn is_all_scalar(&self) -> bool {
        self.all_scalar
    }

    /// Get the encoding for a specific variable.
    #[must_use]
    pub fn encoding(&self, var_idx: usize) -> Option<&VarEncoding> {
        self.encodings.get(var_idx)
    }

    /// Iterate over all variable encodings.
    pub fn encodings(&self) -> &[VarEncoding] {
        &self.encodings
    }

    /// Minimum buffer size (index slots only, no compound data).
    #[must_use]
    pub fn index_slot_count(&self) -> usize {
        self.var_count
    }
}

// ============================================================================
// FlatState — owned flat buffer with schema
// ============================================================================

/// A TLA+ state represented as a flat i64 array.
///
/// Wraps a contiguous `Vec<i64>` buffer with a reference to its schema.
/// The buffer layout is:
///
/// - Slots `0..var_count`: one i64 per variable (scalar value or compound offset)
/// - Slots `var_count..`: compound region (serialized compound values)
///
/// For all-scalar specs, the buffer length equals `var_count`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlatState {
    /// The flat i64 buffer.
    buf: Vec<i64>,
    /// Number of state variables (= index slot count).
    var_count: usize,
}

impl FlatState {
    /// Create an empty flat state with the given variable count.
    ///
    /// All index slots are initialized to 0. No compound region.
    pub fn zeroed(var_count: usize) -> Self {
        FlatState {
            buf: vec![0i64; var_count],
            var_count,
        }
    }

    /// Create a flat state from an existing buffer.
    ///
    /// The buffer must have at least `var_count` slots.
    pub fn from_buf(buf: Vec<i64>, var_count: usize) -> Result<Self, JitRuntimeError> {
        if buf.len() < var_count {
            return Err(JitRuntimeError::CompileError(format!(
                "flat state buffer has {} slots, need at least {var_count}",
                buf.len()
            )));
        }
        Ok(FlatState { buf, var_count })
    }

    /// Get the raw i64 buffer.
    #[must_use]
    pub fn as_slice(&self) -> &[i64] {
        &self.buf
    }

    /// Get a mutable reference to the raw i64 buffer.
    pub fn as_mut_slice(&mut self) -> &mut [i64] {
        &mut self.buf
    }

    /// Get the raw buffer as a pointer (for passing to JIT-compiled code).
    #[must_use]
    pub fn as_ptr(&self) -> *const i64 {
        self.buf.as_ptr()
    }

    /// Number of state variables.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.var_count
    }

    /// Total buffer length including compound region.
    #[must_use]
    pub fn total_slots(&self) -> usize {
        self.buf.len()
    }

    /// Read a scalar i64 value at the given variable index.
    ///
    /// For Bool variables, returns 0 or 1.
    /// For Int variables, returns the integer value.
    /// For String variables, returns the interned NameId as i64.
    /// For Compound variables, returns the offset into the compound region.
    #[must_use]
    pub fn get_slot(&self, var_idx: usize) -> Option<i64> {
        self.buf.get(var_idx).copied()
    }

    /// Write a scalar i64 value at the given variable index.
    pub fn set_slot(&mut self, var_idx: usize, value: i64) {
        if var_idx < self.buf.len() {
            self.buf[var_idx] = value;
        }
    }

    /// Consume this FlatState and return the underlying buffer.
    pub fn into_buf(self) -> Vec<i64> {
        self.buf
    }

    /// Compute the xxh3_64 fingerprint of this flat state.
    ///
    /// Hashes the entire buffer (index + compound region) for dedup.
    #[must_use]
    pub fn fingerprint(&self) -> u64 {
        super::fingerprint::jit_xxh3_fingerprint_64(self.buf.as_ptr(), self.buf.len() as u32)
    }
}

// ============================================================================
// Conversion: Value[] -> FlatState
// ============================================================================

/// Convert a TLA+ state (array of Values) to a flat i64 buffer.
///
/// Uses the schema to determine the encoding for each variable:
/// - Bool/Int/String: written directly into the index slot
/// - Compound: serialized into the compound region; index slot holds the offset
///
/// # Fast path
///
/// When `schema.is_all_scalar()`, no compound serialization occurs and the
/// buffer is exactly `var_count` slots. This is the common case for many
/// TLA+ specs (e.g., EWD998, DiningPhilosophers).
pub fn state_to_flat(
    values: &[Value],
    schema: &FlatStateSchema,
) -> Result<FlatState, JitRuntimeError> {
    if values.len() != schema.var_count() {
        return Err(JitRuntimeError::CompileError(format!(
            "state has {} values but schema expects {}",
            values.len(),
            schema.var_count()
        )));
    }

    let var_count = schema.var_count();
    let mut buf = Vec::with_capacity(var_count);

    // Phase 1: Fill index slots.
    let mut has_compound = false;
    for (val, enc) in values.iter().zip(schema.encodings()) {
        match enc {
            VarEncoding::Bool => {
                let b = match val {
                    Value::Bool(b) => *b,
                    _ => {
                        return Err(JitRuntimeError::CompileError(format!(
                            "expected Bool, got {val:?}"
                        )));
                    }
                };
                buf.push(i64::from(b));
            }
            VarEncoding::Int => {
                let n = value_to_i64(val)?;
                buf.push(n);
            }
            VarEncoding::String => {
                let name_id = match val {
                    Value::String(s) => tla_core::intern_name(s),
                    Value::ModelValue(s) => tla_core::intern_name(s),
                    _ => {
                        return Err(JitRuntimeError::CompileError(format!(
                            "expected String/ModelValue, got {val:?}"
                        )));
                    }
                };
                buf.push(name_id.0 as i64);
            }
            VarEncoding::Compound => {
                buf.push(0); // placeholder — will be patched in Phase 2
                has_compound = true;
            }
        }
    }

    // Phase 2: Serialize compound values into the compound region.
    if has_compound {
        for (var_idx, (val, enc)) in values.iter().zip(schema.encodings()).enumerate() {
            if *enc != VarEncoding::Compound {
                continue;
            }
            let compound_offset = buf.len();
            buf[var_idx] = compound_offset as i64;
            serialize_value(val, &mut buf)?;
        }
    }

    Ok(FlatState { buf, var_count })
}

/// Convert a TLA+ state to a flat i64 buffer, reusing an existing buffer.
///
/// This avoids allocation in the BFS hot path by clearing and reusing `buf`.
/// Returns `true` on success, `false` if a compound value cannot be serialized.
pub fn state_to_flat_reuse(
    values: &[Value],
    schema: &FlatStateSchema,
    buf: &mut Vec<i64>,
) -> bool {
    buf.clear();

    if values.len() != schema.var_count() {
        return false;
    }

    let var_count = schema.var_count();
    if buf.capacity() < var_count {
        buf.reserve(var_count - buf.capacity());
    }

    // Phase 1: Fill index slots.
    let mut has_compound = false;
    for (val, enc) in values.iter().zip(schema.encodings()) {
        match enc {
            VarEncoding::Bool => {
                let b = matches!(val, Value::Bool(true));
                buf.push(i64::from(b));
            }
            VarEncoding::Int => {
                let n = match value_to_i64(val) {
                    Ok(n) => n,
                    Err(_) => return false,
                };
                buf.push(n);
            }
            VarEncoding::String => {
                let name_id = match val {
                    Value::String(s) => tla_core::intern_name(s),
                    Value::ModelValue(s) => tla_core::intern_name(s),
                    _ => return false,
                };
                buf.push(name_id.0 as i64);
            }
            VarEncoding::Compound => {
                buf.push(0);
                has_compound = true;
            }
        }
    }

    // Phase 2: Serialize compound values.
    if has_compound {
        for (var_idx, (val, enc)) in values.iter().zip(schema.encodings()).enumerate() {
            if *enc != VarEncoding::Compound {
                continue;
            }
            let compound_offset = buf.len();
            buf[var_idx] = compound_offset as i64;
            if serialize_value(val, buf).is_err() {
                buf.clear();
                return false;
            }
        }
    }

    true
}

// ============================================================================
// Conversion: FlatState -> Value[]
// ============================================================================

/// Convert a flat i64 buffer back to TLA+ state values.
///
/// Uses the schema to determine how to decode each variable:
/// - Bool: slot value 0 -> false, nonzero -> true
/// - Int: slot value as SmallInt
/// - String: slot value as NameId, resolved to string
/// - Compound: slot value is offset into compound region; deserialized using
///   the tagged format
pub fn flat_to_state(
    flat: &FlatState,
    schema: &FlatStateSchema,
) -> Result<Vec<Value>, JitRuntimeError> {
    flat_to_state_from_slice(flat.as_slice(), schema, flat.var_count())
}

/// Convert a raw i64 slice back to TLA+ state values.
///
/// Lower-level version of `flat_to_state` that operates on a raw slice.
/// Used by the BFS step output iterator to avoid materializing `FlatState`.
pub fn flat_to_state_from_slice(
    buf: &[i64],
    schema: &FlatStateSchema,
    var_count: usize,
) -> Result<Vec<Value>, JitRuntimeError> {
    if buf.len() < var_count {
        return Err(JitRuntimeError::CompileError(format!(
            "flat buffer has {} slots, need at least {var_count}",
            buf.len()
        )));
    }

    let mut values = Vec::with_capacity(var_count);

    for (var_idx, enc) in schema.encodings().iter().enumerate() {
        let slot_val = buf[var_idx];
        let value = match enc {
            VarEncoding::Bool => Value::Bool(slot_val != 0),
            VarEncoding::Int => Value::SmallInt(slot_val),
            VarEncoding::String => {
                let name_id = tla_core::NameId(slot_val as u32);
                let s = tla_core::resolve_name_id(name_id);
                Value::String(s)
            }
            VarEncoding::Compound => {
                let offset = slot_val as usize;
                if offset >= buf.len() {
                    return Err(JitRuntimeError::CompileError(format!(
                        "compound offset {offset} out of range (buf len {})",
                        buf.len()
                    )));
                }
                let (val, _consumed) = deserialize_value(buf, offset)?;
                val
            }
        };
        values.push(value);
    }

    Ok(values)
}

// ============================================================================
// Helpers
// ============================================================================

/// Convert a `Value` to an i64, handling SmallInt and BigInt.
fn value_to_i64(value: &Value) -> Result<i64, JitRuntimeError> {
    match value {
        Value::SmallInt(n) => Ok(*n),
        Value::Int(n) => {
            use num_traits::ToPrimitive;
            n.to_i64().ok_or_else(|| {
                JitRuntimeError::CompileError(format!(
                    "BigInt value {n} does not fit in i64 for flat state encoding"
                ))
            })
        }
        _ => Err(JitRuntimeError::CompileError(format!(
            "expected integer value, got {value:?}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use tla_value::value::{FuncValue, RecordValue, SeqValue, SortedSet};

    // ========================================================================
    // Schema construction
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_schema_all_scalar() {
        let values = vec![
            Value::Bool(true),
            Value::SmallInt(42),
            Value::Bool(false),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);

        assert_eq!(schema.var_count(), 3);
        assert!(schema.is_all_scalar());
        assert_eq!(schema.encoding(0), Some(&VarEncoding::Bool));
        assert_eq!(schema.encoding(1), Some(&VarEncoding::Int));
        assert_eq!(schema.encoding(2), Some(&VarEncoding::Bool));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_schema_with_compound() {
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![Value::SmallInt(1)])));
        let values = vec![Value::SmallInt(10), seq];
        let schema = FlatStateSchema::from_initial_state(&values);

        assert_eq!(schema.var_count(), 2);
        assert!(!schema.is_all_scalar());
        assert_eq!(schema.encoding(0), Some(&VarEncoding::Int));
        assert_eq!(schema.encoding(1), Some(&VarEncoding::Compound));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_schema_with_string() {
        let values = vec![
            Value::String(Arc::from("hello")),
            Value::SmallInt(5),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);

        assert_eq!(schema.var_count(), 2);
        assert!(schema.is_all_scalar()); // strings are scalar
        assert_eq!(schema.encoding(0), Some(&VarEncoding::String));
        assert_eq!(schema.encoding(1), Some(&VarEncoding::Int));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_schema_from_state_layout() {
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::ScalarBool,
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(3),
            }),
        ]);
        let schema = FlatStateSchema::from_state_layout(&layout);

        assert_eq!(schema.var_count(), 3);
        assert!(!schema.is_all_scalar());
        assert_eq!(schema.encoding(0), Some(&VarEncoding::Int));
        assert_eq!(schema.encoding(1), Some(&VarEncoding::Bool));
        assert_eq!(schema.encoding(2), Some(&VarEncoding::Compound));
    }

    // ========================================================================
    // FlatState basics
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_zeroed() {
        let fs = FlatState::zeroed(3);
        assert_eq!(fs.var_count(), 3);
        assert_eq!(fs.total_slots(), 3);
        assert_eq!(fs.as_slice(), &[0, 0, 0]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_get_set_slot() {
        let mut fs = FlatState::zeroed(3);
        fs.set_slot(0, 42);
        fs.set_slot(1, -7);
        fs.set_slot(2, 1);

        assert_eq!(fs.get_slot(0), Some(42));
        assert_eq!(fs.get_slot(1), Some(-7));
        assert_eq!(fs.get_slot(2), Some(1));
        assert_eq!(fs.get_slot(3), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_from_buf() {
        let buf = vec![10, 20, 30];
        let fs = FlatState::from_buf(buf, 3).expect("from_buf");
        assert_eq!(fs.var_count(), 3);
        assert_eq!(fs.total_slots(), 3);
        assert_eq!(fs.as_slice(), &[10, 20, 30]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_from_buf_too_small() {
        let buf = vec![10];
        let result = FlatState::from_buf(buf, 3);
        assert!(result.is_err());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_deterministic() {
        let fs = FlatState::from_buf(vec![1, 2, 3], 3).expect("from_buf");
        let fp1 = fs.fingerprint();
        let fp2 = fs.fingerprint();
        assert_eq!(fp1, fp2, "fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_different_inputs_differ() {
        let fs_a = FlatState::from_buf(vec![1, 2, 3], 3).expect("from_buf a");
        let fs_b = FlatState::from_buf(vec![1, 2, 4], 3).expect("from_buf b");
        assert_ne!(
            fs_a.fingerprint(),
            fs_b.fingerprint(),
            "different states should have different fingerprints"
        );
    }

    // ========================================================================
    // All-scalar round-trip
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_all_scalar_bools() {
        let values = vec![Value::Bool(true), Value::Bool(false), Value::Bool(true)];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        assert_eq!(flat.var_count(), 3);
        assert_eq!(flat.total_slots(), 3);
        assert_eq!(flat.as_slice(), &[1, 0, 1]);

        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        assert_eq!(restored, values);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_all_scalar_ints() {
        let values = vec![
            Value::SmallInt(0),
            Value::SmallInt(42),
            Value::SmallInt(-99),
            Value::SmallInt(i64::MAX),
            Value::SmallInt(i64::MIN),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        assert_eq!(flat.total_slots(), 5);
        assert_eq!(flat.as_slice(), &[0, 42, -99, i64::MAX, i64::MIN]);

        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        assert_eq!(restored, values);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_mixed_scalar() {
        let values = vec![
            Value::Bool(true),
            Value::SmallInt(7),
            Value::Bool(false),
            Value::SmallInt(-1),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        assert_eq!(flat.as_slice(), &[1, 7, 0, -1]);

        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        assert_eq!(restored, values);
    }

    // ========================================================================
    // String round-trip
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_string_values() {
        let values = vec![
            Value::String(Arc::from("active")),
            Value::SmallInt(3),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        assert_eq!(flat.total_slots(), 2);

        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        match &restored[0] {
            Value::String(s) => assert_eq!(&**s, "active"),
            other => panic!("expected String, got {other:?}"),
        }
        assert_eq!(restored[1], Value::SmallInt(3));
    }

    // ========================================================================
    // Compound round-trip
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_with_sequence() {
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ])));
        let values = vec![Value::SmallInt(1), seq.clone()];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(!schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        assert_eq!(flat.var_count(), 2);
        // Index slots + compound region
        assert!(flat.total_slots() > 2, "compound values need extra slots");
        // First slot is the integer 1
        assert_eq!(flat.get_slot(0), Some(1));
        // Second slot is the compound offset (>= 2)
        let compound_offset = flat.get_slot(1).expect("slot 1");
        assert!(compound_offset >= 2, "compound offset should be past index slots");

        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        assert_eq!(restored[0], Value::SmallInt(1));
        match &restored[1] {
            Value::Seq(s) => {
                assert_eq!(s.len(), 3);
                assert_eq!(*s.get(0).expect("elem 0"), Value::SmallInt(10));
                assert_eq!(*s.get(1).expect("elem 1"), Value::SmallInt(20));
                assert_eq!(*s.get(2).expect("elem 2"), Value::SmallInt(30));
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_with_record() {
        let rec = Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("count"), Value::SmallInt(5)),
            (Arc::from("flag"), Value::Bool(true)),
        ]));
        let values = vec![rec.clone(), Value::Bool(false)];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(!schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");

        match &restored[0] {
            Value::Record(r) => assert_eq!(r.len(), 2),
            other => panic!("expected Record, got {other:?}"),
        }
        assert_eq!(restored[1], Value::Bool(false));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_with_set() {
        let set = Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ])));
        let values = vec![set.clone(), Value::SmallInt(42)];
        let schema = FlatStateSchema::from_initial_state(&values);

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");

        match &restored[0] {
            Value::Set(s) => assert_eq!(s.len(), 3),
            other => panic!("expected Set, got {other:?}"),
        }
        assert_eq!(restored[1], Value::SmallInt(42));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_with_function() {
        let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ])));
        let values = vec![func.clone()];
        let schema = FlatStateSchema::from_initial_state(&values);

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");

        match &restored[0] {
            Value::Func(f) => {
                assert_eq!(f.domain_len(), 2);
                assert_eq!(f.apply(&Value::SmallInt(1)), Some(&Value::Bool(true)));
                assert_eq!(f.apply(&Value::SmallInt(2)), Some(&Value::Bool(false)));
            }
            other => panic!("expected Func, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_multiple_compound() {
        // State: [seq, int, record, bool]
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![Value::SmallInt(7)])));
        let rec = Value::Record(RecordValue::from_sorted_str_entries(vec![(
            Arc::from("x"),
            Value::SmallInt(99),
        )]));
        let values = vec![seq.clone(), Value::SmallInt(42), rec.clone(), Value::Bool(true)];
        let schema = FlatStateSchema::from_initial_state(&values);
        assert!(!schema.is_all_scalar());

        let flat = state_to_flat(&values, &schema).expect("state_to_flat");
        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");

        match &restored[0] {
            Value::Seq(s) => assert_eq!(s.len(), 1),
            other => panic!("expected Seq, got {other:?}"),
        }
        assert_eq!(restored[1], Value::SmallInt(42));
        match &restored[2] {
            Value::Record(r) => assert_eq!(r.len(), 1),
            other => panic!("expected Record, got {other:?}"),
        }
        assert_eq!(restored[3], Value::Bool(true));
    }

    // ========================================================================
    // Reuse buffer path
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_reuse_scalar() {
        let values = vec![Value::Bool(true), Value::SmallInt(42)];
        let schema = FlatStateSchema::from_initial_state(&values);

        let mut buf = Vec::new();
        assert!(state_to_flat_reuse(&values, &schema, &mut buf));
        assert_eq!(buf, &[1, 42]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_reuse_compound() {
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![Value::SmallInt(5)])));
        let values = vec![seq, Value::SmallInt(10)];
        let schema = FlatStateSchema::from_initial_state(&values);

        let mut buf = Vec::new();
        assert!(state_to_flat_reuse(&values, &schema, &mut buf));
        assert!(buf.len() > 2, "compound values need extra slots");

        // The buffer should be usable for reconstruction
        let flat = FlatState::from_buf(buf.clone(), 2).expect("from_buf");
        let restored = flat_to_state(&flat, &schema).expect("flat_to_state");
        assert_eq!(restored[1], Value::SmallInt(10));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_reuse_buffer_reused() {
        let values = vec![Value::SmallInt(1), Value::SmallInt(2)];
        let schema = FlatStateSchema::from_initial_state(&values);

        let mut buf = Vec::with_capacity(64);
        let ptr_before = buf.as_ptr();

        assert!(state_to_flat_reuse(&values, &schema, &mut buf));

        // Capacity should not have changed (buffer reused)
        assert_eq!(
            buf.as_ptr(), ptr_before,
            "state_to_flat_reuse should reuse the provided allocation"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_reuse_wrong_count() {
        let values = vec![Value::SmallInt(1)];
        let schema = FlatStateSchema::from_initial_state(&vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
        ]);
        let mut buf = Vec::new();
        assert!(
            !state_to_flat_reuse(&values, &schema, &mut buf),
            "mismatched count should return false"
        );
    }

    // ========================================================================
    // Error cases
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_wrong_count() {
        let values = vec![Value::SmallInt(1)];
        let schema = FlatStateSchema::from_initial_state(&vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
        ]);
        let result = state_to_flat(&values, &schema);
        assert!(result.is_err());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_to_flat_type_mismatch_bool_for_int() {
        let values = vec![Value::SmallInt(42)]; // schema expects bool
        let schema_values = vec![Value::Bool(true)];
        let schema = FlatStateSchema::from_initial_state(&schema_values);

        // Encoding is Bool, but value is Int — should error
        let result = state_to_flat(&values, &schema);
        assert!(result.is_err());
    }

    // ========================================================================
    // Fingerprint consistency
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_matches_direct_xxh3() {
        let values = vec![
            Value::SmallInt(7),
            Value::SmallInt(11),
            Value::SmallInt(42),
        ];
        let schema = FlatStateSchema::from_initial_state(&values);
        let flat = state_to_flat(&values, &schema).expect("state_to_flat");

        let fp_via_flat_state = flat.fingerprint();
        let fp_via_direct = crate::runtime_abi::fingerprint::jit_xxh3_fingerprint_64(
            flat.as_slice().as_ptr(),
            flat.total_slots() as u32,
        );
        assert_eq!(
            fp_via_flat_state, fp_via_direct,
            "FlatState fingerprint must match direct xxh3 call"
        );
    }

    // ========================================================================
    // Into buf
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_into_buf() {
        let fs = FlatState::from_buf(vec![10, 20, 30], 3).expect("from_buf");
        let buf = fs.into_buf();
        assert_eq!(buf, vec![10, 20, 30]);
    }
}
