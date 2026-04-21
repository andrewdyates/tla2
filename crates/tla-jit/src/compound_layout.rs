// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound state variable layout descriptors for the JIT ABI.
//!
//! The JIT state array is a flat `[i64]` where each slot holds one scalar
//! state variable. This module extends the ABI to support compound state
//! variables (records, sequences, sets, functions, tuples) by defining:
//!
//! 1. **`CompoundLayout`** — a descriptor that tells the JIT how a compound
//!    value maps onto a contiguous region of the flat state array.
//!
//! 2. **`StateLayout`** — a full description of all state variables and their
//!    types (scalar or compound), determining the total i64 slot count.
//!
//! 3. **Serialization/deserialization** between `Value` (from `tla-value`) and
//!    the flat `[i64]` representation used by JIT-compiled code.
//!
//! # Design
//!
//! Compound values are serialized into the flat i64 array with a type tag
//! in the first word, followed by a length/field-count word, followed by
//! the payload. Nested compound values are recursively serialized inline.
//!
//! ```text
//! Record [a |-> 1, b |-> TRUE]:
//!   slot[0] = TAG_RECORD (1)
//!   slot[1] = 2 (field count)
//!   slot[2] = name_id("a") as i64
//!   slot[3] = TAG_INT (5)
//!   slot[4] = 1
//!   slot[5] = name_id("b") as i64
//!   slot[6] = TAG_BOOL (6)
//!   slot[7] = 1 (TRUE)
//!
//! Sequence <<3, 7>>:
//!   slot[0] = TAG_SEQ (2)
//!   slot[1] = 2 (length)
//!   slot[2] = TAG_INT (5)
//!   slot[3] = 3
//!   slot[4] = TAG_INT (5)
//!   slot[5] = 7
//! ```
//!
//! Part of #3848.

use crate::error::JitError;
use tla_core::NameId;
use tla_value::value::{FuncValue, IntIntervalFunc, RecordValue, SeqValue, SortedSet, Value};

// ============================================================================
// Value type tags for the flat i64 representation
// ============================================================================

/// Type tag for a record value in the flat i64 state array.
pub const TAG_RECORD: i64 = 1;
/// Type tag for a sequence value.
pub const TAG_SEQ: i64 = 2;
/// Type tag for a set value (finite, enumerated).
pub const TAG_SET: i64 = 3;
/// Type tag for a function value.
pub const TAG_FUNC: i64 = 4;
/// Type tag for an integer scalar.
pub const TAG_INT: i64 = 5;
/// Type tag for a boolean scalar.
pub const TAG_BOOL: i64 = 6;
/// Type tag for a string value (stored as interned NameId).
pub const TAG_STRING: i64 = 7;
/// Type tag for a tuple value.
pub const TAG_TUPLE: i64 = 8;

// ============================================================================
// Compound layout descriptors
// ============================================================================

/// Describes the layout of a single state variable in the JIT state array.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VarLayout {
    /// Scalar integer — occupies 1 i64 slot.
    ScalarInt,
    /// Scalar boolean — occupies 1 i64 slot (0 = false, 1 = true).
    ScalarBool,
    /// Compound value — occupies a variable number of i64 slots determined
    /// by the value's serialized form. The `CompoundLayout` descriptor
    /// provides the structure, but the actual slot count depends on the
    /// runtime value (e.g., sequence length, record field count).
    Compound(CompoundLayout),
}

/// Describes the expected structure of a compound state variable.
///
/// Used by the JIT to understand the memory layout of compound values
/// and to validate serialized data during deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CompoundLayout {
    /// Record with known field names (sorted by NameId).
    /// Each field has its own layout descriptor.
    Record {
        /// (field_name_id, field_layout) pairs, sorted by NameId.
        fields: Vec<(NameId, CompoundLayout)>,
    },

    /// Function (domain -> range mapping).
    /// Stored as interleaved key-value pairs.
    Function {
        /// Layout of domain keys.
        key_layout: Box<CompoundLayout>,
        /// Layout of range values.
        value_layout: Box<CompoundLayout>,
        /// Number of key-value pairs when inferred from a concrete value.
        /// `None` when the cardinality is unknown (e.g., parsed from metadata).
        /// When `Some(n)`, `fixed_serialized_slots()` can compute the total
        /// size as `2 + n * (key_size + value_size)`.
        pair_count: Option<usize>,
        /// For integer-domain functions `[lo..hi -> T]`, the inclusive lower
        /// bound of the domain interval. When `Some(lo)` and `pair_count` is
        /// `Some(n)`, the function maps `lo..lo+n-1` to contiguous values.
        /// This enables O(1) direct-index lookup: `value_at(k) = slots[base + 2 + (k - lo) * pair_slots + key_slots]`.
        ///
        /// `None` for non-integer domains or non-contiguous keys.
        ///
        /// Part of #3985: Phase 2 compound layout wiring.
        domain_lo: Option<i64>,
    },

    /// Sequence of homogeneous or heterogeneous elements.
    Sequence {
        /// Layout of each element (all elements share this layout).
        element_layout: Box<CompoundLayout>,
        /// Number of elements when inferred from a concrete value.
        element_count: Option<usize>,
    },

    /// Finite enumerated set.
    Set {
        /// Layout of each element.
        element_layout: Box<CompoundLayout>,
        /// Number of elements when inferred from a concrete value.
        element_count: Option<usize>,
    },

    /// Tuple with known arity and per-position layouts.
    Tuple {
        /// Layout of each position (1-indexed in TLA+, stored 0-indexed).
        element_layouts: Vec<CompoundLayout>,
    },

    /// Scalar integer leaf — no compound structure.
    Int,

    /// Scalar boolean leaf — no compound structure.
    Bool,

    /// String leaf — serialized as its interned NameId (u32 as i64).
    String,

    /// Dynamic (type-tagged) — the actual type is encoded inline via
    /// a tag word. Used for heterogeneous collections where the element
    /// type is not statically known.
    Dynamic,
}

impl CompoundLayout {
    /// Compute the fixed serialized size in i64 slots, if statically known.
    ///
    /// Returns `Some(n)` when the entire compound value has a fixed, predictable
    /// serialized size. Returns `None` for dynamic or variable-length layouts.
    ///
    /// Scalar leaves: TAG + value = 2 slots.
    /// Records: TAG + field_count + sum(name_id + field_serialized_size per field).
    /// Tuples: TAG + elem_count + sum(elem_serialized_size per element).
    /// Functions: TAG + pair_count + sum(key_size + value_size per pair).
    ///   When `pair_count` is `Some(n)` (inferred from a concrete value),
    ///   the total is `2 + n * (key_slots + value_slots)`.
    /// Sequences/Sets: TAG + count + n * element_slots when count is known.
    #[must_use]
    pub fn fixed_serialized_slots(&self) -> Option<usize> {
        match self {
            CompoundLayout::Int | CompoundLayout::Bool | CompoundLayout::String => Some(2),
            CompoundLayout::Record { fields } => {
                let mut total = 2; // TAG_RECORD + field_count
                for (_, field_layout) in fields {
                    total += 1; // name_id slot
                    total += field_layout.fixed_serialized_slots()?;
                }
                Some(total)
            }
            CompoundLayout::Tuple { element_layouts } => {
                let mut total = 2; // TAG_TUPLE + elem_count
                for elem_layout in element_layouts {
                    total += elem_layout.fixed_serialized_slots()?;
                }
                Some(total)
            }
            CompoundLayout::Function {
                key_layout,
                value_layout,
                pair_count,
                ..
            } => {
                let n = (*pair_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let key_slots = key_layout.fixed_serialized_slots()?;
                let value_slots = value_layout.fixed_serialized_slots()?;
                Some(2 + n * (key_slots + value_slots))
            }
            CompoundLayout::Sequence {
                element_layout,
                element_count,
            } => {
                let n = (*element_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let elem_slots = element_layout.fixed_serialized_slots()?;
                Some(2 + n * elem_slots)
            }
            CompoundLayout::Set {
                element_layout,
                element_count,
            } => {
                let n = (*element_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let elem_slots = element_layout.fixed_serialized_slots()?;
                Some(2 + n * elem_slots)
            }
            CompoundLayout::Dynamic => None,
        }
    }

    /// Check if this is a scalar leaf type (Int, Bool, or String).
    #[must_use]
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            CompoundLayout::Int | CompoundLayout::Bool | CompoundLayout::String
        )
    }

    /// Check if this function has a contiguous integer domain enabling O(1)
    /// direct-index lookup instead of O(n) linear scan.
    ///
    /// Returns `Some((lo, len))` when the function maps `[lo..lo+len-1] -> T`
    /// with scalar keys and known pair count.
    ///
    /// Part of #3985: Phase 2 compound layout wiring.
    #[must_use]
    pub fn int_array_bounds(&self) -> Option<(i64, usize)> {
        match self {
            CompoundLayout::Function {
                key_layout,
                pair_count: Some(n),
                domain_lo: Some(lo),
                ..
            } if key_layout.is_scalar() && *n > 0 => Some((*lo, *n)),
            _ => None,
        }
    }
}

/// Describes the layout of the full state vector (all state variables).
///
/// Maps each state variable index to its layout descriptor and its
/// starting offset in the flat i64 array.
#[derive(Debug, Clone)]
pub struct StateLayout {
    /// Per-variable layout descriptors, in VarIdx order.
    vars: Vec<VarLayout>,
}

impl StateLayout {
    /// Create a new state layout from variable descriptors.
    pub fn new(vars: Vec<VarLayout>) -> Self {
        StateLayout { vars }
    }

    /// Get the number of state variables.
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Get the layout for a specific variable.
    pub fn var_layout(&self, idx: usize) -> Option<&VarLayout> {
        self.vars.get(idx)
    }

    /// Check if all variables are scalar (legacy flat i64 layout).
    pub fn is_all_scalar(&self) -> bool {
        self.vars
            .iter()
            .all(|v| matches!(v, VarLayout::ScalarInt | VarLayout::ScalarBool))
    }

    /// Iterate over all variable layouts.
    pub fn iter(&self) -> impl Iterator<Item = &VarLayout> {
        self.vars.iter()
    }

    /// Compute the starting slot offset for each variable in the flat i64 array.
    ///
    /// Returns a vector where `offsets[i]` is `Some(offset)` for variables
    /// whose starting position can be determined at compile time, or `None`
    /// for variables that come after a dynamic-size compound variable.
    ///
    /// Scalar variables occupy 1 slot. Compound variables with fixed
    /// serialized size occupy their `fixed_serialized_slots()` count.
    /// Once a variable with dynamic size is encountered, all subsequent
    /// variables get `None` (their offsets cannot be computed statically).
    #[must_use]
    pub fn compute_var_offsets(&self) -> Vec<Option<usize>> {
        let mut offsets = Vec::with_capacity(self.vars.len());
        let mut current: Option<usize> = Some(0);
        for var in &self.vars {
            offsets.push(current);
            if let Some(cur) = current {
                match var {
                    VarLayout::ScalarInt | VarLayout::ScalarBool => {
                        current = Some(cur + 1);
                    }
                    VarLayout::Compound(layout) => {
                        current = layout.fixed_serialized_slots().map(|s| cur + s);
                    }
                }
            }
        }
        offsets
    }
}

// ============================================================================
// Serialization: Value -> flat i64 buffer
// ============================================================================

/// Serialize a `Value` into a flat i64 buffer, appending to `buf`.
///
/// Returns the number of i64 slots written.
///
/// The serialization format is self-describing: each value starts with a
/// type tag word, followed by type-specific payload. This allows
/// deserialization without external layout metadata (though layout
/// descriptors can validate the structure).
pub fn serialize_value(value: &Value, buf: &mut Vec<i64>) -> Result<usize, JitError> {
    let start = buf.len();
    serialize_value_inner(value, buf)?;
    Ok(buf.len() - start)
}

/// Internal recursive serialization.
fn serialize_value_inner(value: &Value, buf: &mut Vec<i64>) -> Result<(), JitError> {
    match value {
        Value::Bool(b) => {
            buf.push(TAG_BOOL);
            buf.push(i64::from(*b));
        }
        Value::SmallInt(n) => {
            buf.push(TAG_INT);
            buf.push(*n);
        }
        Value::Int(n) => {
            use num_traits::ToPrimitive;
            let val = n.to_i64().ok_or_else(|| {
                JitError::CompileError(format!(
                    "BigInt value {n} does not fit in i64 for JIT serialization"
                ))
            })?;
            buf.push(TAG_INT);
            buf.push(val);
        }
        Value::String(s) => {
            let name_id = tla_core::intern_name(s);
            buf.push(TAG_STRING);
            buf.push(name_id.0 as i64);
        }
        // ModelValue is serialized identically to String: intern the name
        // and store as TAG_STRING + NameId. Both are represented as interned
        // NameId values at runtime in the JIT. Part of #3958.
        Value::ModelValue(s) => {
            let name_id = tla_core::intern_name(s);
            buf.push(TAG_STRING);
            buf.push(name_id.0 as i64);
        }
        Value::Record(rec) => {
            buf.push(TAG_RECORD);
            buf.push(rec.len() as i64);
            // iter() yields (NameId, &Value) pairs sorted by NameId
            for (name_id, field_val) in rec.iter() {
                buf.push(name_id.0 as i64);
                serialize_value_inner(field_val, buf)?;
            }
        }
        Value::Seq(seq) => {
            buf.push(TAG_SEQ);
            buf.push(seq.len() as i64);
            for elem in seq.iter() {
                serialize_value_inner(elem, buf)?;
            }
        }
        Value::Set(sorted_set) => {
            buf.push(TAG_SET);
            buf.push(sorted_set.len() as i64);
            for elem in sorted_set.iter() {
                serialize_value_inner(elem, buf)?;
            }
        }
        Value::Func(func) => {
            serialize_func_value(func, buf)?;
        }
        Value::IntFunc(func) => {
            serialize_int_func_value(func, buf)?;
        }
        Value::Tuple(elems) => {
            buf.push(TAG_TUPLE);
            buf.push(elems.len() as i64);
            for elem in elems.iter() {
                serialize_value_inner(elem, buf)?;
            }
        }
        _ => {
            return Err(JitError::UnsupportedExpr(format!(
                "cannot serialize value type for JIT: {value:?}"
            )));
        }
    }
    Ok(())
}

/// Serialize a FuncValue using its overlay-aware iterator.
fn serialize_func_value(func: &FuncValue, buf: &mut Vec<i64>) -> Result<(), JitError> {
    buf.push(TAG_FUNC);
    buf.push(func.domain_len() as i64);
    // iter() yields (key, value) pairs in domain-sorted order, overlay-aware
    for (key, val) in func.iter() {
        serialize_value_inner(key, buf)?;
        serialize_value_inner(val, buf)?;
    }
    Ok(())
}

/// Serialize an IntIntervalFunc as TAG_FUNC with integer keys [min..max].
///
/// The wire format is identical to FuncValue so deserialization always
/// produces a generic `Value::Func`. This is fine because the JIT only
/// needs the flattened i64 representation — the optimized IntFunc is an
/// interpreter-side memory optimization, not a semantic distinction.
fn serialize_int_func_value(func: &IntIntervalFunc, buf: &mut Vec<i64>) -> Result<(), JitError> {
    buf.push(TAG_FUNC);
    buf.push(func.len() as i64);
    for i in 0..func.len() {
        let key = func.min() + i as i64;
        buf.push(TAG_INT);
        buf.push(key);
        serialize_value_inner(&func.values()[i], buf)?;
    }
    Ok(())
}

// ============================================================================
// Deserialization: flat i64 buffer -> Value
// ============================================================================

/// Deserialize a `Value` from a flat i64 buffer starting at `pos`.
///
/// Returns the deserialized value and the number of i64 slots consumed.
pub fn deserialize_value(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow during JIT deserialization".to_string(),
        ));
    }

    let tag = buf[pos];
    match tag {
        TAG_BOOL => {
            if pos + 1 >= buf.len() {
                return Err(JitError::CompileError(
                    "buffer underflow reading bool value".to_string(),
                ));
            }
            Ok((Value::Bool(buf[pos + 1] != 0), 2))
        }
        TAG_INT => {
            if pos + 1 >= buf.len() {
                return Err(JitError::CompileError(
                    "buffer underflow reading int value".to_string(),
                ));
            }
            Ok((Value::SmallInt(buf[pos + 1]), 2))
        }
        TAG_STRING => {
            if pos + 1 >= buf.len() {
                return Err(JitError::CompileError(
                    "buffer underflow reading string value".to_string(),
                ));
            }
            let name_id = NameId(buf[pos + 1] as u32);
            let s = tla_core::resolve_name_id(name_id);
            Ok((Value::String(s), 2))
        }
        TAG_RECORD => deserialize_record(buf, pos),
        TAG_SEQ => deserialize_seq(buf, pos),
        TAG_SET => deserialize_set(buf, pos),
        TAG_FUNC => deserialize_func(buf, pos),
        TAG_TUPLE => deserialize_tuple(buf, pos),
        _ => Err(JitError::CompileError(format!(
            "unknown type tag {tag} at offset {pos} during JIT deserialization"
        ))),
    }
}

/// Deserialize a record from the flat buffer.
fn deserialize_record(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos + 1 >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow reading record header".to_string(),
        ));
    }
    let field_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut entries = Vec::with_capacity(field_count);

    for _ in 0..field_count {
        if offset >= buf.len() {
            return Err(JitError::CompileError(
                "buffer underflow reading record field name".to_string(),
            ));
        }
        let name_id = NameId(buf[offset] as u32);
        offset += 1;
        let (val, consumed) = deserialize_value(buf, offset)?;
        offset += consumed;
        entries.push((name_id, val));
    }

    // RecordValue expects entries sorted by NameId — they are already sorted
    // because serialize preserves the RecordValue's sorted order.
    Ok((
        Value::Record(RecordValue::from_sorted_entries(entries)),
        offset - pos,
    ))
}

/// Deserialize a sequence from the flat buffer.
fn deserialize_seq(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos + 1 >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow reading seq header".to_string(),
        ));
    }
    let elem_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut elements = Vec::with_capacity(elem_count);

    for _ in 0..elem_count {
        let (val, consumed) = deserialize_value(buf, offset)?;
        offset += consumed;
        elements.push(val);
    }

    Ok((
        Value::Seq(std::sync::Arc::new(SeqValue::from_vec(elements))),
        offset - pos,
    ))
}

/// Deserialize a set from the flat buffer.
fn deserialize_set(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos + 1 >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow reading set header".to_string(),
        ));
    }
    let elem_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut elements = Vec::with_capacity(elem_count);

    for _ in 0..elem_count {
        let (val, consumed) = deserialize_value(buf, offset)?;
        offset += consumed;
        elements.push(val);
    }

    // Elements are already sorted because serialize iterates in canonical order.
    Ok((
        Value::Set(std::sync::Arc::new(SortedSet::from_sorted_vec(elements))),
        offset - pos,
    ))
}

/// Deserialize a function from the flat buffer.
fn deserialize_func(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos + 1 >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow reading func header".to_string(),
        ));
    }
    let pair_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut entries = Vec::with_capacity(pair_count);

    for _ in 0..pair_count {
        let (key, key_consumed) = deserialize_value(buf, offset)?;
        offset += key_consumed;
        let (val, val_consumed) = deserialize_value(buf, offset)?;
        offset += val_consumed;
        entries.push((key, val));
    }

    Ok((
        Value::Func(std::sync::Arc::new(FuncValue::from_sorted_entries(entries))),
        offset - pos,
    ))
}

/// Deserialize a tuple from the flat buffer.
fn deserialize_tuple(buf: &[i64], pos: usize) -> Result<(Value, usize), JitError> {
    if pos + 1 >= buf.len() {
        return Err(JitError::CompileError(
            "buffer underflow reading tuple header".to_string(),
        ));
    }
    let elem_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut elements = Vec::with_capacity(elem_count);

    for _ in 0..elem_count {
        let (val, consumed) = deserialize_value(buf, offset)?;
        offset += consumed;
        elements.push(val);
    }

    Ok((Value::Tuple(elements.into()), offset - pos))
}

// ============================================================================
// Layout inference
// ============================================================================

/// Infer a `CompoundLayout` from a runtime `Value`.
///
/// This is useful when the type of a state variable is not statically known
/// and must be determined from the initial state.
pub fn infer_layout(value: &Value) -> CompoundLayout {
    match value {
        Value::Bool(_) => CompoundLayout::Bool,
        Value::SmallInt(_) | Value::Int(_) => CompoundLayout::Int,
        Value::String(_) => CompoundLayout::String,
        Value::Record(rec) => {
            let fields = rec
                .iter()
                .map(|(nid, val)| (nid, infer_layout(val)))
                .collect();
            CompoundLayout::Record { fields }
        }
        Value::Seq(seq) => {
            let element_layout = seq
                .get(0)
                .map(|first| infer_layout(first))
                .unwrap_or(CompoundLayout::Dynamic);
            CompoundLayout::Sequence {
                element_layout: Box::new(element_layout),
                element_count: Some(seq.len()),
            }
        }
        Value::Set(sorted_set) => {
            let element_layout = sorted_set
                .iter()
                .next()
                .map(|e| infer_layout(e))
                .unwrap_or(CompoundLayout::Dynamic);
            CompoundLayout::Set {
                element_layout: Box::new(element_layout),
                element_count: Some(sorted_set.len()),
            }
        }
        Value::Func(func) => {
            let key_layout = func
                .domain_iter()
                .next()
                .map(|k| infer_layout(k))
                .unwrap_or(CompoundLayout::Dynamic);
            let value_layout = if func.domain_is_empty() {
                CompoundLayout::Dynamic
            } else {
                infer_layout(func.get_value_at(0))
            };

            // Detect contiguous integer domain for direct-index optimization.
            // Part of #3985: Phase 2 compound layout wiring.
            let domain_lo = if matches!(key_layout, CompoundLayout::Int) && !func.domain_is_empty()
            {
                let mut min_key = i64::MAX;
                let mut max_key = i64::MIN;
                let mut all_int = true;
                for key in func.domain_iter() {
                    match key {
                        Value::SmallInt(n) => {
                            min_key = min_key.min(*n);
                            max_key = max_key.max(*n);
                        }
                        _ => {
                            all_int = false;
                            break;
                        }
                    }
                }
                if all_int {
                    let expected_len = (max_key - min_key + 1) as usize;
                    if expected_len == func.domain_len() {
                        Some(min_key)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            CompoundLayout::Function {
                key_layout: Box::new(key_layout),
                value_layout: Box::new(value_layout),
                pair_count: Some(func.domain_len()),
                domain_lo,
            }
        }
        Value::IntFunc(func) => {
            let value_layout = func
                .values()
                .first()
                .map(|v| infer_layout(v))
                .unwrap_or(CompoundLayout::Dynamic);
            CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(value_layout),
                pair_count: Some(func.len()),
                domain_lo: Some(IntIntervalFunc::min(func)),
            }
        }
        Value::Tuple(elems) => {
            let element_layouts = elems.iter().map(|e| infer_layout(e)).collect();
            CompoundLayout::Tuple { element_layouts }
        }
        _ => CompoundLayout::Dynamic,
    }
}

// ============================================================================
// VarLayout inference from Value
// ============================================================================

/// Infer a `VarLayout` from a runtime `Value`.
///
/// Returns `ScalarInt`/`ScalarBool` for scalar values, or `Compound(..)` for
/// compound values.
pub fn infer_var_layout(value: &Value) -> VarLayout {
    match value {
        Value::SmallInt(_) | Value::Int(_) => VarLayout::ScalarInt,
        Value::Bool(_) => VarLayout::ScalarBool,
        _ => VarLayout::Compound(infer_layout(value)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ========================================================================
    // Scalar round-trips
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_bool_true() {
        let val = Value::Bool(true);
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize bool");
        assert_eq!(written, 2);
        assert_eq!(buf, vec![TAG_BOOL, 1]);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize bool");
        assert_eq!(consumed, 2);
        assert_eq!(deserialized, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_bool_false() {
        let val = Value::Bool(false);
        let mut buf = Vec::new();
        serialize_value(&val, &mut buf).expect("serialize bool");

        let (deserialized, _) = deserialize_value(&buf, 0).expect("deserialize bool");
        assert_eq!(deserialized, Value::Bool(false));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_int() {
        let val = Value::SmallInt(42);
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize int");
        assert_eq!(written, 2);
        assert_eq!(buf, vec![TAG_INT, 42]);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize int");
        assert_eq!(consumed, 2);
        assert_eq!(deserialized, Value::SmallInt(42));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_negative_int() {
        let val = Value::SmallInt(-99);
        let mut buf = Vec::new();
        serialize_value(&val, &mut buf).expect("serialize int");

        let (deserialized, _) = deserialize_value(&buf, 0).expect("deserialize int");
        assert_eq!(deserialized, Value::SmallInt(-99));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_string() {
        let val = Value::String(Arc::from("hello"));
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize string");
        assert_eq!(written, 2);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize string");
        assert_eq!(consumed, 2);
        match &deserialized {
            Value::String(s) => assert_eq!(&**s, "hello"),
            other => panic!("expected String, got {other:?}"),
        }
    }

    // ========================================================================
    // Compound round-trips
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_record() {
        // Build a record [a |-> 1, b |-> TRUE]
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::SmallInt(1)),
            (Arc::from("b"), Value::Bool(true)),
        ]);
        let val = Value::Record(rec);

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize record");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_RECORD);
        assert_eq!(buf[1], 2); // field count

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize record");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Record(rec) => {
                assert_eq!(rec.len(), 2);
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_sequence() {
        let seq = SeqValue::from_vec(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ]);
        let val = Value::Seq(Arc::new(seq));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize seq");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_SEQ);
        assert_eq!(buf[1], 3); // element count

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize seq");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Seq(seq) => {
                assert_eq!(seq.len(), 3);
                assert_eq!(*seq.get(0).expect("elem 0"), Value::SmallInt(10));
                assert_eq!(*seq.get(1).expect("elem 1"), Value::SmallInt(20));
                assert_eq!(*seq.get(2).expect("elem 2"), Value::SmallInt(30));
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_set() {
        // Build {1, 2, 3}
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let val = Value::Set(Arc::new(set));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize set");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_SET);
        assert_eq!(buf[1], 3); // cardinality

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize set");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Set(s) => {
                assert_eq!(s.len(), 3);
            }
            other => panic!("expected Set, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_function() {
        // Build [1 |-> TRUE, 2 |-> FALSE]
        let func = FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ]);
        let val = Value::Func(Arc::new(func));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize func");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_FUNC);
        assert_eq!(buf[1], 2); // pair count

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize func");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Func(f) => {
                assert_eq!(f.domain_len(), 2);
            }
            other => panic!("expected Func, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_tuple() {
        let val =
            Value::Tuple(vec![Value::SmallInt(1), Value::Bool(true), Value::SmallInt(99)].into());

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize tuple");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_TUPLE);
        assert_eq!(buf[1], 3); // element count

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize tuple");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Tuple(elems) => {
                assert_eq!(elems.len(), 3);
                assert_eq!(elems[0], Value::SmallInt(1));
                assert_eq!(elems[1], Value::Bool(true));
                assert_eq!(elems[2], Value::SmallInt(99));
            }
            other => panic!("expected Tuple, got {other:?}"),
        }
    }

    // ========================================================================
    // IntFunc round-trips
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_int_func() {
        use tla_value::value::IntIntervalFunc;
        // [0 |-> FALSE, 1 |-> TRUE, 2 |-> FALSE] — like EWD998's `active`
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(false), Value::Bool(true), Value::Bool(false)],
        );
        let val = Value::IntFunc(Arc::new(func));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize int_func");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_FUNC);
        assert_eq!(buf[1], 3); // 3 pairs

        // Deserializes as Value::Func (generic), which is semantically equivalent
        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize int_func");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Func(f) => {
                assert_eq!(f.domain_len(), 3);
                // Check key-value pairs
                assert_eq!(f.apply(&Value::SmallInt(0)), Some(&Value::Bool(false)));
                assert_eq!(f.apply(&Value::SmallInt(1)), Some(&Value::Bool(true)));
                assert_eq!(f.apply(&Value::SmallInt(2)), Some(&Value::Bool(false)));
            }
            other => panic!("expected Func, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_int_func() {
        use tla_value::value::IntIntervalFunc;
        let func = IntIntervalFunc::new(
            1,
            3,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(true)],
        );
        let layout = infer_layout(&Value::IntFunc(Arc::new(func)));
        match layout {
            CompoundLayout::Function {
                key_layout,
                value_layout,
                ..
            } => {
                assert_eq!(*key_layout, CompoundLayout::Int);
                assert_eq!(*value_layout, CompoundLayout::Bool);
            }
            other => panic!("expected Function layout, got {other:?}"),
        }
    }

    // ========================================================================
    // Nested compound round-trips
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_nested_record_with_seq() {
        // [msgs |-> <<1, 2>>, count |-> 5]
        let seq = SeqValue::from_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("count"), Value::SmallInt(5)),
            (Arc::from("msgs"), Value::Seq(Arc::new(seq))),
        ]);
        let val = Value::Record(rec);

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize nested");
        assert!(written > 0);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize nested");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Record(rec) => {
                assert_eq!(rec.len(), 2);
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_set_of_records() {
        // { [x |-> 1], [x |-> 2] }
        let rec1 = Value::Record(RecordValue::from_sorted_str_entries(vec![(
            Arc::from("x"),
            Value::SmallInt(1),
        )]));
        let rec2 = Value::Record(RecordValue::from_sorted_str_entries(vec![(
            Arc::from("x"),
            Value::SmallInt(2),
        )]));
        let set = SortedSet::from_sorted_vec(vec![rec1, rec2]);
        let val = Value::Set(Arc::new(set));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize set of records");
        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Set(s) => assert_eq!(s.len(), 2),
            other => panic!("expected Set, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_func_with_record_values() {
        // [1 |-> [a |-> TRUE], 2 |-> [a |-> FALSE]]
        let rec1 = Value::Record(RecordValue::from_sorted_str_entries(vec![(
            Arc::from("a"),
            Value::Bool(true),
        )]));
        let rec2 = Value::Record(RecordValue::from_sorted_str_entries(vec![(
            Arc::from("a"),
            Value::Bool(false),
        )]));
        let func = FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), rec1),
            (Value::SmallInt(2), rec2),
        ]);
        let val = Value::Func(Arc::new(func));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize");
        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize");
        assert_eq!(consumed, written);

        match &deserialized {
            Value::Func(f) => assert_eq!(f.domain_len(), 2),
            other => panic!("expected Func, got {other:?}"),
        }
    }

    // ========================================================================
    // Empty compound round-trips
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_empty_seq() {
        let seq = SeqValue::from_vec(vec![]);
        let val = Value::Seq(Arc::new(seq));

        let mut buf = Vec::new();
        serialize_value(&val, &mut buf).expect("serialize empty seq");
        let (deserialized, _) = deserialize_value(&buf, 0).expect("deserialize empty seq");

        match &deserialized {
            Value::Seq(s) => assert_eq!(s.len(), 0),
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_empty_set() {
        let set = SortedSet::from_sorted_vec(vec![]);
        let val = Value::Set(Arc::new(set));

        let mut buf = Vec::new();
        serialize_value(&val, &mut buf).expect("serialize empty set");
        let (deserialized, _) = deserialize_value(&buf, 0).expect("deserialize empty set");

        match &deserialized {
            Value::Set(s) => assert_eq!(s.len(), 0),
            other => panic!("expected Set, got {other:?}"),
        }
    }

    // ========================================================================
    // Layout inference
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_scalar() {
        assert_eq!(infer_layout(&Value::SmallInt(5)), CompoundLayout::Int);
        assert_eq!(infer_layout(&Value::Bool(true)), CompoundLayout::Bool);
        assert_eq!(
            infer_layout(&Value::String(Arc::from("x"))),
            CompoundLayout::String
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_record() {
        let rec = RecordValue::from_sorted_str_entries(vec![(Arc::from("x"), Value::SmallInt(1))]);
        let layout = infer_layout(&Value::Record(rec));
        match layout {
            CompoundLayout::Record { fields } => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].1, CompoundLayout::Int);
            }
            other => panic!("expected Record layout, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_var_layout() {
        assert_eq!(infer_var_layout(&Value::SmallInt(1)), VarLayout::ScalarInt);
        assert_eq!(infer_var_layout(&Value::Bool(true)), VarLayout::ScalarBool);
        match infer_var_layout(&Value::Tuple(vec![Value::SmallInt(1)].into())) {
            VarLayout::Compound(CompoundLayout::Tuple { element_layouts }) => {
                assert_eq!(element_layouts.len(), 1);
            }
            other => panic!("expected Compound(Tuple), got {other:?}"),
        }
    }

    // ========================================================================
    // StateLayout
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_all_scalar() {
        let layout = StateLayout::new(vec![VarLayout::ScalarInt, VarLayout::ScalarBool]);
        assert_eq!(layout.var_count(), 2);
        assert!(layout.is_all_scalar());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_mixed() {
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: None,
            }),
        ]);
        assert_eq!(layout.var_count(), 2);
        assert!(!layout.is_all_scalar());
    }

    // ========================================================================
    // Multi-value serialization at offset
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_deserialize_at_offset() {
        // Serialize two values back-to-back, then deserialize from offset
        let v1 = Value::SmallInt(42);
        let v2 = Value::Bool(true);
        let mut buf = Vec::new();
        let written1 = serialize_value(&v1, &mut buf).expect("serialize v1");
        let written2 = serialize_value(&v2, &mut buf).expect("serialize v2");

        let (d1, c1) = deserialize_value(&buf, 0).expect("deserialize v1");
        assert_eq!(d1, Value::SmallInt(42));
        assert_eq!(c1, written1);

        let (d2, c2) = deserialize_value(&buf, written1).expect("deserialize v2");
        assert_eq!(d2, Value::Bool(true));
        assert_eq!(c2, written2);
    }

    // ========================================================================
    // Error cases
    // ========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_deserialize_empty_buffer_returns_error() {
        let result = deserialize_value(&[], 0);
        assert!(result.is_err());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_deserialize_unknown_tag_returns_error() {
        let buf = vec![999i64, 0];
        let result = deserialize_value(&buf, 0);
        assert!(result.is_err());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_deserialize_truncated_int_returns_error() {
        let buf = vec![TAG_INT]; // missing value word
        let result = deserialize_value(&buf, 0);
        assert!(result.is_err());
    }
}
