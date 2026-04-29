// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound value serialization + scratch-buffer state for the JIT/AOT ABI.
//!
//! This module is the canonical source for:
//!
//! - `serialize_value` / `deserialize_value` — Convert between `tla_value::Value`
//!   and the flat `[i64]` representation used by JIT-compiled code.
//! - `infer_layout` / `infer_var_layout` — Build [`CompoundLayout`] /
//!   [`VarLayout`] descriptors from runtime values.
//! - `COMPOUND_SCRATCH_BASE`, `clear_compound_scratch`, `read_compound_scratch`,
//!   `compound_scratch_guard`, `with_compound_scratch`, `with_compound_scratch_mut`
//!   — Thread-local scratch buffer shared between JIT-emitted code and the
//!   interpreter fallback path.
//!
//! These functions live here (not in `tla-jit-runtime::compound_layout`) so they
//! survive the Stage 2d deletion of `tla-jit` and `tla-jit-runtime`. Callers in
//! `tla-check` and `tla-llvm2` import directly from `tla_jit_abi`, and
//! `tla-jit-runtime::compound_layout` / `tla-jit-runtime::abi` re-export these
//! items for backward compatibility during the deletion transition.
//!
//! Part of #4267 Wave 11d (epic #4251 Stage 2d).

use crate::layout::{
    CompoundLayout, VarLayout, TAG_BOOL, TAG_FUNC, TAG_INT, TAG_RECORD, TAG_SEQ, TAG_SET,
    TAG_STRING, TAG_TUPLE,
};
use crate::JitRuntimeError;
use tla_core::NameId;
use tla_value::value::{FuncValue, IntIntervalFunc, RecordValue, SeqValue, SortedSet, Value};

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
pub fn serialize_value(value: &Value, buf: &mut Vec<i64>) -> Result<usize, JitRuntimeError> {
    let start = buf.len();
    serialize_value_inner(value, buf)?;
    Ok(buf.len() - start)
}

/// Internal recursive serialization.
fn serialize_value_inner(value: &Value, buf: &mut Vec<i64>) -> Result<(), JitRuntimeError> {
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
                JitRuntimeError::CompileError(format!(
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
            return Err(JitRuntimeError::UnsupportedExpr(format!(
                "cannot serialize value type for JIT: {value:?}"
            )));
        }
    }
    Ok(())
}

/// Serialize a FuncValue using its overlay-aware iterator.
fn serialize_func_value(func: &FuncValue, buf: &mut Vec<i64>) -> Result<(), JitRuntimeError> {
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
fn serialize_int_func_value(
    func: &IntIntervalFunc,
    buf: &mut Vec<i64>,
) -> Result<(), JitRuntimeError> {
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
pub fn deserialize_value(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos >= buf.len() {
        return Err(JitRuntimeError::CompileError(
            "buffer underflow during JIT deserialization".to_string(),
        ));
    }

    let tag = buf[pos];
    match tag {
        TAG_BOOL => {
            if pos + 1 >= buf.len() {
                return Err(JitRuntimeError::CompileError(
                    "buffer underflow reading bool value".to_string(),
                ));
            }
            Ok((Value::Bool(buf[pos + 1] != 0), 2))
        }
        TAG_INT => {
            if pos + 1 >= buf.len() {
                return Err(JitRuntimeError::CompileError(
                    "buffer underflow reading int value".to_string(),
                ));
            }
            Ok((Value::SmallInt(buf[pos + 1]), 2))
        }
        TAG_STRING => {
            if pos + 1 >= buf.len() {
                return Err(JitRuntimeError::CompileError(
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
        _ => Err(JitRuntimeError::CompileError(format!(
            "unknown type tag {tag} at offset {pos} during JIT deserialization"
        ))),
    }
}

/// Deserialize a record from the flat buffer.
fn deserialize_record(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos + 1 >= buf.len() {
        return Err(JitRuntimeError::CompileError(
            "buffer underflow reading record header".to_string(),
        ));
    }
    let field_count = buf[pos + 1] as usize;
    let mut offset = pos + 2;
    let mut entries = Vec::with_capacity(field_count);

    for _ in 0..field_count {
        if offset >= buf.len() {
            return Err(JitRuntimeError::CompileError(
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
fn deserialize_seq(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos + 1 >= buf.len() {
        return Err(JitRuntimeError::CompileError(
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
fn deserialize_set(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos + 1 >= buf.len() {
        return Err(JitRuntimeError::CompileError(
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
fn deserialize_func(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos + 1 >= buf.len() {
        return Err(JitRuntimeError::CompileError(
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
fn deserialize_tuple(buf: &[i64], pos: usize) -> Result<(Value, usize), JitRuntimeError> {
    if pos + 1 >= buf.len() {
        return Err(JitRuntimeError::CompileError(
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

// ============================================================================
// Compound scratch buffer (thread-local, shared between JIT + interpreter)
// ============================================================================

/// Sentinel base offset for compound scratch buffer references.
///
/// A JIT-constructed compound value writes itself into the thread-local
/// scratch buffer and returns `COMPOUND_SCRATCH_BASE + start_pos`, allowing
/// the interpreter fallback to detect "compound was constructed here" and
/// deserialize via [`read_compound_scratch`].
pub const COMPOUND_SCRATCH_BASE: i64 = 0x7FFF_0000_0000_0000_u64 as i64;

thread_local! {
    /// Thread-local scratch buffer for JIT-constructed compound values.
    ///
    /// Shared between the Cranelift runtime helpers (in `tla-jit-runtime::abi`,
    /// called from JIT-emitted native code) and the interpreter fallback (in
    /// `tla-check::check::model_checker::invariants::eval`). Exposed via
    /// [`with_compound_scratch`] / [`with_compound_scratch_mut`].
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

/// Access the compound scratch buffer for read-only operations.
///
/// Used by JIT runtime helpers that need to inspect the buffer without
/// allocating a copy.
pub fn with_compound_scratch<F, R>(f: F) -> R
where
    F: FnOnce(&Vec<i64>) -> R,
{
    COMPOUND_SCRATCH.with(|buf| f(&buf.borrow()))
}

/// Access the compound scratch buffer for mutation.
///
/// Used by JIT runtime helpers (`jit_record_new_scalar`, `jit_seq_tail`, etc.)
/// that construct compound values and append them to the shared scratch buffer.
pub fn with_compound_scratch_mut<F, R>(f: F) -> R
where
    F: FnOnce(&mut Vec<i64>) -> R,
{
    COMPOUND_SCRATCH.with(|buf| f(&mut buf.borrow_mut()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ========================================================================
    // Scalar round-trips
    // ========================================================================

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

    #[test]
    fn test_roundtrip_int_scalar() {
        let val = Value::SmallInt(42);
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize int");
        assert_eq!(written, 2);
        assert_eq!(buf, vec![TAG_INT, 42]);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize int");
        assert_eq!(consumed, 2);
        assert_eq!(deserialized, Value::SmallInt(42));
    }

    #[test]
    fn test_roundtrip_string_scalar() {
        let val = Value::String(Arc::from("hello"));
        let mut buf = Vec::new();
        serialize_value(&val, &mut buf).expect("serialize string");
        let (deserialized, _) = deserialize_value(&buf, 0).expect("deserialize string");
        match &deserialized {
            Value::String(s) => assert_eq!(&**s, "hello"),
            other => panic!("expected String, got {other:?}"),
        }
    }

    #[test]
    fn test_compound_scratch_base_sentinel() {
        // Sentinel must be high enough to avoid collision with legitimate
        // serialization offsets (which are small usize values).
        assert!(COMPOUND_SCRATCH_BASE > 0);
        assert!(COMPOUND_SCRATCH_BASE > i64::from(u32::MAX));
    }

    #[test]
    fn test_compound_scratch_clear() {
        with_compound_scratch_mut(|buf| buf.push(123));
        assert_eq!(read_compound_scratch(), vec![123]);
        clear_compound_scratch();
        assert_eq!(read_compound_scratch(), Vec::<i64>::new());
    }

    #[test]
    fn test_compound_scratch_guard_clears() {
        with_compound_scratch_mut(|buf| buf.push(1));
        {
            let _guard = compound_scratch_guard();
            with_compound_scratch_mut(|buf| buf.push(2));
            assert_eq!(read_compound_scratch(), vec![2]);
        }
        assert_eq!(read_compound_scratch(), Vec::<i64>::new());
    }

    #[test]
    fn test_infer_var_layout_scalar_int() {
        assert_eq!(infer_var_layout(&Value::SmallInt(0)), VarLayout::ScalarInt);
    }

    #[test]
    fn test_infer_var_layout_scalar_bool() {
        assert_eq!(infer_var_layout(&Value::Bool(true)), VarLayout::ScalarBool);
    }
}
