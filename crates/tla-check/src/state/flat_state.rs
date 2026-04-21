// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Flat i64 state representation for JIT-compiled model checking.
//!
//! `FlatState` stores the entire TLA+ state as a contiguous `[i64]` buffer,
//! interpreted via a shared `StateLayout`. This is the representation that
//! JIT-compiled transition functions and invariant checkers operate on
//! directly — no tagged pointers, no heap indirection for scalar variables.
//!
//! # Conversion
//!
//! `FlatState::from_array_state` and `FlatState::to_array_state` provide
//! exact roundtrip conversion. The `Dynamic` layout kind stores a zero
//! placeholder in the flat buffer; the actual value must be retrieved from
//! the originating `ArrayState` for those variables.
//!
//! Part of #3986.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use tla_value::CompactValue;

use super::array_state::ArrayState;
use super::flat_fingerprint::{fingerprint_flat_xxh3, FlatFingerprinter};
use super::state_layout::{SlotType, StateLayout, VarLayoutKind};
use crate::var_index::VarRegistry;
use crate::Value;

/// A TLA+ state as a flat `[i64]` buffer with layout metadata.
///
/// The buffer length equals `layout.total_slots()`. Each variable occupies
/// a contiguous region of slots determined by its `VarLayout`.
#[derive(Debug, Clone)]
pub(crate) struct FlatState {
    /// The i64 slots. Length == layout.total_slots().
    buffer: Box<[i64]>,
    /// Shared layout descriptor.
    layout: Arc<StateLayout>,
}

impl FlatState {
    /// Create a zeroed FlatState with the given layout.
    #[must_use]
    pub(crate) fn new(layout: Arc<StateLayout>) -> Self {
        let buffer = vec![0i64; layout.total_slots()].into_boxed_slice();
        FlatState { buffer, layout }
    }

    /// Create a FlatState from an existing buffer and layout.
    ///
    /// The buffer length must equal `layout.total_slots()`.
    ///
    /// Part of #3986.
    #[must_use]
    pub(crate) fn from_buffer(buffer: Box<[i64]>, layout: Arc<StateLayout>) -> Self {
        debug_assert_eq!(
            buffer.len(),
            layout.total_slots(),
            "FlatState::from_buffer: buffer len {} != total_slots {}",
            buffer.len(),
            layout.total_slots()
        );
        FlatState { buffer, layout }
    }

    /// Get the raw i64 buffer.
    #[must_use]
    pub(crate) fn buffer(&self) -> &[i64] {
        &self.buffer
    }

    /// Get the raw i64 buffer mutably.
    ///
    /// Part of #3986: needed for direct writes by arena allocation (#3990)
    /// and compiled BFS step (#3988).
    pub(crate) fn buffer_mut(&mut self) -> &mut [i64] {
        &mut self.buffer
    }

    /// Number of i64 slots in this state.
    #[must_use]
    #[inline]
    pub(crate) fn num_slots(&self) -> usize {
        self.buffer.len()
    }

    /// Total bytes consumed by this state's flat buffer.
    ///
    /// Part of #3986: acceptance criterion "bytes per state < 200".
    #[must_use]
    #[inline]
    pub(crate) fn total_bytes(&self) -> usize {
        self.buffer.len() * std::mem::size_of::<i64>()
    }

    /// Get the layout.
    #[must_use]
    pub(crate) fn layout(&self) -> &StateLayout {
        &self.layout
    }

    /// Get the shared layout Arc.
    ///
    /// Part of #3986: needed by FlatSuccessor to clone the layout for
    /// materialized states.
    #[must_use]
    pub(crate) fn layout_arc(&self) -> &Arc<StateLayout> {
        &self.layout
    }

    /// Create a new FlatState by applying slot changes to this one.
    ///
    /// Each change is `(slot_index, new_value)`. The parent is not modified.
    /// This is the non-diff-aware version — for diff-based successor
    /// generation with incremental fingerprinting, use `FlatSuccessor`.
    ///
    /// Part of #3986: successor writes directly to output i64[] buffer.
    #[must_use]
    pub(crate) fn with_slot_changes(&self, changes: &[(usize, i64)]) -> Self {
        let mut buffer = self.buffer.clone();
        for &(slot_index, new_value) in changes {
            debug_assert!(
                slot_index < buffer.len(),
                "FlatState::with_slot_changes: slot index {} out of bounds (buffer len {})",
                slot_index,
                buffer.len()
            );
            buffer[slot_index] = new_value;
        }
        FlatState {
            buffer,
            layout: Arc::clone(&self.layout),
        }
    }

    /// Copy this state's buffer into the target slice.
    ///
    /// Part of #3986: zero-copy state export for arena allocation (#3990).
    #[inline]
    pub(crate) fn copy_buffer_to(&self, target: &mut [i64]) {
        debug_assert_eq!(
            target.len(),
            self.buffer.len(),
            "FlatState::copy_buffer_to: target len {} != buffer len {}",
            target.len(),
            self.buffer.len()
        );
        target.copy_from_slice(&self.buffer);
    }

    /// Get the i64 slots for a variable by index.
    ///
    /// Returns `None` if the variable index is out of range.
    #[must_use]
    pub(crate) fn get_var_slots(&self, var_idx: usize) -> Option<&[i64]> {
        let vl = self.layout.var_layout(var_idx)?;
        Some(&self.buffer[vl.offset..vl.offset + vl.slot_count])
    }

    /// Get mutable i64 slots for a variable by index.
    ///
    /// Returns `None` if the variable index is out of range.
    pub(crate) fn get_var_slots_mut(&mut self, var_idx: usize) -> Option<&mut [i64]> {
        let vl = self.layout.var_layout(var_idx)?;
        Some(&mut self.buffer[vl.offset..vl.offset + vl.slot_count])
    }

    /// Convert an `ArrayState` into a `FlatState`.
    ///
    /// Each variable is serialized into its slot region according to the layout:
    ///
    /// - **Scalar**: Bool → 0/1, Int → raw i64.
    /// - **IntArray**: Each element written as a scalar i64 into contiguous slots.
    /// - **Record**: Each field (in sorted NameId order) written as a scalar i64.
    /// - **Bitmask**: A single i64 with set bits for present elements. Only
    ///   meaningful when the caller knows the canonical element ordering.
    ///   For now, stores 0 (placeholder) — full bitmask encoding requires
    ///   universe enumeration context from the spec.
    /// - **Dynamic**: Writes 0. The actual compound value is not representable
    ///   in the flat buffer and must be fetched from the ArrayState.
    pub(crate) fn from_array_state(array_state: &ArrayState, layout: Arc<StateLayout>) -> Self {
        let compact_values = array_state.values();
        let total = layout.total_slots();
        let mut buffer = vec![0i64; total];

        write_array_state_into_buffer(compact_values, &layout, &mut buffer);

        FlatState {
            buffer: buffer.into_boxed_slice(),
            layout,
        }
    }

    /// Write an `ArrayState`'s values into a pre-allocated `[i64]` buffer.
    ///
    /// This is the zero-allocation counterpart of `from_array_state`: the caller
    /// provides the buffer (e.g., from a `FlatStatePool`) and this function fills
    /// it. The buffer must have length `>= layout.total_slots()`.
    ///
    /// Returns the number of i64 slots written (always `layout.total_slots()`).
    ///
    /// Part of #4172: Arena-backed flat state pool.
    pub(crate) fn write_array_state_into(
        array_state: &ArrayState,
        layout: &StateLayout,
        buffer: &mut [i64],
    ) -> usize {
        let compact_values = array_state.values();
        let total = layout.total_slots();
        debug_assert!(
            buffer.len() >= total,
            "buffer too small: {} < {}",
            buffer.len(),
            total
        );
        // Zero the buffer first to match from_array_state behavior.
        buffer[..total].fill(0);
        write_array_state_into_buffer(compact_values, layout, &mut buffer[..total]);
        total
    }

    /// Compute a 128-bit xxh3 fingerprint of this state's flat buffer.
    ///
    /// Uses SIMD-accelerated xxHash3-128 for single-call hashing of the raw
    /// byte representation. For a typical 15-slot (120-byte) state this
    /// completes in ~2-5ns.
    ///
    /// Part of #3986: enables dedup via flat buffer fingerprinting.
    #[must_use]
    #[inline]
    pub(crate) fn fingerprint_xxh3(&self) -> u128 {
        fingerprint_flat_xxh3(&self.buffer)
    }

    /// Compute a 64-bit xxh3 fingerprint compatible with `Fingerprint(u64)`.
    ///
    /// This is the BFS dedup-compatible version: returns `crate::Fingerprint`
    /// directly from xxh3-64 SIMD on the raw byte buffer. Use this when the
    /// BFS seen set expects `Fingerprint(u64)` — avoids the per-variable FP64
    /// tree walk entirely.
    ///
    /// Part of #3987: compiled xxh3 fingerprinting for the BFS hot path.
    /// Part of #4215: Uses domain-separation seed to prevent collisions with
    /// FP64/FNV array-path fingerprints in the same dedup table.
    #[must_use]
    #[inline]
    pub(crate) fn fingerprint_compiled(&self) -> crate::Fingerprint {
        crate::Fingerprint(super::flat_fingerprint::fingerprint_flat_xxh3_u64_with_seed(
            &self.buffer,
            super::flat_fingerprint::FLAT_COMPILED_DOMAIN_SEED,
        ))
    }

    /// Compute a 128-bit XOR-accumulator fingerprint using a `FlatFingerprinter`.
    ///
    /// This fingerprint is composable with `FlatFingerprinter::diff` for
    /// incremental successor fingerprinting.
    ///
    /// Part of #3986: enables composable fingerprinting for FlatSuccessor diffs.
    #[must_use]
    #[inline]
    pub(crate) fn fingerprint_with(&self, fingerprinter: &FlatFingerprinter) -> u128 {
        fingerprinter.fingerprint(&self.buffer)
    }

    /// Convert this `FlatState` back to an `ArrayState`.
    ///
    /// The roundtrip is exact for `Scalar` and `IntArray` kinds. For `Dynamic`
    /// variables, the slot holds 0 — callers must supply the original values
    /// for those variables via `patch_dynamic_vars`.
    ///
    /// For `Record` and `Bitmask`, reconstruction produces equivalent `Value`s
    /// only when the layout was inferred from matching initial-state shapes.
    pub(crate) fn to_array_state(&self, _registry: &VarRegistry) -> ArrayState {
        let num_vars = self.layout.var_count();
        let mut values: Vec<Value> = Vec::with_capacity(num_vars);

        for (var_idx, vl) in self.layout.iter().enumerate() {
            let slots = &self.buffer[vl.offset..vl.offset + vl.slot_count];
            let _ = var_idx; // Used only for iteration ordering.

            let value = match &vl.kind {
                VarLayoutKind::Scalar => Value::SmallInt(slots[0]),
                VarLayoutKind::ScalarBool => Value::Bool(slots[0] != 0),
                VarLayoutKind::ScalarString => {
                    let name_id = tla_core::NameId(slots[0] as u32);
                    Value::String(tla_core::resolve_name_id(name_id))
                }
                VarLayoutKind::ScalarModelValue => {
                    let name_id = tla_core::NameId(slots[0] as u32);
                    Value::ModelValue(tla_core::resolve_name_id(name_id))
                }
                VarLayoutKind::IntArray {
                    lo,
                    len,
                    elements_are_bool,
                    element_types,
                } => reconstruct_int_array(*lo, *len, *elements_are_bool, element_types.as_deref(), slots),
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                    field_types,
                } => reconstruct_record(field_names, field_is_bool, field_types, slots),
                VarLayoutKind::StringKeyedArray {
                    domain_keys,
                    domain_types,
                    value_types,
                } => reconstruct_string_keyed_array(domain_keys, domain_types, value_types, slots),
                VarLayoutKind::Bitmask { .. } => {
                    // Bitmask placeholder: return as integer.
                    Value::SmallInt(slots[0])
                }
                VarLayoutKind::Dynamic => {
                    // Dynamic: the slot is 0 — return Bool(false) placeholder.
                    // Caller should use patch_dynamic_vars to fix these.
                    Value::Bool(false)
                }
            };
            values.push(value);
        }

        ArrayState::from_values(values)
    }

    /// Patch dynamic variables from an `ArrayState`.
    ///
    /// For any variable with `VarLayoutKind::Dynamic`, copies the value from
    /// the given `ArrayState` into this `FlatState`'s corresponding
    /// `to_array_state()` result. This is used in a two-phase pattern:
    ///
    /// 1. `flat.to_array_state()` — gets scalars/arrays right, dynamics wrong.
    /// 2. For each dynamic var, copy from the original ArrayState.
    ///
    /// Returns a new ArrayState with all values correct.
    pub(crate) fn to_array_state_with_fallback(
        &self,
        registry: &VarRegistry,
        original: &ArrayState,
    ) -> ArrayState {
        let num_vars = self.layout.var_count();
        let mut values: Vec<Value> = Vec::with_capacity(num_vars);

        for (var_idx, vl) in self.layout.iter().enumerate() {
            let slots = &self.buffer[vl.offset..vl.offset + vl.slot_count];

            let value = match &vl.kind {
                VarLayoutKind::Dynamic => {
                    // Use original ArrayState value for dynamic vars.
                    let idx = crate::var_index::VarIndex::new(var_idx);
                    original.get(idx)
                }
                VarLayoutKind::Scalar => Value::SmallInt(slots[0]),
                VarLayoutKind::ScalarBool => Value::Bool(slots[0] != 0),
                VarLayoutKind::ScalarString => {
                    let name_id = tla_core::NameId(slots[0] as u32);
                    Value::String(tla_core::resolve_name_id(name_id))
                }
                VarLayoutKind::ScalarModelValue => {
                    let name_id = tla_core::NameId(slots[0] as u32);
                    Value::ModelValue(tla_core::resolve_name_id(name_id))
                }
                VarLayoutKind::IntArray {
                    lo,
                    len,
                    elements_are_bool,
                    element_types,
                } => reconstruct_int_array(*lo, *len, *elements_are_bool, element_types.as_deref(), slots),
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                    field_types,
                } => reconstruct_record(field_names, field_is_bool, field_types, slots),
                VarLayoutKind::StringKeyedArray {
                    domain_keys,
                    domain_types,
                    value_types,
                } => reconstruct_string_keyed_array(domain_keys, domain_types, value_types, slots),
                VarLayoutKind::Bitmask { .. } => {
                    // Bitmask: use original for exact roundtrip.
                    let idx = crate::var_index::VarIndex::new(var_idx);
                    original.get(idx)
                }
            };
            values.push(value);
        }

        let _ = registry; // Used for API consistency with other conversion methods.
        ArrayState::from_values(values)
    }
}

impl PartialEq for FlatState {
    /// Two FlatStates are equal iff their buffers are equal.
    ///
    /// Layout identity is not checked — two states with the same buffer
    /// contents but different layouts are considered equal. In practice,
    /// all FlatStates in a model checking run share the same layout.
    fn eq(&self, other: &Self) -> bool {
        self.buffer == other.buffer
    }
}

impl Eq for FlatState {}

impl Hash for FlatState {
    /// Hash via xxh3-128 fingerprint of the flat buffer.
    ///
    /// This uses the same xxh3-128 algorithm as `fingerprint_xxh3()` to
    /// produce a u128 fingerprint, then feeds both halves through the
    /// `Hasher`. This ensures that FlatState can be used in hash-based
    /// collections (HashSet, HashMap) with high collision resistance.
    ///
    /// Part of #3986.
    fn hash<H: Hasher>(&self, state: &mut H) {
        let fp = fingerprint_flat_xxh3(&self.buffer);
        fp.hash(state);
    }
}

impl fmt::Display for FlatState {
    /// Display as `FlatState[N slots, M bytes]`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FlatState[{} slots, {} bytes]",
            self.buffer.len(),
            self.total_bytes()
        )
    }
}

// ============================================================================
// Conversion helpers
// ============================================================================

/// Write an ArrayState's compact values into a pre-existing `[i64]` buffer
/// using the given layout. Shared by `from_array_state` and `write_array_state_into`.
///
/// The buffer must be zero-initialized and have length `>= layout.total_slots()`.
fn write_array_state_into_buffer(
    compact_values: &[CompactValue],
    layout: &StateLayout,
    buffer: &mut [i64],
) {
    for (var_idx, vl) in layout.iter().enumerate() {
        let cv = &compact_values[var_idx];
        let slots = &mut buffer[vl.offset..vl.offset + vl.slot_count];

        match &vl.kind {
            VarLayoutKind::Scalar
            | VarLayoutKind::ScalarBool
            | VarLayoutKind::ScalarString
            | VarLayoutKind::ScalarModelValue => {
                slots[0] = compact_value_to_i64(cv);
            }
            VarLayoutKind::IntArray { lo, len, .. } => {
                let value = Value::from(cv);
                write_int_array_slots(&value, *lo, *len, slots);
            }
            VarLayoutKind::Record { field_names, .. } => {
                let value = Value::from(cv);
                write_record_slots(&value, field_names, slots);
            }
            VarLayoutKind::StringKeyedArray {
                domain_keys,
                domain_types,
                ..
            } => {
                let value = Value::from(cv);
                write_string_keyed_array_slots(&value, domain_keys, domain_types, slots);
            }
            VarLayoutKind::Bitmask { .. } => {
                slots[0] = compact_value_to_i64(cv);
            }
            VarLayoutKind::Dynamic => {
                slots[0] = 0;
            }
        }
    }
}

/// Convert a CompactValue to a single i64 slot value.
///
/// Bool → 0/1, SmallInt → raw i64, String → NameId as i64,
/// ModelValue → NameId as i64, otherwise → 0 (unsupported).
/// Part of #3908: string/model-value flat state roundtrip.
///
/// Handles both inline-tagged (TAG_STRING/TAG_MODEL) and heap-tagged
/// (TAG_HEAP wrapping `Value::String`/`Value::ModelValue`) representations.
/// Production CompactValues constructed via `CompactValue::from(Value)` are
/// always TAG_HEAP for strings/model-values; the inline tags only arise in
/// tests. Missing the heap branch causes `ScalarString`/`ScalarModelValue`
/// variables to be flattened as 0 and reconstructed as the NameId-0 interned
/// string, which corrupts state during flat BFS roundtrip (#4278).
fn compact_value_to_i64(cv: &CompactValue) -> i64 {
    if cv.is_int() {
        cv.as_int()
    } else if cv.is_bool() {
        i64::from(cv.as_bool())
    } else if cv.is_string() {
        cv.as_string_id() as i64
    } else if cv.is_model_value() {
        cv.as_model_value_id() as i64
    } else if cv.is_heap() {
        // TAG_HEAP wrapping a String/ModelValue — intern the Arc<str> and
        // return the NameId. Fixes #4278.
        match Value::from(cv) {
            Value::String(ref s) => tla_core::intern_name(s).0 as i64,
            Value::ModelValue(ref s) => tla_core::intern_name(s).0 as i64,
            _ => 0,
        }
    } else {
        0
    }
}

/// Write an IntFunc / Func value into contiguous i64 slots.
///
/// Defensively tolerates length mismatches between the value and the layout's
/// `len` (zero-pads when the value has fewer elements, truncates when it has
/// more). Length mismatches indicate a layout inference bug (the inferred
/// `IntArray{len}` doesn't match the actual state), which should be caught
/// upstream by wavefront inference (#4287). The defensive bounds handling here
/// prevents panics in `write_array_state_into_buffer` while the upstream
/// mismatch is surfaced through state_mismatch diagnostics.
fn write_int_array_slots(value: &Value, lo: i64, len: usize, slots: &mut [i64]) {
    // Zero-init so short values leave trailing slots deterministic.
    for slot in slots.iter_mut() {
        *slot = 0;
    }
    let write_len = std::cmp::min(len, slots.len());
    match value {
        Value::IntFunc(ref func) => {
            let values = func.values();
            let n = std::cmp::min(write_len, values.len());
            for (slot, val) in slots.iter_mut().take(n).zip(values.iter().take(n)) {
                *slot = value_to_scalar_i64(val);
            }
        }
        Value::Func(ref func) => {
            for (i, slot) in slots.iter_mut().take(write_len).enumerate() {
                let key = Value::SmallInt(lo + i as i64);
                if let Some(val) = func.apply(&key) {
                    *slot = value_to_scalar_i64(val);
                }
            }
        }
        _ => {
            // Already zero-filled above.
        }
    }
}

/// Write a record's fields into contiguous i64 slots.
fn write_record_slots(value: &Value, _field_names: &[Arc<str>], slots: &mut [i64]) {
    match value {
        Value::Record(ref rec) => {
            // rec.iter() yields (NameId, &Value) in sorted NameId order,
            // which matches the field_names order (also sorted by NameId).
            for (i, (_nid, val)) in rec.iter().enumerate() {
                if i < slots.len() {
                    slots[i] = value_to_scalar_i64(val);
                }
            }
        }
        _ => {
            for slot in slots.iter_mut() {
                *slot = 0;
            }
        }
    }
}

/// Convert a Value to a scalar i64 (for array/record element storage).
///
/// String → NameId as i64, ModelValue → NameId as i64.
/// Part of #3908: string/model-value flat state roundtrip.
fn value_to_scalar_i64(value: &Value) -> i64 {
    match value {
        Value::SmallInt(n) => *n,
        Value::Int(n) => {
            use num_traits::ToPrimitive;
            n.to_i64().unwrap_or(0)
        }
        Value::Bool(b) => i64::from(*b),
        Value::String(s) => tla_core::intern_name(s).0 as i64,
        Value::ModelValue(s) => tla_core::intern_name(s).0 as i64,
        _ => 0,
    }
}

/// Reconstruct an IntFunc from contiguous i64 slots.
///
/// When `element_types` is `Some`, uses per-element type tags to reconstruct
/// strings and model-values correctly. Otherwise falls back to
/// `elements_are_bool` for uniform Bool/Int elements. Part of #3908.
fn reconstruct_int_array(
    lo: i64,
    len: usize,
    elements_are_bool: bool,
    element_types: Option<&[SlotType]>,
    slots: &[i64],
) -> Value {
    use std::sync::Arc;
    use tla_value::value::IntIntervalFunc;

    let hi = lo + (len as i64) - 1;
    let values: Vec<Value> = if let Some(types) = element_types {
        slots
            .iter()
            .zip(types.iter())
            .map(|(&s, ty)| reconstruct_slot_value(s, *ty))
            .collect()
    } else if elements_are_bool {
        slots.iter().map(|&s| Value::Bool(s != 0)).collect()
    } else {
        slots.iter().map(|&s| Value::SmallInt(s)).collect()
    };
    Value::IntFunc(Arc::new(IntIntervalFunc::new(lo, hi, values)))
}

/// Reconstruct a Record from contiguous i64 slots.
///
/// Uses `field_types` for per-field type-aware reconstruction (String,
/// ModelValue, Bool, Int). Falls back to `field_is_bool` when field_types
/// contains only Int/Bool. Part of #3908.
fn reconstruct_record(
    field_names: &[Arc<str>],
    field_is_bool: &[bool],
    field_types: &[SlotType],
    slots: &[i64],
) -> Value {
    use tla_value::value::RecordValue;

    let entries: Vec<(Arc<str>, Value)> = field_names
        .iter()
        .zip(field_types.iter())
        .zip(field_is_bool.iter())
        .zip(slots.iter())
        .map(|(((name, ty), &is_bool), &slot)| {
            let val = reconstruct_slot_value_with_bool_fallback(slot, *ty, is_bool);
            (Arc::clone(name), val)
        })
        .collect();
    Value::Record(RecordValue::from_sorted_str_entries(entries))
}

/// Write a string-keyed function's values into contiguous i64 slots.
///
/// The domain keys define the canonical order. `domain_types` selects the key
/// type (`String` vs `ModelValue`) for each slot. Each range value is written
/// as a scalar i64 (using `value_to_scalar_i64` which handles strings).
///
/// Part of #3908 / #4277.
fn write_string_keyed_array_slots(
    value: &Value,
    domain_keys: &[Arc<str>],
    domain_types: &[SlotType],
    slots: &mut [i64],
) {
    match value {
        Value::Func(ref func) => {
            for (i, (key_str, key_ty)) in
                domain_keys.iter().zip(domain_types.iter()).enumerate()
            {
                let key = match key_ty {
                    SlotType::ModelValue => Value::ModelValue(Arc::clone(key_str)),
                    _ => Value::String(Arc::clone(key_str)),
                };
                if let Some(val) = func.apply(&key) {
                    slots[i] = value_to_scalar_i64(val);
                } else {
                    // Fallback: try the other key type. Guards against specs
                    // where successor states happen to type domain keys
                    // differently from the initial state used for inference.
                    let alt_key = match key_ty {
                        SlotType::ModelValue => Value::String(Arc::clone(key_str)),
                        _ => Value::ModelValue(Arc::clone(key_str)),
                    };
                    if let Some(val) = func.apply(&alt_key) {
                        slots[i] = value_to_scalar_i64(val);
                    }
                }
            }
        }
        _ => {
            for slot in slots.iter_mut() {
                *slot = 0;
            }
        }
    }
}

/// Reconstruct a Func with string/model-value domain from contiguous i64 slots.
///
/// Produces a `Value::Func` whose domain keys are `Value::String` or
/// `Value::ModelValue` per the original layout's `domain_types`, and whose
/// range values are reconstructed via per-element `value_types`.
///
/// Fixes #4277: previously always emitted `Value::String` for domain keys,
/// which silently corrupted specs with ModelValue domains (e.g. `RM = {rm1,
/// rm2, rm3}` with `rmState = [rm \in RM |-> "working"]`).
///
/// Part of #3908 / #4277.
fn reconstruct_string_keyed_array(
    domain_keys: &[Arc<str>],
    domain_types: &[SlotType],
    value_types: &[SlotType],
    slots: &[i64],
) -> Value {
    use tla_value::value::FuncValue;

    let entries: Vec<(Value, Value)> = domain_keys
        .iter()
        .zip(domain_types.iter())
        .zip(value_types.iter())
        .zip(slots.iter())
        .map(|(((key_str, key_ty), val_ty), &slot)| {
            let key = match key_ty {
                SlotType::ModelValue => Value::ModelValue(Arc::clone(key_str)),
                _ => Value::String(Arc::clone(key_str)),
            };
            let val = reconstruct_slot_value(slot, *val_ty);
            (key, val)
        })
        .collect();
    Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
}

/// Reconstruct a single Value from an i64 slot using its SlotType.
/// Part of #3908.
fn reconstruct_slot_value(slot: i64, ty: SlotType) -> Value {
    match ty {
        SlotType::Bool => Value::Bool(slot != 0),
        SlotType::String => {
            let name_id = tla_core::NameId(slot as u32);
            Value::String(tla_core::resolve_name_id(name_id))
        }
        SlotType::ModelValue => {
            let name_id = tla_core::NameId(slot as u32);
            Value::ModelValue(tla_core::resolve_name_id(name_id))
        }
        SlotType::Int => Value::SmallInt(slot),
    }
}

/// Reconstruct a single Value with fallback to field_is_bool for backward compat.
/// When SlotType is Int and field_is_bool is true, produces Bool.
/// Part of #3908.
fn reconstruct_slot_value_with_bool_fallback(slot: i64, ty: SlotType, is_bool: bool) -> Value {
    match ty {
        SlotType::Bool => Value::Bool(slot != 0),
        SlotType::String => {
            let name_id = tla_core::NameId(slot as u32);
            Value::String(tla_core::resolve_name_id(name_id))
        }
        SlotType::ModelValue => {
            let name_id = tla_core::NameId(slot as u32);
            Value::ModelValue(tla_core::resolve_name_id(name_id))
        }
        SlotType::Int => {
            if is_bool {
                Value::Bool(slot != 0)
            } else {
                Value::SmallInt(slot)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::var_index::VarRegistry;
    use std::sync::Arc;

    fn make_scalar_layout(registry: &VarRegistry) -> Arc<StateLayout> {
        let kinds = (0..registry.len()).map(|_| VarLayoutKind::Scalar).collect();
        Arc::new(StateLayout::new(registry, kinds))
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_new_zeroed() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::new(layout);

        assert_eq!(flat.buffer().len(), 2);
        assert_eq!(flat.buffer()[0], 0);
        assert_eq!(flat.buffer()[1], 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_get_var_slots() {
        let registry = VarRegistry::from_names(["a", "b", "c"]);
        let kinds = vec![
            VarLayoutKind::Scalar,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                element_types: None,
            },
            VarLayoutKind::Scalar,
        ];
        let layout = Arc::new(StateLayout::new(&registry, kinds));
        let mut flat = FlatState::new(layout);

        // Write to var 1 (IntArray with 3 slots at offset 1)
        let slots = flat.get_var_slots_mut(1).unwrap();
        slots[0] = 10;
        slots[1] = 20;
        slots[2] = 30;

        // Read back
        let slots = flat.get_var_slots(1).unwrap();
        assert_eq!(slots, &[10, 20, 30]);

        // Var 0 is still at offset 0
        assert_eq!(flat.get_var_slots(0).unwrap(), &[0]);
        // Var 2 is at offset 4
        assert_eq!(flat.get_var_slots(2).unwrap(), &[0]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_scalar_values() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);

        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));

        assert_eq!(flat.buffer(), &[42, -7]);

        let restored = flat.to_array_state(&registry);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(42)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(1)),
            Value::SmallInt(-7)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_bool_with_scalar_bool_kind() {
        // ScalarBool layout preserves Bool type through roundtrip. Fixes #4007.
        let registry = VarRegistry::from_names(["flag", "done"]);
        let kinds = vec![VarLayoutKind::ScalarBool, VarLayoutKind::ScalarBool];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        let array = ArrayState::from_values(vec![Value::Bool(true), Value::Bool(false)]);
        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));

        assert_eq!(flat.buffer(), &[1, 0]);

        let restored = flat.to_array_state(&registry);
        // ScalarBool roundtrip preserves Bool type exactly.
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::Bool(true)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(false)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_bool_with_plain_scalar_returns_int() {
        // When a Bool is stored in a plain Scalar (not ScalarBool) slot,
        // roundtrip returns SmallInt. This is expected — callers should use
        // infer_layout() which produces ScalarBool for Bool variables.
        let registry = VarRegistry::from_names(["flag"]);
        let layout = make_scalar_layout(&registry);

        let array = ArrayState::from_values(vec![Value::Bool(true)]);
        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));

        assert_eq!(flat.buffer(), &[1]);

        let restored = flat.to_array_state(&registry);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(1)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_int_array() {
        use tla_value::value::IntIntervalFunc;

        let registry = VarRegistry::from_names(["f"]);
        let kinds = vec![VarLayoutKind::IntArray {
            lo: 1,
            len: 3,
            elements_are_bool: false,
            element_types: None,
        }];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        // f = [1 |-> 10, 2 |-> 20, 3 |-> 30]
        let func = IntIntervalFunc::new(
            1,
            3,
            vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
                Value::SmallInt(30),
            ],
        );
        let array = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        assert_eq!(flat.buffer(), &[10, 20, 30]);

        // Roundtrip
        let restored = flat.to_array_state(&registry);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::IntFunc(ref f) => {
                assert_eq!(f.len(), 3);
                assert_eq!(IntIntervalFunc::min(&f), 1);
                assert_eq!(f.values()[0], Value::SmallInt(10));
                assert_eq!(f.values()[1], Value::SmallInt(20));
                assert_eq!(f.values()[2], Value::SmallInt(30));
            }
            other => panic!("expected IntFunc, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_with_dynamic_fallback() {
        use tla_value::value::SortedSet;

        let registry = VarRegistry::from_names(["count", "data"]);
        let kinds = vec![VarLayoutKind::Scalar, VarLayoutKind::Dynamic];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        // data = {1, 2, 3} — a set, which is Dynamic
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let original =
            ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);

        let flat = FlatState::from_array_state(&original, Arc::clone(&layout));
        assert_eq!(flat.buffer()[0], 99); // scalar
        assert_eq!(flat.buffer()[1], 0); // dynamic placeholder

        // to_array_state gives placeholder for dynamic
        let naive = flat.to_array_state(&registry);
        assert_eq!(
            naive.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(99)
        );
        // Dynamic var gets Bool(false) placeholder
        assert_eq!(
            naive.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(false)
        );

        // to_array_state_with_fallback gives the original value
        let patched = flat.to_array_state_with_fallback(&registry, &original);
        assert_eq!(
            patched.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(99)
        );
        let data_val = patched.get(crate::var_index::VarIndex::new(1));
        match data_val {
            Value::Set(ref s) => assert_eq!(s.len(), 3),
            other => panic!("expected Set, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_record() {
        use tla_value::value::RecordValue;

        let registry = VarRegistry::from_names(["r"]);
        let kinds = vec![VarLayoutKind::Record {
            field_names: vec![Arc::from("a"), Arc::from("b")],
            field_is_bool: vec![false, false],
            field_types: vec![SlotType::Int, SlotType::Int],
        }];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::SmallInt(5)),
            (Arc::from("b"), Value::SmallInt(10)),
        ]);
        let array = ArrayState::from_values(vec![Value::Record(rec)]);

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        assert_eq!(flat.buffer(), &[5, 10]);

        let restored = flat.to_array_state(&registry);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::Record(ref r) => {
                assert_eq!(r.len(), 2);
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_bool_via_inferred_layout() {
        // End-to-end test: infer_layout + from_array_state + to_array_state
        // should preserve Bool type exactly. This is the fix for #4007.
        use super::super::layout_inference::infer_layout;

        let registry = VarRegistry::from_names(["x", "flag", "y"]);
        let array = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-1),
        ]);

        let layout = Arc::new(infer_layout(&array, &registry));

        // Verify inferred kinds
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::ScalarBool
        ));
        assert!(matches!(
            layout.var_layout(2).unwrap().kind,
            VarLayoutKind::Scalar
        ));

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        assert_eq!(flat.buffer(), &[42, 1, -1]);

        let restored = flat.to_array_state(&registry);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(42),
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(true),
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(2)),
            Value::SmallInt(-1),
        );

        // Also test Bool(false) roundtrip
        let array_false = ArrayState::from_values(vec![
            Value::SmallInt(0),
            Value::Bool(false),
            Value::SmallInt(0),
        ]);
        let flat_false = FlatState::from_array_state(&array_false, Arc::clone(&layout));
        assert_eq!(flat_false.buffer(), &[0, 0, 0]);

        let restored_false = flat_false.to_array_state(&registry);
        assert_eq!(
            restored_false.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(0),
        );
        assert_eq!(
            restored_false.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(false),
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_inferred_as_dynamic_not_bitmask() {
        // Sets should be inferred as Dynamic (not Bitmask) until
        // bitmask encoding is implemented. See #4007.
        use super::super::layout_inference::infer_layout;
        use tla_value::value::SortedSet;

        let registry = VarRegistry::from_names(["nodes"]);
        let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let array = ArrayState::from_values(vec![Value::Set(Arc::new(set))]);

        let layout = infer_layout(&array, &registry);
        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "expected Dynamic for set variable, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_record_with_bool_fields() {
        // Fixes #4014: Record fields that are Bool should roundtrip as Bool,
        // not SmallInt.
        use super::super::layout_inference::infer_layout;
        use tla_value::value::RecordValue;

        let registry = VarRegistry::from_names(["r"]);
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("count"), Value::SmallInt(5)),
            (Arc::from("enabled"), Value::Bool(true)),
        ]);
        let array = ArrayState::from_values(vec![Value::Record(rec)]);

        let layout = Arc::new(infer_layout(&array, &registry));

        // Verify the Record layout has correct field_is_bool tracking
        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::Record {
                field_names,
                field_is_bool,
                ..
            } => {
                assert_eq!(field_names.len(), 2);
                // Fields are sorted: "count" then "enabled"
                assert!(!field_is_bool[0], "count should not be bool");
                assert!(field_is_bool[1], "enabled should be bool");
            }
            other => panic!("expected Record, got {other:?}"),
        }

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        assert_eq!(flat.buffer(), &[5, 1]);

        let restored = flat.to_array_state(&registry);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::Record(ref r) => {
                assert_eq!(r.len(), 2);
                // Verify count is SmallInt and enabled is Bool
                let entries: Vec<_> = r.iter().collect();
                assert_eq!(*entries[0].1, Value::SmallInt(5));
                assert_eq!(*entries[1].1, Value::Bool(true));
            }
            other => panic!("expected Record, got {other:?}"),
        }

        // Also test with Bool(false) to verify 0 roundtrips correctly
        let rec_false = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("count"), Value::SmallInt(0)),
            (Arc::from("enabled"), Value::Bool(false)),
        ]);
        let array_false = ArrayState::from_values(vec![Value::Record(rec_false)]);
        let flat_false = FlatState::from_array_state(&array_false, Arc::clone(&layout));
        assert_eq!(flat_false.buffer(), &[0, 0]);

        let restored_false = flat_false.to_array_state(&registry);
        let val_false = restored_false.get(crate::var_index::VarIndex::new(0));
        match val_false {
            Value::Record(ref r) => {
                let entries: Vec<_> = r.iter().collect();
                assert_eq!(*entries[0].1, Value::SmallInt(0));
                assert_eq!(*entries[1].1, Value::Bool(false));
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_int_array_with_bool_elements() {
        // Fixes #4014: IntFunc with Bool elements should roundtrip as Bool,
        // not SmallInt.
        use super::super::layout_inference::infer_layout;
        use tla_value::value::IntIntervalFunc;

        let registry = VarRegistry::from_names(["active"]);
        // active = [0 |-> FALSE, 1 |-> TRUE, 2 |-> FALSE]
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(false), Value::Bool(true), Value::Bool(false)],
        );
        let array = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);

        let layout = Arc::new(infer_layout(&array, &registry));

        // Verify the IntArray layout has elements_are_bool=true
        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::IntArray {
                lo,
                len,
                elements_are_bool,
                ..
            } => {
                assert_eq!(*lo, 0);
                assert_eq!(*len, 3);
                assert!(
                    *elements_are_bool,
                    "Bool-valued IntFunc should track elements_are_bool"
                );
            }
            other => panic!("expected IntArray, got {other:?}"),
        }

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        assert_eq!(flat.buffer(), &[0, 1, 0]);

        let restored = flat.to_array_state(&registry);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::IntFunc(ref f) => {
                assert_eq!(f.len(), 3);
                // Verify elements are Bool, not SmallInt
                assert_eq!(f.values()[0], Value::Bool(false));
                assert_eq!(f.values()[1], Value::Bool(true));
                assert_eq!(f.values()[2], Value::Bool(false));
            }
            other => panic!("expected IntFunc, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_int_array_with_int_elements_unchanged() {
        // Regression test: IntFunc with Int elements should still produce SmallInt.
        use super::super::layout_inference::infer_layout;
        use tla_value::value::IntIntervalFunc;

        let registry = VarRegistry::from_names(["counts"]);
        let func = IntIntervalFunc::new(
            1,
            3,
            vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
                Value::SmallInt(30),
            ],
        );
        let array = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);

        let layout = Arc::new(infer_layout(&array, &registry));

        match &layout.var_layout(0).unwrap().kind {
            VarLayoutKind::IntArray {
                elements_are_bool, ..
            } => {
                assert!(
                    !*elements_are_bool,
                    "Int-valued IntFunc should not have elements_are_bool"
                );
            }
            other => panic!("expected IntArray, got {other:?}"),
        }

        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        let restored = flat.to_array_state(&registry);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::IntFunc(ref f) => {
                assert_eq!(f.values()[0], Value::SmallInt(10));
                assert_eq!(f.values()[1], Value::SmallInt(20));
                assert_eq!(f.values()[2], Value::SmallInt(30));
            }
            other => panic!("expected IntFunc, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_record_with_fallback_preserves_bool() {
        // Verify to_array_state_with_fallback also preserves Bool types in records.
        use tla_value::value::RecordValue;

        let registry = VarRegistry::from_names(["r"]);
        let kinds = vec![VarLayoutKind::Record {
            field_names: vec![Arc::from("done"), Arc::from("val")],
            field_is_bool: vec![true, false],
            field_types: vec![SlotType::Bool, SlotType::Int],
        }];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("done"), Value::Bool(true)),
            (Arc::from("val"), Value::SmallInt(42)),
        ]);
        let original = ArrayState::from_values(vec![Value::Record(rec)]);
        let flat = FlatState::from_array_state(&original, Arc::clone(&layout));

        let restored = flat.to_array_state_with_fallback(&registry, &original);
        let val = restored.get(crate::var_index::VarIndex::new(0));
        match val {
            Value::Record(ref r) => {
                let entries: Vec<_> = r.iter().collect();
                assert_eq!(*entries[0].1, Value::Bool(true));
                assert_eq!(*entries[1].1, Value::SmallInt(42));
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_buffer_mut() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let mut flat = FlatState::new(layout);

        flat.buffer_mut()[0] = 42;
        flat.buffer_mut()[1] = -7;

        assert_eq!(flat.buffer(), &[42, -7]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_num_slots_and_total_bytes() {
        let registry = VarRegistry::from_names(["a", "b", "c"]);
        let kinds = vec![
            VarLayoutKind::Scalar,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                element_types: None,
            },
            VarLayoutKind::Scalar,
        ];
        let layout = Arc::new(StateLayout::new(&registry, kinds));
        let flat = FlatState::new(layout);

        // 1 + 3 + 1 = 5 slots
        assert_eq!(flat.num_slots(), 5);
        // 5 slots * 8 bytes = 40 bytes
        assert_eq!(flat.total_bytes(), 40);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_with_slot_changes() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let layout = make_scalar_layout(&registry);
        let array = ArrayState::from_values(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let flat = FlatState::from_array_state(&array, layout);

        let changed = flat.with_slot_changes(&[(0, 10), (2, 30)]);

        assert_eq!(changed.buffer(), &[10, 2, 30]);
        // Original is unmodified.
        assert_eq!(flat.buffer(), &[1, 2, 3]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_copy_buffer_to() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let flat = FlatState::from_array_state(&array, layout);

        let mut target = vec![0i64; 2];
        flat.copy_buffer_to(&mut target);

        assert_eq!(target, vec![42, -7]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_equality() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);

        let a = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]),
            Arc::clone(&layout),
        );
        let b = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]),
            Arc::clone(&layout),
        );
        let c = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(3)]),
            layout,
        );

        assert_eq!(a, b, "same buffers should be equal");
        assert_ne!(a, c, "different buffers should not be equal");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_bytes_acceptance_criterion() {
        // Verify the "bytes per state < 200" acceptance criterion for
        // typical EWD998-like specs. EWD998 with N=3 has 15 slots = 120 bytes.
        use super::super::flat_successor::flat_state_bytes;

        let registry = VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let kinds = vec![
            // active: [Nodes -> BOOLEAN] = 3 slots
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: true,
                element_types: None,
            },
            // color: [Nodes -> {"white","black"}] = 3 slots
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                element_types: None,
            },
            // counter: [Nodes -> Int] = 3 slots
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                element_types: None,
            },
            // pending: [Nodes -> Nat] = 3 slots
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                element_types: None,
            },
            // token.pos = 1 scalar
            VarLayoutKind::Scalar,
            // token.q = 1 scalar
            VarLayoutKind::Scalar,
            // token.color = 1 scalar
            VarLayoutKind::Scalar,
        ];
        let layout = StateLayout::new(&registry, kinds);
        let bytes = flat_state_bytes(&layout);

        // 3+3+3+3+1+1+1 = 15 slots * 8 = 120 bytes
        assert_eq!(layout.total_slots(), 15);
        assert_eq!(bytes, 120);
        assert!(
            bytes < 200,
            "EWD998 N=3 should be under 200 bytes, got {}",
            bytes
        );
    }

    // ====================================================================
    // Hash, Display, fingerprint tests (Part of #3986 Phase 3)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_hash_deterministic() {
        use std::collections::hash_map::DefaultHasher;

        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]),
            layout,
        );

        let mut h1 = DefaultHasher::new();
        flat.hash(&mut h1);
        let hash1 = h1.finish();

        let mut h2 = DefaultHasher::new();
        flat.hash(&mut h2);
        let hash2 = h2.finish();

        assert_eq!(hash1, hash2, "Hash must be deterministic for same FlatState");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_hash_distinguishes_different_states() {
        use std::collections::hash_map::DefaultHasher;

        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let a = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]),
            Arc::clone(&layout),
        );
        let b = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(3)]),
            layout,
        );

        let mut h_a = DefaultHasher::new();
        a.hash(&mut h_a);
        let mut h_b = DefaultHasher::new();
        b.hash(&mut h_b);

        assert_ne!(
            h_a.finish(),
            h_b.finish(),
            "Different FlatStates should have different hashes"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_in_hash_set() {
        use std::collections::HashSet;

        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);

        let mut set = HashSet::new();
        for i in 0..50 {
            let flat = FlatState::from_array_state(
                &ArrayState::from_values(vec![Value::SmallInt(i), Value::SmallInt(i * 2)]),
                Arc::clone(&layout),
            );
            set.insert(flat);
        }

        assert_eq!(set.len(), 50, "50 distinct states should produce 50 entries");

        // Insert a duplicate — should not increase set size.
        let dup = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]),
            layout,
        );
        set.insert(dup);
        assert_eq!(set.len(), 50, "duplicate should not increase set size");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_display() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::new(layout);

        let display = format!("{}", flat);
        assert_eq!(display, "FlatState[3 slots, 24 bytes]");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_xxh3() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]),
            Arc::clone(&layout),
        );

        let fp1 = flat.fingerprint_xxh3();
        let fp2 = flat.fingerprint_xxh3();
        assert_eq!(fp1, fp2, "xxh3 fingerprint must be deterministic");
        assert_ne!(fp1, 0, "xxh3 fingerprint should be non-zero for non-trivial input");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_compiled_u64() {
        // Verify fingerprint_compiled() produces the same result as calling
        // fingerprint_flat_xxh3_u64_with_seed with the domain separation seed.
        use super::super::flat_fingerprint::{fingerprint_flat_xxh3_u64_with_seed, FLAT_COMPILED_DOMAIN_SEED};

        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::from_array_state(
            &ArrayState::from_values(vec![
                Value::SmallInt(42),
                Value::SmallInt(-7),
                Value::SmallInt(100),
            ]),
            Arc::clone(&layout),
        );

        let fp_compiled = flat.fingerprint_compiled();
        let fp_direct = crate::Fingerprint(fingerprint_flat_xxh3_u64_with_seed(
            flat.buffer(),
            FLAT_COMPILED_DOMAIN_SEED,
        ));
        assert_eq!(
            fp_compiled, fp_direct,
            "fingerprint_compiled must match direct fingerprint_flat_xxh3_u64_with_seed(FLAT_COMPILED_DOMAIN_SEED)"
        );

        // Verify determinism.
        assert_eq!(
            flat.fingerprint_compiled(),
            flat.fingerprint_compiled(),
            "fingerprint_compiled must be deterministic"
        );

        // Verify different states produce different fingerprints.
        let flat2 = FlatState::from_array_state(
            &ArrayState::from_values(vec![
                Value::SmallInt(42),
                Value::SmallInt(-7),
                Value::SmallInt(101),
            ]),
            layout,
        );
        assert_ne!(
            flat.fingerprint_compiled(),
            flat2.fingerprint_compiled(),
            "different states must produce different compiled fingerprints"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_state_fingerprint_with_xor_accumulator() {
        use super::super::flat_fingerprint::FlatFingerprinter;

        let registry = VarRegistry::from_names(["x", "y"]);
        let layout = make_scalar_layout(&registry);
        let flat = FlatState::from_array_state(
            &ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]),
            layout,
        );
        let fpr = FlatFingerprinter::new(flat.num_slots());

        let fp1 = flat.fingerprint_with(&fpr);
        let fp2 = fpr.fingerprint(flat.buffer());
        assert_eq!(
            fp1, fp2,
            "fingerprint_with must match direct FlatFingerprinter call"
        );
    }

    // ====================================================================
    // EWD998-like integration test (Part of #3986 Phase 3)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ewd998_like_roundtrip_integration() {
        // Simulates an EWD998-like spec with N=3 nodes:
        //   active: [0..2 -> BOOLEAN]  (3 bool slots)
        //   color:  [0..2 -> {0,1}]    (3 int slots)
        //   counter:[0..2 -> Int]      (3 int slots)
        //   pending:[0..2 -> Nat]      (3 int slots)
        //   token_pos: Int             (1 scalar)
        //   token_q:   Int             (1 scalar)
        //   token_color: Int           (1 scalar)
        // Total: 15 slots = 120 bytes
        use tla_value::value::IntIntervalFunc;
        use super::super::flat_fingerprint::FlatFingerprinter;
        use super::super::flat_successor::FlatSuccessor;

        let registry = VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let kinds = vec![
            VarLayoutKind::IntArray { lo: 0, len: 3, elements_are_bool: true, element_types: None },
            VarLayoutKind::IntArray { lo: 0, len: 3, elements_are_bool: false, element_types: None },
            VarLayoutKind::IntArray { lo: 0, len: 3, elements_are_bool: false, element_types: None },
            VarLayoutKind::IntArray { lo: 0, len: 3, elements_are_bool: false, element_types: None },
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
        ];
        let layout = Arc::new(StateLayout::new(&registry, kinds));

        // Initial state:
        //   active = [0 |-> TRUE, 1 |-> FALSE, 2 |-> FALSE]
        //   color  = [0 |-> 0, 1 |-> 0, 2 |-> 0]  (white=0)
        //   counter = [0 |-> 0, 1 |-> 0, 2 |-> 0]
        //   pending = [0 |-> 0, 1 |-> 0, 2 |-> 0]
        //   token_pos = 0, token_q = 0, token_color = 0
        let active = IntIntervalFunc::new(0, 2, vec![
            Value::Bool(true), Value::Bool(false), Value::Bool(false),
        ]);
        let color = IntIntervalFunc::new(0, 2, vec![
            Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0),
        ]);
        let counter = IntIntervalFunc::new(0, 2, vec![
            Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0),
        ]);
        let pending = IntIntervalFunc::new(0, 2, vec![
            Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0),
        ]);

        let init_state = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(active)),
            Value::IntFunc(Arc::new(color)),
            Value::IntFunc(Arc::new(counter)),
            Value::IntFunc(Arc::new(pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ]);

        let flat_init = FlatState::from_array_state(&init_state, Arc::clone(&layout));

        // Verify slot count and layout.
        assert_eq!(flat_init.num_slots(), 15);
        assert_eq!(flat_init.total_bytes(), 120);

        // Verify buffer contents.
        // active: [1, 0, 0]  (bools as i64)
        // color:  [0, 0, 0]
        // counter: [0, 0, 0]
        // pending: [0, 0, 0]
        // token_pos: 0, token_q: 0, token_color: 0
        assert_eq!(flat_init.buffer(), &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

        // Roundtrip: flat -> ArrayState -> flat
        let roundtrip_array = flat_init.to_array_state(&registry);
        let roundtrip_flat = FlatState::from_array_state(&roundtrip_array, Arc::clone(&layout));
        assert_eq!(
            flat_init.buffer(),
            roundtrip_flat.buffer(),
            "roundtrip must preserve flat buffer exactly"
        );

        // Verify Bool type preservation through roundtrip.
        let active_restored = roundtrip_array.get(crate::var_index::VarIndex::new(0));
        match active_restored {
            Value::IntFunc(ref f) => {
                assert_eq!(f.values()[0], Value::Bool(true));
                assert_eq!(f.values()[1], Value::Bool(false));
                assert_eq!(f.values()[2], Value::Bool(false));
            }
            other => panic!("expected IntFunc for active, got {other:?}"),
        }

        // Now create a successor state (simulate SendMsg: node 0 sends to node 1).
        // Changes: pending[1] += 1, counter[0] -= 1
        let succ_pending = IntIntervalFunc::new(0, 2, vec![
            Value::SmallInt(0), Value::SmallInt(1), Value::SmallInt(0),
        ]);
        let succ_counter = IntIntervalFunc::new(0, 2, vec![
            Value::SmallInt(-1), Value::SmallInt(0), Value::SmallInt(0),
        ]);
        let succ_state = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(IntIntervalFunc::new(0, 2, vec![
                Value::Bool(true), Value::Bool(false), Value::Bool(false),
            ]))),
            Value::IntFunc(Arc::new(IntIntervalFunc::new(0, 2, vec![
                Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0),
            ]))),
            Value::IntFunc(Arc::new(succ_counter)),
            Value::IntFunc(Arc::new(succ_pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ]);
        let flat_succ = FlatState::from_array_state(&succ_state, Arc::clone(&layout));

        // Verify the two flat states differ.
        assert_ne!(flat_init, flat_succ, "init and successor must differ");

        // Verify fingerprints differ.
        let fp_init = flat_init.fingerprint_xxh3();
        let fp_succ = flat_succ.fingerprint_xxh3();
        assert_ne!(fp_init, fp_succ, "fingerprints must differ for different states");

        // Verify FlatSuccessor diff is correct.
        let fingerprinter = FlatFingerprinter::new(flat_init.num_slots());
        let diff = FlatSuccessor::from_flat_diff(&flat_init, &flat_succ, &fingerprinter);

        // Changed slots: counter[0] (slot 6: 0 -> -1) and pending[1] (slot 10: 0 -> 1)
        assert_eq!(diff.num_changes(), 2);

        // Apply diff and verify.
        let materialized = diff.apply_to(&flat_init);
        assert_eq!(
            materialized.buffer(),
            flat_succ.buffer(),
            "applied diff must produce same buffer as direct conversion"
        );

        // Verify diff fingerprint matches direct fingerprint.
        let direct_fp = fingerprinter.fingerprint(flat_succ.buffer());
        assert_eq!(
            diff.fingerprint, direct_fp,
            "diff fingerprint must match direct fingerprint"
        );
    }
}
