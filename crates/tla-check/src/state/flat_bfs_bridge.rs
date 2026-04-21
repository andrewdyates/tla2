// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between `FlatState` and the BFS engine.
//!
//! The BFS engine operates on `ArrayState` + 64-bit `Fingerprint` for state
//! deduplication. The JIT path operates on `FlatState` (contiguous `[i64]`
//! buffers). This module provides the conversion layer at the BFS boundary:
//!
//! 1. **`FlatBfsBridge`**: Reusable converter that holds a shared `StateLayout`
//!    and provides cheap `ArrayState <-> FlatState` conversions.
//!
//! 2. **Fingerprint bridging**: Computes a traditional 64-bit `Fingerprint`
//!    from a `FlatState` by converting back to `ArrayState` and using the
//!    existing fingerprint pipeline. This ensures dedup consistency with
//!    the interpreter path.
//!
//! 3. **Round-trip verification**: Debug-mode assertions that the flat
//!    representation preserves state identity through conversion.
//!
//! # Design
//!
//! The bridge is created once per model-checking run after the first initial
//! state is generated (when `StateLayout` is inferred). It is stored in the
//! `ModelChecker` struct and used at the BFS boundary where states cross
//! between the interpreter (Value-based) and JIT (i64-based) worlds.
//!
//! ## Fingerprint strategy
//!
//! For correctness, the 64-bit fingerprint used for dedup MUST match between
//! the flat path and the interpreter path. The safest approach is to convert
//! FlatState -> ArrayState and use the existing fingerprint pipeline. This
//! is the initial implementation. Future optimization: when `is_fully_flat()`
//! is true, we could compute a compatible 64-bit fingerprint directly from
//! the flat buffer (eliminating the roundtrip), but this requires proving
//! hash equivalence — deferred to Phase 4.
//!
//! Part of #3986: Wire FlatState into BFS engine.

use std::sync::Arc;

use super::array_state::ArrayState;
use super::flat_fingerprint::{FlatFingerprintStrategy, FlatFingerprinter};
use super::flat_state::FlatState;
use super::state_layout::{StateLayout, VarLayoutKind};
use super::value_hash::finalize_fingerprint_xor;
use super::Fingerprint;
use crate::var_index::VarRegistry;
use tla_core::FNV_PRIME;

/// Reusable bridge for converting between `ArrayState` and `FlatState`
/// at the BFS engine boundary.
///
/// Created once per model-checking run and shared across all BFS iterations.
/// The bridge holds the `StateLayout` (shared via `Arc`) and a
/// `FlatFingerprinter` for 128-bit flat fingerprinting.
///
/// Supports two fingerprinting backends via [`FlatFingerprintStrategy`]:
/// - **XOR-accumulator** (default): per-slot splitmix64 salts XORed together.
///   Supports true O(k) incremental diff fingerprinting.
/// - **xxh3-128** (Phase 4, SIMD): single SIMD-accelerated hash call over the
///   byte buffer. ~50 GB/s throughput. For typical 120-byte states, ~2.4ns.
///
/// Part of #3986. xxh3 strategy added as part of #3987.
#[derive(Debug, Clone)]
pub(crate) struct FlatBfsBridge {
    /// Shared layout descriptor for all states in this run.
    layout: Arc<StateLayout>,
    /// XOR-accumulator fingerprinter for 128-bit flat fingerprints.
    /// Kept for backward compatibility and composable diff fingerprinting.
    fingerprinter: FlatFingerprinter,
    /// Unified fingerprint strategy (XOR or xxh3).
    /// Used by strategy-aware methods. Part of #3987.
    strategy: FlatFingerprintStrategy,
    /// Whether all variables are fully flattenable (no Dynamic vars).
    /// When true, the flat buffer is a complete state representation.
    fully_flat: bool,
}

impl FlatBfsBridge {
    /// Create a new bridge from an inferred layout.
    ///
    /// Uses the XOR-accumulator fingerprinting backend by default.
    /// The layout must be inferred from the first initial state using
    /// `infer_layout()`. The bridge is then valid for all states in the
    /// model-checking run (TLA+ guarantees uniform variable types).
    #[must_use]
    pub(crate) fn new(layout: Arc<StateLayout>) -> Self {
        let num_slots = layout.total_slots();
        let fingerprinter = FlatFingerprinter::new(num_slots);
        let strategy = FlatFingerprintStrategy::new_xor(num_slots);
        let fully_flat = layout.is_fully_flat();
        FlatBfsBridge {
            layout,
            fingerprinter,
            strategy,
            fully_flat,
        }
    }

    /// Create a new bridge using the xxh3-128 SIMD fingerprinting backend.
    ///
    /// Uses xxHash3-128 for full-state fingerprinting (~50 GB/s, ~2.4ns for
    /// 120-byte states). Diff fingerprinting copies the buffer and re-hashes
    /// (still extremely fast for n < 20 slots).
    ///
    /// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
    #[must_use]
    pub(crate) fn new_xxh3(layout: Arc<StateLayout>) -> Self {
        let num_slots = layout.total_slots();
        let fingerprinter = FlatFingerprinter::new(num_slots);
        let strategy = FlatFingerprintStrategy::new_xxh3(num_slots);
        let fully_flat = layout.is_fully_flat();
        FlatBfsBridge {
            layout,
            fingerprinter,
            strategy,
            fully_flat,
        }
    }

    /// Convert an `ArrayState` to a `FlatState`.
    ///
    /// This is an O(V) operation where V is the number of state variables.
    /// For fully-flat layouts (no Dynamic vars), the flat buffer is a
    /// complete representation. For layouts with Dynamic vars, the flat
    /// buffer stores 0 placeholders for those variables.
    #[must_use]
    #[inline]
    pub(crate) fn to_flat(&self, array_state: &ArrayState) -> FlatState {
        FlatState::from_array_state(array_state, Arc::clone(&self.layout))
    }

    /// Write an `ArrayState` into a pre-allocated `[i64]` buffer.
    ///
    /// This is the zero-allocation counterpart of `to_flat()`: instead of
    /// allocating a new `Box<[i64]>`, it writes into a caller-provided buffer
    /// (e.g., from a `FlatStatePool`). Returns the number of slots written.
    ///
    /// The buffer must have length `>= layout.total_slots()`.
    ///
    /// Part of #4172: Arena-backed flat state pool.
    #[inline]
    pub(crate) fn write_flat_into(&self, array_state: &ArrayState, buffer: &mut [i64]) -> usize {
        FlatState::write_array_state_into(array_state, &self.layout, buffer)
    }

    /// Convert a `FlatState` back to an `ArrayState`.
    ///
    /// For fully-flat layouts, this is an exact roundtrip. For layouts
    /// with Dynamic variables, the dynamic vars will have placeholder
    /// values (`Bool(false)`). Use `to_array_state_with_fallback` for
    /// layouts with Dynamic vars.
    #[must_use]
    #[inline]
    pub(crate) fn to_array_state(&self, flat: &FlatState, registry: &VarRegistry) -> ArrayState {
        flat.to_array_state(registry)
    }

    /// Convert a `FlatState` back to an `ArrayState`, using the original
    /// `ArrayState` as a fallback for Dynamic variables.
    ///
    /// This is the safe roundtrip path that works for ALL layout kinds.
    /// The original ArrayState is only consulted for Dynamic and Bitmask
    /// variables; all other variables are reconstructed from the flat buffer.
    #[must_use]
    #[inline]
    pub(crate) fn to_array_state_with_fallback(
        &self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: &ArrayState,
    ) -> ArrayState {
        flat.to_array_state_with_fallback(registry, original)
    }

    /// Compute a 128-bit flat fingerprint for the given `ArrayState`.
    ///
    /// Converts to FlatState internally, then fingerprints the flat buffer.
    /// This fingerprint lives in a different space than the traditional
    /// 64-bit `Fingerprint` — it is used for flat-path dedup (Phase 4+).
    #[must_use]
    #[inline]
    pub(crate) fn flat_fingerprint(&self, array_state: &ArrayState) -> u128 {
        let flat = self.to_flat(array_state);
        flat.fingerprint_with(&self.fingerprinter)
    }

    /// Compute a 128-bit flat fingerprint from a pre-converted `FlatState`.
    ///
    /// Avoids the ArrayState -> FlatState conversion when the caller already
    /// has a FlatState (e.g., from JIT output).
    #[must_use]
    #[inline]
    pub(crate) fn flat_fingerprint_from_flat(&self, flat: &FlatState) -> u128 {
        flat.fingerprint_with(&self.fingerprinter)
    }

    /// Compute a 128-bit fingerprint using the configured strategy backend.
    ///
    /// Dispatches through [`FlatFingerprintStrategy`]: either XOR-accumulator
    /// or xxh3-128, depending on how this bridge was constructed.
    ///
    /// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
    #[must_use]
    #[inline]
    pub(crate) fn strategy_fingerprint(&self, array_state: &ArrayState) -> u128 {
        let flat = self.to_flat(array_state);
        self.strategy.fingerprint(flat.buffer())
    }

    /// Compute a 128-bit strategy fingerprint from a pre-converted `FlatState`.
    ///
    /// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
    #[must_use]
    #[inline]
    pub(crate) fn strategy_fingerprint_from_flat(&self, flat: &FlatState) -> u128 {
        self.strategy.fingerprint(flat.buffer())
    }

    /// Compute an incremental strategy fingerprint from a parent buffer,
    /// parent fingerprint, and a list of slot changes.
    ///
    /// For the XOR backend this is a true O(k) incremental update.
    /// For the xxh3 backend this copies + rehashes (still fast for n < 20).
    ///
    /// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
    #[must_use]
    #[inline]
    pub(crate) fn strategy_diff_fingerprint(
        &self,
        parent_buffer: &[i64],
        parent_fp: u128,
        changes: &[(usize, i64, i64)],
        scratch: &mut Vec<i64>,
    ) -> u128 {
        self.strategy.diff(parent_buffer, parent_fp, changes, scratch)
    }

    /// Get the fingerprint strategy.
    ///
    /// Part of #3987.
    #[must_use]
    #[inline]
    pub(crate) fn strategy(&self) -> &FlatFingerprintStrategy {
        &self.strategy
    }

    /// Returns `true` if this bridge uses the xxh3-128 fingerprinting backend.
    ///
    /// Part of #3987.
    #[must_use]
    #[inline]
    pub(crate) fn is_xxh3(&self) -> bool {
        self.strategy.is_xxh3()
    }

    /// Compute the traditional 64-bit `Fingerprint` from a `FlatState`.
    ///
    /// Converts FlatState -> ArrayState and uses the existing fingerprint
    /// pipeline for dedup consistency with the interpreter path.
    ///
    /// For fully-flat layouts, the roundtrip is exact. For layouts with
    /// Dynamic vars, the `original` ArrayState must be provided to
    /// reconstruct the full state.
    ///
    /// This is the BFS dedup-compatible fingerprint. The 128-bit flat
    /// fingerprint is in a different hash space and cannot be used for
    /// dedup against interpreter-generated states.
    #[must_use]
    pub(crate) fn traditional_fingerprint(
        &self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: Option<&ArrayState>,
    ) -> Fingerprint {
        // Fast path: compute directly from flat buffer when possible.
        // This avoids constructing Value objects and ArrayState entirely.
        // Part of #4126.
        if self.fully_flat {
            if let Some(fp) = self.fingerprint_flat_direct(flat, registry) {
                return fp;
            }
        }

        // Slow path: roundtrip through ArrayState.
        let mut array_state = if self.fully_flat {
            flat.to_array_state(registry)
        } else {
            match original {
                Some(orig) => flat.to_array_state_with_fallback(registry, orig),
                None => flat.to_array_state(registry),
            }
        };
        array_state.fingerprint(registry)
    }

    /// Compute the traditional 64-bit `Fingerprint` directly from a `FlatState`
    /// buffer without constructing `Value` objects or `ArrayState`.
    ///
    /// This is the fast path for fully-flat layouts where every variable is
    /// `Scalar`, `ScalarBool`, `IntArray`, or `Record`. For each variable, the
    /// per-value FP64 fingerprint is computed directly from the i64 slots:
    ///
    /// - **Scalar**: `fp64_smallint_lookup(slot)` or byte-at-a-time FP64
    /// - **ScalarBool**: `fp64_bool_lookup(slot != 0)`
    /// - **IntArray**: additive function fingerprint from slots (same algorithm
    ///   as `compute_int_func_additive_fp`)
    /// - **Record**: additive record fingerprint from slots (same algorithm
    ///   as `compute_record_additive_fp`)
    /// - **Dynamic/Bitmask**: returns `None` (caller must fall back to roundtrip)
    ///
    /// The per-variable FP64s are then combined with registry salts using the
    /// same XOR-and-finalize algorithm as `ArrayState::fingerprint()`.
    ///
    /// Returns `Some(Fingerprint)` when all variables can be fingerprinted
    /// directly, `None` when fallback to the roundtrip path is needed.
    ///
    /// Part of #4126: eliminates Value allocation on the BFS dedup hot path.
    #[must_use]
    pub(crate) fn fingerprint_flat_direct(
        &self,
        flat: &FlatState,
        registry: &VarRegistry,
    ) -> Option<Fingerprint> {
        use tla_value::dedup_fingerprint::{
            additive_entry_hash_from_fps, splitmix64, ADDITIVE_FUNC_SEED,
        };
        use tla_value::fingerprint::{
            fp64_bool_lookup, fp64_extend_i32, fp64_extend_i64, fp64_smallint_lookup,
            value_tags::INTVALUE, FP64_INIT,
        };

        let buf = flat.buffer();
        let mut combined_xor = 0u64;

        for (var_idx, var_layout) in self.layout.iter().enumerate() {
            let offset = var_layout.offset;
            let vfp = match &var_layout.kind {
                VarLayoutKind::ScalarBool => fp64_bool_lookup(buf[offset] != 0),
                VarLayoutKind::Scalar => {
                    let n = buf[offset];
                    if let Some(fp) = fp64_smallint_lookup(n) {
                        fp
                    } else {
                        // Outside precomputed range: byte-at-a-time FP64
                        let fp = fp64_extend_i64(FP64_INIT, INTVALUE);
                        if i32::try_from(n).is_ok() {
                            fp64_extend_i32(fp, n as i32)
                        } else {
                            fp64_extend_i64(fp, n)
                        }
                    }
                }
                VarLayoutKind::IntArray {
                    lo,
                    len,
                    elements_are_bool,
                } => {
                    // Same algorithm as compute_int_func_additive_fp in
                    // tla_value::dedup_fingerprint
                    let mut fp = ADDITIVE_FUNC_SEED;
                    fp = fp.wrapping_add(splitmix64(*len as u64));
                    for elem_idx in 0..*len {
                        let key_int = lo
                            .checked_add(elem_idx as i64)
                            .expect("invariant: IntArray index within i64 domain");
                        let slot_val = buf[offset + elem_idx];

                        // Compute the value FP64 for this element
                        let val_fp = if *elements_are_bool {
                            fp64_bool_lookup(slot_val != 0)
                        } else if let Some(fp_val) = fp64_smallint_lookup(slot_val) {
                            fp_val
                        } else {
                            let fp_val = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(slot_val).is_ok() {
                                fp64_extend_i32(fp_val, slot_val as i32)
                            } else {
                                fp64_extend_i64(fp_val, slot_val)
                            }
                        };

                        // Compute the key FP64
                        let key_fp = if let Some(kfp) = fp64_smallint_lookup(key_int) {
                            kfp
                        } else {
                            let kfp = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(key_int).is_ok() {
                                fp64_extend_i32(kfp, key_int as i32)
                            } else {
                                fp64_extend_i64(kfp, key_int)
                            }
                        };

                        fp = fp.wrapping_add(additive_entry_hash_from_fps(key_fp, val_fp));
                    }
                    fp
                }
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                } => {
                    // Same algorithm as compute_record_additive_fp in
                    // tla_value::dedup_fingerprint
                    let mut fp = ADDITIVE_FUNC_SEED;
                    fp = fp.wrapping_add(splitmix64(field_names.len() as u64));
                    for (field_idx, field_name) in field_names.iter().enumerate() {
                        let slot_val = buf[offset + field_idx];

                        // Compute value FP64 for this field
                        let val_fp = if field_is_bool[field_idx] {
                            fp64_bool_lookup(slot_val != 0)
                        } else if let Some(fp_val) = fp64_smallint_lookup(slot_val) {
                            fp_val
                        } else {
                            let fp_val = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(slot_val).is_ok() {
                                fp64_extend_i32(fp_val, slot_val as i32)
                            } else {
                                fp64_extend_i64(fp_val, slot_val)
                            }
                        };

                        // Compute key FP64 from interned field name
                        let key_fp = match tla_core::lookup_name_id(field_name) {
                            Some(name_id) => {
                                tla_core::resolve_name_id_string_fp64(name_id)
                            }
                            None => {
                                // Field name not interned -- cannot compute directly.
                                // Fall back to roundtrip path.
                                return None;
                            }
                        };

                        fp = fp.wrapping_add(additive_entry_hash_from_fps(key_fp, val_fp));
                    }
                    fp
                }
                VarLayoutKind::Bitmask { .. } | VarLayoutKind::Dynamic => {
                    // Cannot fingerprint directly from buffer
                    return None;
                }
            };

            let salt = registry.fp_salt(crate::var_index::VarIndex::new(var_idx));
            let contribution = salt.wrapping_mul(vfp.wrapping_add(1));
            combined_xor ^= contribution;
        }

        let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
        Some(Fingerprint(mixed))
    }

    /// Compute the traditional 64-bit `Fingerprint` directly from a raw
    /// `&[i64]` buffer without constructing a `FlatState` or `ArrayState`.
    ///
    /// This is the zero-allocation fast path for the compiled BFS loop:
    /// successor buffers produced by the JIT are raw `&[i64]` slices, and
    /// wrapping them in `FlatState` (which requires `Box<[i64]>`) is pure
    /// overhead when we only need the fingerprint for dedup.
    ///
    /// Semantically identical to `fingerprint_flat_direct(&FlatState)` but
    /// avoids the heap allocation for the `FlatState` wrapper.
    ///
    /// Returns `Some(Fingerprint)` when all variables can be fingerprinted
    /// directly, `None` when fallback to the roundtrip path is needed
    /// (Dynamic/Bitmask variables present).
    ///
    /// # Panics
    ///
    /// Debug-asserts that `buffer.len() == self.layout.total_slots()`.
    ///
    /// Part of #3986: Phase 3 zero-alloc compiled BFS fingerprinting.
    #[must_use]
    pub(crate) fn fingerprint_buffer_direct(
        &self,
        buffer: &[i64],
        registry: &VarRegistry,
    ) -> Option<Fingerprint> {
        use tla_value::dedup_fingerprint::{
            additive_entry_hash_from_fps, splitmix64, ADDITIVE_FUNC_SEED,
        };
        use tla_value::fingerprint::{
            fp64_bool_lookup, fp64_extend_i32, fp64_extend_i64, fp64_smallint_lookup,
            value_tags::INTVALUE, FP64_INIT,
        };

        debug_assert_eq!(
            buffer.len(),
            self.layout.total_slots(),
            "fingerprint_buffer_direct: buffer has {} slots, expected {}",
            buffer.len(),
            self.layout.total_slots(),
        );

        if !self.fully_flat {
            return None;
        }

        let mut combined_xor = 0u64;

        for (var_idx, var_layout) in self.layout.iter().enumerate() {
            let offset = var_layout.offset;
            let vfp = match &var_layout.kind {
                VarLayoutKind::ScalarBool => fp64_bool_lookup(buffer[offset] != 0),
                VarLayoutKind::Scalar => {
                    let n = buffer[offset];
                    if let Some(fp) = fp64_smallint_lookup(n) {
                        fp
                    } else {
                        let fp = fp64_extend_i64(FP64_INIT, INTVALUE);
                        if i32::try_from(n).is_ok() {
                            fp64_extend_i32(fp, n as i32)
                        } else {
                            fp64_extend_i64(fp, n)
                        }
                    }
                }
                VarLayoutKind::IntArray {
                    lo,
                    len,
                    elements_are_bool,
                } => {
                    let mut fp = ADDITIVE_FUNC_SEED;
                    fp = fp.wrapping_add(splitmix64(*len as u64));
                    for elem_idx in 0..*len {
                        let key_int = lo
                            .checked_add(elem_idx as i64)
                            .expect("invariant: IntArray index within i64 domain");
                        let slot_val = buffer[offset + elem_idx];

                        let val_fp = if *elements_are_bool {
                            fp64_bool_lookup(slot_val != 0)
                        } else if let Some(fp_val) = fp64_smallint_lookup(slot_val) {
                            fp_val
                        } else {
                            let fp_val = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(slot_val).is_ok() {
                                fp64_extend_i32(fp_val, slot_val as i32)
                            } else {
                                fp64_extend_i64(fp_val, slot_val)
                            }
                        };

                        let key_fp = if let Some(kfp) = fp64_smallint_lookup(key_int) {
                            kfp
                        } else {
                            let kfp = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(key_int).is_ok() {
                                fp64_extend_i32(kfp, key_int as i32)
                            } else {
                                fp64_extend_i64(kfp, key_int)
                            }
                        };

                        fp = fp.wrapping_add(additive_entry_hash_from_fps(key_fp, val_fp));
                    }
                    fp
                }
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                } => {
                    let mut fp = ADDITIVE_FUNC_SEED;
                    fp = fp.wrapping_add(splitmix64(field_names.len() as u64));
                    for (field_idx, field_name) in field_names.iter().enumerate() {
                        let slot_val = buffer[offset + field_idx];

                        let val_fp = if field_is_bool[field_idx] {
                            fp64_bool_lookup(slot_val != 0)
                        } else if let Some(fp_val) = fp64_smallint_lookup(slot_val) {
                            fp_val
                        } else {
                            let fp_val = fp64_extend_i64(FP64_INIT, INTVALUE);
                            if i32::try_from(slot_val).is_ok() {
                                fp64_extend_i32(fp_val, slot_val as i32)
                            } else {
                                fp64_extend_i64(fp_val, slot_val)
                            }
                        };

                        let key_fp = match tla_core::lookup_name_id(field_name) {
                            Some(name_id) => {
                                tla_core::resolve_name_id_string_fp64(name_id)
                            }
                            None => {
                                return None;
                            }
                        };

                        fp = fp.wrapping_add(additive_entry_hash_from_fps(key_fp, val_fp));
                    }
                    fp
                }
                VarLayoutKind::Bitmask { .. } | VarLayoutKind::Dynamic => {
                    return None;
                }
            };

            let salt = registry.fp_salt(crate::var_index::VarIndex::new(var_idx));
            let contribution = salt.wrapping_mul(vfp.wrapping_add(1));
            combined_xor ^= contribution;
        }

        let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
        Some(Fingerprint(mixed))
    }

    /// Compute the traditional 64-bit `Fingerprint` from a raw `&[i64]` buffer
    /// with fallback through `ArrayState` roundtrip if direct computation fails.
    ///
    /// This is the primary fingerprint entry point for the compiled BFS loop:
    /// it first tries the zero-allocation `fingerprint_buffer_direct` fast path,
    /// and only falls back to constructing a `FlatState` + `ArrayState` roundtrip
    /// when the layout contains Dynamic/Bitmask variables.
    ///
    /// Part of #3986: Phase 3 zero-alloc compiled BFS fingerprinting.
    #[must_use]
    pub(crate) fn traditional_fingerprint_from_buffer(
        &self,
        buffer: &[i64],
        registry: &VarRegistry,
    ) -> Fingerprint {
        // Fast path: zero allocation.
        if let Some(fp) = self.fingerprint_buffer_direct(buffer, registry) {
            return fp;
        }

        // Slow path: construct FlatState and roundtrip through ArrayState.
        let boxed: Box<[i64]> = buffer.to_vec().into_boxed_slice();
        let flat = FlatState::from_buffer(boxed, Arc::clone(&self.layout));
        self.traditional_fingerprint(&flat, registry, None)
    }

    /// Get the shared layout.
    #[must_use]
    #[inline]
    pub(crate) fn layout(&self) -> &Arc<StateLayout> {
        &self.layout
    }

    /// Get the flat fingerprinter.
    #[must_use]
    #[inline]
    pub(crate) fn fingerprinter(&self) -> &FlatFingerprinter {
        &self.fingerprinter
    }

    /// Whether all variables are fully flattenable.
    #[must_use]
    #[inline]
    pub(crate) fn is_fully_flat(&self) -> bool {
        self.fully_flat
    }

    /// Number of i64 slots in the flat state buffer.
    #[must_use]
    #[inline]
    pub(crate) fn num_slots(&self) -> usize {
        self.layout.total_slots()
    }

    /// Bytes per flat state buffer.
    #[must_use]
    #[inline]
    pub(crate) fn bytes_per_state(&self) -> usize {
        self.layout.total_slots() * std::mem::size_of::<i64>()
    }

    /// Convert this bridge's check layout to the equivalent JIT layout.
    ///
    /// Returns a `tla_jit::StateLayout` whose variable descriptors match the
    /// compact buffer format used by this bridge. JIT code generation can use
    /// this layout to emit Cranelift IR that reads/writes the flat buffer
    /// produced by `to_flat()` and consumed by `to_array_state()`.
    ///
    /// Part of #3986: Phase 3 layout bridge for JIT V2.
    #[cfg(feature = "jit")]
    #[must_use]
    pub(crate) fn to_jit_layout(&self) -> tla_jit::StateLayout {
        super::layout_bridge::check_layout_to_jit_layout(&self.layout)
    }

    /// Verify that the given JIT layout is compatible with this bridge's
    /// check layout (same variable count and slot counts).
    ///
    /// Returns `true` if the two layouts produce identically-sized flat buffers.
    /// Call this at BFS init time to ensure the JIT compiled code and the
    /// model checker agree on the buffer format.
    ///
    /// Part of #3986: Phase 3 layout bridge for JIT V2.
    #[cfg(feature = "jit")]
    #[must_use]
    pub(crate) fn is_compatible_with_jit(&self, jit_layout: &tla_jit::StateLayout) -> bool {
        super::layout_bridge::layouts_compatible(&self.layout, jit_layout)
    }

    /// Verify that the ArrayState -> FlatState -> ArrayState roundtrip
    /// preserves the traditional fingerprint.
    ///
    /// Returns `true` if the fingerprints match, `false` on mismatch.
    /// This is a debug/test utility — not called in production hot paths.
    ///
    /// Part of #3986: correctness acceptance criterion.
    #[must_use]
    pub(crate) fn verify_roundtrip_fingerprint(
        &self,
        array_state: &mut ArrayState,
        registry: &VarRegistry,
    ) -> bool {
        let original_fp = array_state.fingerprint(registry);
        let flat = self.to_flat(array_state);
        let roundtrip_fp = self.traditional_fingerprint(&flat, registry, Some(array_state));
        original_fp == roundtrip_fp
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::layout_inference::infer_layout;
    use crate::Value;
    use std::sync::Arc;
    use tla_value::value::IntIntervalFunc;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_all_scalar_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let array = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        assert!(bridge.is_fully_flat());
        assert_eq!(bridge.num_slots(), 3);
        assert_eq!(bridge.bytes_per_state(), 24);

        // Convert to flat and back
        let flat = bridge.to_flat(&array);
        assert_eq!(flat.buffer(), &[42, 1, -7]);

        let restored = bridge.to_array_state(&flat, &registry);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(42)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(true)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(2)),
            Value::SmallInt(-7)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_fingerprint_roundtrip_preserves_identity() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let mut array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        assert!(bridge.verify_roundtrip_fingerprint(&mut array, &registry));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_int_array_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["pc", "counter"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)],
        );
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(1), Value::IntFunc(Arc::new(func))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        assert!(bridge.is_fully_flat());
        assert_eq!(bridge.num_slots(), 4); // 1 scalar + 3 array elements

        let flat = bridge.to_flat(&array);
        assert_eq!(flat.buffer(), &[1, 10, 20, 30]);

        assert!(bridge.verify_roundtrip_fingerprint(&mut array, &registry));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_dynamic_var_fallback() {
        use tla_value::value::SortedSet;

        let registry = crate::var_index::VarRegistry::from_names(["count", "data"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        assert!(!bridge.is_fully_flat());

        // Flat buffer has placeholder for dynamic var
        let flat = bridge.to_flat(&array);
        assert_eq!(flat.buffer()[0], 99);
        assert_eq!(flat.buffer()[1], 0); // Dynamic placeholder

        // Roundtrip with fallback preserves dynamic value
        let restored = bridge.to_array_state_with_fallback(&flat, &registry, &array);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(99)
        );
        let data = restored.get(crate::var_index::VarIndex::new(1));
        match data {
            Value::Set(ref s) => assert_eq!(s.len(), 3),
            other => panic!("expected Set, got {other:?}"),
        }

        // Traditional fingerprint with fallback matches original
        assert!(bridge.verify_roundtrip_fingerprint(&mut array, &registry));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_flat_fingerprint_deterministic() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let fp1 = bridge.flat_fingerprint(&array);
        let fp2 = bridge.flat_fingerprint(&array);
        assert_eq!(fp1, fp2, "flat fingerprint must be deterministic");
        assert_ne!(fp1, 0, "flat fingerprint should be non-zero");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_flat_fingerprint_distinguishes_states() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let a = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let b = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(3)]);
        let layout = Arc::new(infer_layout(&a, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let fp_a = bridge.flat_fingerprint(&a);
        let fp_b = bridge.flat_fingerprint(&b);
        assert_ne!(fp_a, fp_b, "different states must have different fingerprints");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_ewd998_like() {
        // Simulates EWD998 N=3: 7 variables, 15 slots, 120 bytes
        let registry = crate::var_index::VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let active = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
        );
        let color = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let counter = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let pending = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );

        let mut init = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(active)),
            Value::IntFunc(Arc::new(color)),
            Value::IntFunc(Arc::new(counter)),
            Value::IntFunc(Arc::new(pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ]);

        let layout = Arc::new(infer_layout(&init, &registry));
        let bridge = FlatBfsBridge::new(layout);

        assert!(bridge.is_fully_flat());
        assert_eq!(bridge.num_slots(), 15);
        assert_eq!(bridge.bytes_per_state(), 120);
        assert!(bridge.bytes_per_state() < 200, "acceptance criterion: <200 bytes");

        // Verify fingerprint roundtrip
        assert!(bridge.verify_roundtrip_fingerprint(&mut init, &registry));

        // Test successor diff scenario
        let succ_counter = IntIntervalFunc::new(
            0,
            2,
            vec![
                Value::SmallInt(-1),
                Value::SmallInt(0),
                Value::SmallInt(0),
            ],
        );
        let succ_pending = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(1), Value::SmallInt(0)],
        );
        let mut succ = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                2,
                vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
            ))),
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                2,
                vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
            ))),
            Value::IntFunc(Arc::new(succ_counter)),
            Value::IntFunc(Arc::new(succ_pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ]);

        // Flat fingerprints must differ
        let fp_init = bridge.flat_fingerprint(&init);
        let fp_succ = bridge.flat_fingerprint(&succ);
        assert_ne!(fp_init, fp_succ);

        // Traditional fingerprints must also differ
        let tfp_init = init.fingerprint(&registry);
        let tfp_succ = succ.fingerprint(&registry);
        assert_ne!(tfp_init, tfp_succ);

        // Successor roundtrip must also work
        assert!(bridge.verify_roundtrip_fingerprint(&mut succ, &registry));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_from_flat_fingerprint() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let fp_via_array = bridge.flat_fingerprint(&array);
        let fp_via_flat = bridge.flat_fingerprint_from_flat(&flat);

        assert_eq!(
            fp_via_array, fp_via_flat,
            "flat fingerprint from ArrayState and FlatState must match"
        );
    }

    // ====================================================================
    // xxh3 bridge tests (Part of #3987)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xxh3_constructor_and_is_xxh3() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));

        let xor_bridge = FlatBfsBridge::new(Arc::clone(&layout));
        assert!(!xor_bridge.is_xxh3());

        let xxh3_bridge = FlatBfsBridge::new_xxh3(layout);
        assert!(xxh3_bridge.is_xxh3());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xxh3_strategy_fingerprint_deterministic() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new_xxh3(layout);

        let fp1 = bridge.strategy_fingerprint(&array);
        let fp2 = bridge.strategy_fingerprint(&array);
        assert_eq!(fp1, fp2, "xxh3 strategy fingerprint must be deterministic");
        assert_ne!(fp1, 0, "xxh3 strategy fingerprint should be non-zero");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xxh3_strategy_distinguishes_states() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let a = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let b = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(3)]);
        let layout = Arc::new(infer_layout(&a, &registry));
        let bridge = FlatBfsBridge::new_xxh3(layout);

        let fp_a = bridge.strategy_fingerprint(&a);
        let fp_b = bridge.strategy_fingerprint(&b);
        assert_ne!(fp_a, fp_b, "xxh3: different states must have different fingerprints");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xxh3_strategy_from_flat_matches() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new_xxh3(layout);

        let flat = bridge.to_flat(&array);
        let fp_via_array = bridge.strategy_fingerprint(&array);
        let fp_via_flat = bridge.strategy_fingerprint_from_flat(&flat);

        assert_eq!(
            fp_via_array, fp_via_flat,
            "xxh3 strategy fingerprint from ArrayState and FlatState must match"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xxh3_strategy_diff_fingerprint() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let array = ArrayState::from_values(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new_xxh3(layout);

        let flat = bridge.to_flat(&array);
        let parent_fp = bridge.strategy_fingerprint_from_flat(&flat);

        // Change slot 1 from 20 to 99
        let changes: Vec<(usize, i64, i64)> = vec![(1, 20, 99)];
        let mut scratch = Vec::new();
        let diff_fp = bridge.strategy_diff_fingerprint(
            flat.buffer(),
            parent_fp,
            &changes,
            &mut scratch,
        );

        // Verify against direct fingerprint of modified state
        let modified = ArrayState::from_values(vec![
            Value::SmallInt(10),
            Value::SmallInt(99),
            Value::SmallInt(30),
        ]);
        let direct_fp = bridge.strategy_fingerprint(&modified);
        assert_eq!(
            diff_fp, direct_fp,
            "xxh3 diff fingerprint must match direct fingerprint of modified state"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bridge_xor_and_xxh3_both_dedup_correctly() {
        // Cross-check: both XOR and xxh3 backends must correctly distinguish
        // and identify the same set of states. Part of #3987 acceptance criteria.
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let layout = {
            let sample = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
            Arc::new(infer_layout(&sample, &registry))
        };
        let xor_bridge = FlatBfsBridge::new(Arc::clone(&layout));
        let xxh3_bridge = FlatBfsBridge::new_xxh3(layout);

        let mut xor_fps = std::collections::HashSet::new();
        let mut xxh3_fps = std::collections::HashSet::new();

        for i in 0i64..100 {
            let state = ArrayState::from_values(vec![
                Value::SmallInt(i),
                Value::SmallInt(i * 7 + 3),
            ]);
            let xor_fp = xor_bridge.strategy_fingerprint(&state);
            let xxh3_fp = xxh3_bridge.strategy_fingerprint(&state);

            assert!(
                xor_fps.insert(xor_fp),
                "XOR collision at i={}: fingerprint {:032x} already seen",
                i, xor_fp
            );
            assert!(
                xxh3_fps.insert(xxh3_fp),
                "xxh3 collision at i={}: fingerprint {:032x} already seen",
                i, xxh3_fp
            );
        }
        assert_eq!(xor_fps.len(), 100);
        assert_eq!(xxh3_fps.len(), 100);
    }

    // ====================================================================
    // Direct flat fingerprint tests (Part of #4126)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_scalars_matches_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let mut array = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let roundtrip_fp = array.fingerprint(&registry);

        let direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("all-scalar layout should be directly fingerprintable");

        assert_eq!(
            direct_fp, roundtrip_fp,
            "direct flat fingerprint must match ArrayState fingerprint for scalars"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_int_array_matches_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["pc", "counter"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)],
        );
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(1), Value::IntFunc(Arc::new(func))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let roundtrip_fp = array.fingerprint(&registry);

        let direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("int-array layout should be directly fingerprintable");

        assert_eq!(
            direct_fp, roundtrip_fp,
            "direct flat fingerprint must match ArrayState fingerprint for IntArray"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_bool_array_matches_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["active"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(true)],
        );
        let mut array = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let roundtrip_fp = array.fingerprint(&registry);

        let direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("bool-array layout should be directly fingerprintable");

        assert_eq!(
            direct_fp, roundtrip_fp,
            "direct flat fingerprint must match ArrayState fingerprint for bool IntArray"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_ewd998_like_matches_roundtrip() {
        // Simulates EWD998 N=3: mixed IntArrays + scalars
        let registry = crate::var_index::VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let active = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
        );
        let color = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let counter = IntIntervalFunc::new(
            0,
            2,
            vec![
                Value::SmallInt(-1),
                Value::SmallInt(0),
                Value::SmallInt(0),
            ],
        );
        let pending = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(1), Value::SmallInt(0)],
        );

        let mut state = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(active)),
            Value::IntFunc(Arc::new(color)),
            Value::IntFunc(Arc::new(counter)),
            Value::IntFunc(Arc::new(pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::SmallInt(0),
        ]);
        let layout = Arc::new(infer_layout(&state, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&state);
        let roundtrip_fp = state.fingerprint(&registry);

        let direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("EWD998-like layout should be directly fingerprintable");

        assert_eq!(
            direct_fp, roundtrip_fp,
            "direct flat fingerprint must match ArrayState fingerprint for EWD998"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_dynamic_returns_none() {
        use tla_value::value::SortedSet;

        let registry = crate::var_index::VarRegistry::from_names(["count", "data"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let array =
            ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let result = bridge.fingerprint_flat_direct(&flat, &registry);

        assert!(
            result.is_none(),
            "dynamic layout should return None from fingerprint_flat_direct"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_large_ints_matches_roundtrip() {
        // Test with integers outside the precomputed [-256, 1023] range
        let registry = crate::var_index::VarRegistry::from_names(["big", "huge"]);
        let mut array = ArrayState::from_values(vec![
            Value::SmallInt(100_000),
            Value::SmallInt(-50_000),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let roundtrip_fp = array.fingerprint(&registry);

        let direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("large-int layout should be directly fingerprintable");

        assert_eq!(
            direct_fp, roundtrip_fp,
            "direct flat fingerprint must match for large integers"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_flat_direct_distinguishes_states() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let layout = {
            let sample = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
            Arc::new(infer_layout(&sample, &registry))
        };
        let bridge = FlatBfsBridge::new(layout);

        let mut fps = std::collections::HashSet::new();
        for i in 0i64..200 {
            let state = ArrayState::from_values(vec![
                Value::SmallInt(i),
                Value::SmallInt(i * 7 + 3),
            ]);
            let flat = bridge.to_flat(&state);
            let fp = bridge
                .fingerprint_flat_direct(&flat, &registry)
                .expect("scalar layout should be directly fingerprintable");
            assert!(
                fps.insert(fp),
                "direct flat fingerprint collision at i={i}"
            );
        }
    }

    // ====================================================================
    // Buffer-direct fingerprint tests (Part of #3986 Phase 3)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_buffer_direct_matches_flatstate_direct() {
        // fingerprint_buffer_direct on &[i64] must match fingerprint_flat_direct on FlatState
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let mut array = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let flat_direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("all-scalar layout should be directly fingerprintable");

        let buffer_direct_fp = bridge
            .fingerprint_buffer_direct(flat.buffer(), &registry)
            .expect("all-scalar layout should be directly fingerprintable from buffer");

        assert_eq!(
            flat_direct_fp, buffer_direct_fp,
            "fingerprint_buffer_direct must produce identical result to fingerprint_flat_direct"
        );

        // Also verify it matches the traditional roundtrip fingerprint.
        let roundtrip_fp = array.fingerprint(&registry);
        assert_eq!(
            buffer_direct_fp, roundtrip_fp,
            "fingerprint_buffer_direct must match ArrayState::fingerprint"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_buffer_direct_int_array_matches() {
        let registry = crate::var_index::VarRegistry::from_names(["pc", "counter"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)],
        );
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(1), Value::IntFunc(Arc::new(func))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);
        let flat_direct_fp = bridge
            .fingerprint_flat_direct(&flat, &registry)
            .expect("int-array layout should be directly fingerprintable");

        let buffer_direct_fp = bridge
            .fingerprint_buffer_direct(flat.buffer(), &registry)
            .expect("int-array layout should be directly fingerprintable from buffer");

        assert_eq!(
            flat_direct_fp, buffer_direct_fp,
            "buffer-direct must match flat-direct for IntArray layout"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_traditional_fingerprint_from_buffer_matches_flatstate() {
        // The convenience method traditional_fingerprint_from_buffer must
        // produce the same result as traditional_fingerprint on a FlatState.
        let registry = crate::var_index::VarRegistry::from_names(["a", "b"]);
        let mut array = ArrayState::from_values(vec![
            Value::SmallInt(99),
            Value::SmallInt(-123),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);

        let flat = bridge.to_flat(&array);

        let from_flat = bridge.traditional_fingerprint(&flat, &registry, None);
        let from_buffer = bridge.traditional_fingerprint_from_buffer(flat.buffer(), &registry);

        assert_eq!(
            from_flat, from_buffer,
            "traditional_fingerprint_from_buffer must match traditional_fingerprint"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_buffer_direct_distinguishes_states() {
        // Verify the buffer-direct path produces unique fingerprints for distinct states.
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let layout = {
            let sample = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
            Arc::new(infer_layout(&sample, &registry))
        };
        let bridge = FlatBfsBridge::new(layout);

        let mut fps = std::collections::HashSet::new();
        for i in 0i64..200 {
            let buffer = vec![i, i * 7 + 3];
            let fp = bridge
                .fingerprint_buffer_direct(&buffer, &registry)
                .expect("scalar layout should be directly fingerprintable");
            assert!(
                fps.insert(fp),
                "buffer-direct fingerprint collision at i={i}"
            );
        }
    }
}
