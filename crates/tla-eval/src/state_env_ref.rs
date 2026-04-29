// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::value::Value;
use tla_value::CompactValue;

/// Borrowed state variable environment (current state's values array).
///
/// Supports two backing storage formats:
/// - `Compact`: points to `[CompactValue]` (8B per slot) — used by ArrayState
/// - `Value`: points to `[Value]` (24B per slot) — used by closure captures
///
/// The hot path (BFS successor generation) always uses `Compact`.
/// `Value` exists for backward compatibility with closure-captured state.
///
/// # Safety
///
/// The underlying slice must remain valid for the duration of any evaluation
/// that uses this ref.
#[derive(Clone, Copy)]
pub enum StateEnvRef {
    /// Points to a `[CompactValue]` array (ArrayState storage).
    Compact {
        ptr: *const CompactValue,
        len: usize,
    },
    /// Points to a `[Value]` array (closure captures, legacy paths).
    Legacy { ptr: *const Value, len: usize },
}

impl StateEnvRef {
    /// Create from a compact value slice (hot path — zero-cost binding).
    ///
    /// Part of #3579: Used by ArrayState::env_ref() for compact state storage.
    #[inline]
    pub fn from_compact_slice(values: &[CompactValue]) -> Self {
        StateEnvRef::Compact {
            ptr: values.as_ptr(),
            len: values.len(),
        }
    }

    /// Create from a Value slice (backward compatibility for closures).
    #[inline]
    pub fn from_slice(values: &[Value]) -> Self {
        StateEnvRef::Legacy {
            ptr: values.as_ptr(),
            len: values.len(),
        }
    }

    /// Number of state variables.
    #[inline(always)]
    pub(crate) fn env_len(&self) -> usize {
        match self {
            StateEnvRef::Compact { len, .. } | StateEnvRef::Legacy { len, .. } => *len,
        }
    }

    /// Get the value at `idx` as an owned `Value`, without bounds checking.
    ///
    /// This is the primary accessor for evaluation. For the Compact variant,
    /// inline scalars (Bool, SmallInt) are reconstructed without allocation.
    /// Heap-backed compound types are cloned from the inner Box<Value>.
    ///
    /// # Safety
    ///
    /// Caller must ensure `idx < self.env_len()`.
    #[inline(always)]
    pub(crate) unsafe fn get_value(self, idx: usize) -> Value {
        match self {
            StateEnvRef::Compact { ptr, len } => {
                debug_assert!(idx < len);
                let cv = &*ptr.add(idx);
                Value::from(cv)
            }
            StateEnvRef::Legacy { ptr, len } => {
                debug_assert!(idx < len);
                (*ptr.add(idx)).clone()
            }
        }
    }

    /// Check if the value at `idx` matches an expected `CompactValue`.
    ///
    /// Part of #3579: Used by op_cache_entry_valid when VarDepMap stores
    /// CompactValue. For the Compact variant, this is a direct CompactValue
    /// comparison (u64 fast-path for identical inline values). For Legacy,
    /// converts the expected CompactValue to Value for comparison.
    ///
    /// # Safety
    ///
    /// Caller must ensure `idx < self.env_len()`.
    #[inline]
    pub(crate) unsafe fn slot_matches_compact(self, idx: usize, expected: &CompactValue) -> bool {
        match self {
            StateEnvRef::Compact { ptr, len } => {
                debug_assert!(idx < len);
                let cv = &*ptr.add(idx);
                cv == expected
            }
            StateEnvRef::Legacy { ptr, len } => {
                debug_assert!(idx < len);
                let expected_val = Value::from(expected);
                (*ptr.add(idx)) == expected_val
            }
        }
    }

    /// Compare values at the same index across two state environments.
    ///
    /// Optimized for the Compact+Compact case: compares raw CompactValue bits
    /// first (O(1) for identical inline values), falling back to Value-level
    /// comparison only when at least one side is heap-backed.
    ///
    /// # Safety
    ///
    /// Caller must ensure `idx` is valid for both `self` and `other`.
    ///
    /// Part of #3579: Direct slot comparison with compact state arrays.
    #[inline]
    pub(crate) unsafe fn values_equal(self, other: Self, idx: usize) -> bool {
        match (self, other) {
            (
                StateEnvRef::Compact { ptr: p1, len: l1 },
                StateEnvRef::Compact { ptr: p2, len: l2 },
            ) => {
                debug_assert!(idx < l1 && idx < l2);
                let cv1 = &*p1.add(idx);
                let cv2 = &*p2.add(idx);
                // Fast path: identical bits means identical value (works for all
                // inline types and same-pointer heap values). Handles ~99% of cases
                // in BFS state comparison.
                if cv1.raw_bits() == cv2.raw_bits() {
                    return true;
                }
                // Both inline (non-heap) with different bits: different values.
                // No need to allocate Values. Covers the common case of two
                // different SmallInt or Bool values.
                if !cv1.is_heap() && !cv2.is_heap() {
                    return false;
                }
                // At least one side is heap-backed. Must convert to Value for
                // deep comparison (handles cross-type coercions like
                // SmallInt(42) == Int(BigInt(42)), Tuple/Seq/Func equivalence).
                let v1 = Value::from(cv1);
                let v2 = Value::from(cv2);
                v1 == v2
            }
            _ => {
                // Mixed or both Legacy — convert to Value and compare
                let v1 = self.get_value(idx);
                let v2 = other.get_value(idx);
                v1 == v2
            }
        }
    }

    /// Get a unique identity for this state array (pointer address).
    /// Part of #346 (Phase 4): Used for cache invalidation - when the state
    /// pointer changes, the ZERO_ARG_OP_CACHE is cleared.
    #[inline]
    pub(crate) fn identity(&self) -> usize {
        match self {
            StateEnvRef::Compact { ptr, .. } => *ptr as usize,
            StateEnvRef::Legacy { ptr, .. } => *ptr as usize,
        }
    }
}

/// Borrowed sparse next-state overlay for ENABLED evaluation.
///
/// Part of #3365: Points to `WitnessState::values` (`&[Option<Value>]`) without
/// owning it. `None` slots = unbound (reads fall through to current state);
/// `Some(v)` slots = bound (primed reads return `v`).
///
/// Safety contract mirrors `StateEnvRef`: the underlying `Box<[Option<Value>]>`
/// inside `WitnessState` must outlive any evaluation that uses this ref.
#[derive(Clone, Copy)]
pub struct SparseStateEnvRef {
    ptr: *const Option<Value>,
    len: usize,
}

// Note: No Send/Sync impls — matches StateEnvRef (which also wraps a raw
// pointer without Send/Sync). EvalCtx is !Send from StateEnvRef, so these
// would be inert anyway. ENABLED evaluation is single-threaded within a
// worker's BFS expansion.

impl SparseStateEnvRef {
    /// Create from a slice of optional values (WitnessState storage).
    #[inline]
    pub fn from_slice(values: &[Option<Value>]) -> Self {
        SparseStateEnvRef {
            ptr: values.as_ptr(),
            len: values.len(),
        }
    }

    /// Get a reference to the optional value at `idx` without bounds checking.
    ///
    /// # Safety
    ///
    /// Caller must ensure `idx < self.len`. The returned reference borrows the
    /// underlying `[Option<Value>]` slice, so the slice must remain live for `'a`.
    #[inline(always)]
    pub unsafe fn get_unchecked<'a>(self, idx: usize) -> &'a Option<Value> {
        debug_assert!(idx < self.len);
        &*self.ptr.add(idx)
    }
}
