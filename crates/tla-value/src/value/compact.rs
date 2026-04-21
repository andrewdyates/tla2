// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! 8-byte tagged value representation for high-performance model checking.
//!
//! `CompactValue` encodes TLA+ values into a single `u64` using tagged pointers.
//! Inline scalars (Bool, SmallInt, interned String, ModelValue) require zero heap
//! allocation. Compound types (Set, Func, Record, etc.) are stored behind a
//! heap pointer with the tag bits cleared.
//!
//! ## Tag Layout (little-endian, 64-bit)
//!
//! ```text
//! Tag bits [2:0]:
//!   000 = Heap pointer to Box<Value> (aligned, tag in low bits)
//!   001 = SmallInt (i61 in bits [63:3])
//!   010 = Bool (bit [3] = value: 0=false, 1=true)
//!   011 = Interned String (u61 intern ID in bits [63:3])
//!   100 = Model Value (u61 intern ID in bits [63:3])
//!   101 = Reserved
//!   110 = Reserved
//!   111 = Nil sentinel (used for uninitialized slots)
//! ```
//!
//! ## Safety Invariants
//!
//! 1. A `CompactValue` with tag `TAG_HEAP` contains a valid, non-null pointer
//!    obtained from `Box::into_raw`. The pointee is exclusively owned.
//! 2. `SmallInt` values fit in i61 (checked at construction time).
//! 3. Intern IDs fit in u61 (checked at construction time).
//! 4. `Drop` reconstructs and drops the `Box<Value>` for heap-allocated values.
//! 5. `Clone` creates a deep copy of heap-allocated values.
#![allow(unsafe_code)]

// === Child modules ===

mod convert;
mod heap;
mod inline;
#[cfg(test)]
mod tests;
mod traits;

// === Tag Constants ===

const TAG_MASK: u64 = 0b111;
const TAG_HEAP: u64 = 0b000;
const TAG_INT: u64 = 0b001;
const TAG_BOOL: u64 = 0b010;
const TAG_STRING: u64 = 0b011;
const TAG_MODEL: u64 = 0b100;
const TAG_NIL: u64 = 0b111;

/// Bit position for the boolean value within a Bool-tagged CompactValue.
const BOOL_VALUE_BIT: u64 = 1 << 3;

/// Maximum i61 value: 2^60 - 1
const MAX_SMALL_INT: i64 = (1_i64 << 60) - 1;
/// Minimum i61 value: -2^60
const MIN_SMALL_INT: i64 = -(1_i64 << 60);

/// Maximum intern ID that fits in 61 bits.
const MAX_INTERN_ID: u64 = (1_u64 << 61) - 1;

/// An 8-byte tagged value for TLA+ model checking.
///
/// This type provides zero-allocation storage for common TLA+ values (booleans,
/// small integers, interned strings) while falling back to heap allocation for
/// compound types (sets, functions, records, sequences, tuples).
///
/// # Size
///
/// `CompactValue` is exactly 8 bytes — 3x smaller than `Value` (24 bytes).
/// Arrays of `CompactValue` enable cache-friendly state representation.
///
/// # Performance
///
/// - **Bool/SmallInt**: Zero heap allocation. Construction and comparison are
///   bitwise operations.
/// - **Interned String/ModelValue**: Zero heap allocation. Stored as intern table
///   IDs, resolved on demand.
/// - **Compound types**: One heap allocation (Box<Value>). Clone allocates a new
///   box. This is the same cost as the current `Value` type for these variants.
#[repr(transparent)]
pub struct CompactValue {
    bits: u64,
}

// === Size assertion ===
const _: () = assert!(std::mem::size_of::<CompactValue>() == 8);

impl CompactValue {
    /// Get the 3-bit tag.
    #[inline(always)]
    pub(super) const fn tag(&self) -> u64 {
        self.bits & TAG_MASK
    }
}
