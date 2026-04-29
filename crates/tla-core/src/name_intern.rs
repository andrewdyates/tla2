// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parse-time identifier interning for O(1) lookups
//!
//! This module provides compile-time interning of identifiers for efficient
//! runtime comparison. Instead of comparing strings (O(len) hash + DashMap lookup),
//! we compare integers (O(1)).
//!
//! # Design
//!
//! TLC achieves high performance partly through UniqueString interning done at parse time.
//! This module brings the same approach to TLA2:
//!
//! - Parser calls `intern()` when creating identifiers
//! - AST stores `NameId(u32)` instead of `String`
//! - Eval compares NameIds with integer equality
//!
//! # Thread Safety
//!
//! The global interner uses `parking_lot::RwLock` for thread-safe access.
//! Interning is write-locked (rare, at parse time) and resolution is read-locked
//! (common, at eval time). Parse is single-threaded, so contention is minimal.
//!
//! # Part of #188, #232

// Copyright 2026 Dropbox
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use parking_lot::RwLock;
use rustc_hash::FxHashMap;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};

/// Unique identifier for an interned name.
///
/// This is a simple u32 index into the global name table.
/// Comparison is O(1) integer equality.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct NameId(pub u32);

impl NameId {
    /// The invalid/unset NameId (0xFFFFFFFF)
    pub const INVALID: NameId = NameId(u32::MAX);

    /// Check if this NameId is valid (not INVALID)
    #[cfg(test)]
    pub(crate) fn is_valid(&self) -> bool {
        *self != Self::INVALID
    }
}

/// Global name interner.
///
/// Maps strings to unique u32 indices and vice versa.
/// Thread-safe via RwLock.
pub(crate) struct NameInterner {
    /// Names in insertion order (id -> string)
    names: Vec<Arc<str>>,
    /// Precomputed standalone FP64 fingerprints for each interned name.
    ///
    /// `string_fp64[id]` matches the fingerprint of `Value::String(name)`.
    string_fp64: Vec<u64>,
    /// Lookup by string (string -> id).
    /// Part of #3063: Uses FxHashMap instead of HashMap (SipHash) for faster
    /// lookups on short identifier strings. Field names are trusted input
    /// (from parser), so HashDoS resistance from SipHash is unnecessary.
    lookup: FxHashMap<Arc<str>, NameId>,
}

impl NameInterner {
    /// Create a new empty interner.
    pub(crate) fn new() -> Self {
        Self {
            names: Vec::new(),
            string_fp64: Vec::new(),
            lookup: FxHashMap::default(),
        }
    }

    /// Intern a name, returning its NameId.
    ///
    /// If the name was already interned, returns the existing ID.
    /// Otherwise, assigns a new ID and stores the name.
    pub(crate) fn intern(&mut self, name: &str) -> NameId {
        // Fast path: already interned
        if let Some(&id) = self.lookup.get(name) {
            return id;
        }

        // Slow path: add new entry
        let id = NameId(self.names.len() as u32);
        let name_fp64 = standalone_string_fp64(name);
        let name: Arc<str> = Arc::from(name);
        self.names.push(name.clone());
        self.string_fp64.push(name_fp64);
        self.lookup.insert(name, id);
        id
    }

    /// Get the string for a NameId.
    ///
    /// # Panics
    ///
    /// Panics if the NameId is invalid or out of range.
    #[cfg(test)]
    pub(crate) fn resolve(&self, id: NameId) -> &str {
        &self.names[id.0 as usize]
    }

    /// Get the number of interned names.
    pub(crate) fn len(&self) -> usize {
        self.names.len()
    }

    /// Clear all interned names.
    ///
    /// WARNING: This invalidates all existing NameIds!
    /// Only use for testing or when completely resetting state.
    pub(crate) fn clear(&mut self) {
        self.names.clear();
        self.string_fp64.clear();
        self.lookup.clear();
    }
}

impl Default for NameInterner {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Global Interner
// ============================================================================

/// Access the global name interner.
///
/// All parsing uses this single interner, ensuring consistent NameIds
/// across all modules within a checking session.
fn global_interner() -> &'static RwLock<NameInterner> {
    static INTERNER: OnceLock<RwLock<NameInterner>> = OnceLock::new();
    INTERNER.get_or_init(|| RwLock::new(NameInterner::new()))
}

// ============================================================================
// Frozen Interner (Part of #2955: lock-free BFS lookup)
// ============================================================================
//
// After parsing/compilation, `freeze_interner()` snapshots the lookup table
// into an immutable HashMap accessible via a single atomic pointer load.
// During BFS, `intern_name()` checks this frozen snapshot first (no lock),
// falling back to the RwLock path only for names not in the snapshot.
// Since ~100% of names are interned at parse time, BFS runs lock-free.

/// Frozen snapshot of the interner for lock-free read access during BFS.
/// Part of #3063: Uses FxHashMap for faster lookups (no SipHash overhead).
struct FrozenInterner {
    lookup: FxHashMap<Arc<str>, NameId>,
    names: Vec<Arc<str>>,
    string_fp64: Vec<u64>,
}

// SAFETY: FrozenInterner is only written by freeze_interner() (single-threaded,
// between BFS runs) and read immutably during BFS via atomic pointer load.
unsafe impl Send for FrozenInterner {}
unsafe impl Sync for FrozenInterner {}

/// Atomic pointer to the frozen interner snapshot. null when not frozen.
static FROZEN: AtomicPtr<FrozenInterner> = AtomicPtr::new(std::ptr::null_mut());
/// Number of threads currently using the raw frozen pointer.
///
/// `freeze_interner()` and `unfreeze_interner()` wait for this count to drain
/// before dropping an old snapshot. That preserves the lock-free read path while
/// preventing use-after-free when multiple model-checking runs freeze the global
/// interner concurrently.
static FROZEN_READERS: AtomicUsize = AtomicUsize::new(0);

struct FrozenReadGuard;

impl FrozenReadGuard {
    #[inline]
    fn enter() -> Self {
        FROZEN_READERS.fetch_add(1, Ordering::AcqRel);
        Self
    }
}

impl Drop for FrozenReadGuard {
    #[inline]
    fn drop(&mut self) {
        FROZEN_READERS.fetch_sub(1, Ordering::AcqRel);
    }
}

fn drop_frozen_after_readers_drain(ptr: *mut FrozenInterner) {
    if ptr.is_null() {
        return;
    }
    while FROZEN_READERS.load(Ordering::Acquire) != 0 {
        std::thread::yield_now();
    }
    // SAFETY: `ptr` was created by Box::into_raw in freeze_interner(). The
    // atomic swap removed it from publication, and the reader count reached
    // zero after the swap, so no lock-free reader can still hold this pointer.
    unsafe {
        drop(Box::from_raw(ptr));
    }
}

// Duplicate the minimal TLC FP64 string extension logic here so tla-core can
// precompute standalone name fingerprints without depending on tla-value.
const FP64_INIT: u64 = 0x911498AE0E66BAD6;
const STRINGVALUE: i64 = 3;
const FP64_ONE: u64 = 0x8000000000000000;
const FP64_X63: u64 = 0x1;
static FP64_BYTE_MOD_TABLE: [u64; 256] = compute_fp64_byte_mod_table(FP64_INIT);

const fn compute_fp64_byte_mod_table(irred_poly: u64) -> [u64; 256] {
    const PLENGTH: usize = 72;
    let mut power_table = [0u64; PLENGTH];
    let mut t = FP64_ONE;
    let mut i = 0;
    while i < PLENGTH {
        power_table[i] = t;
        let mask = if (t & FP64_X63) != 0 { irred_poly } else { 0 };
        t = (t >> 1) ^ mask;
        i += 1;
    }

    let mut table = [0u64; 256];
    let mut j = 0;
    while j < 256 {
        let mut v = 0u64;
        let mut k = 0;
        while k <= 7 {
            if (j & (1usize << k)) != 0 {
                v ^= power_table[127 - 7 * 8 - k];
            }
            k += 1;
        }
        table[j] = v;
        j += 1;
    }
    table
}

#[inline]
fn fp64_extend_byte(fp: u64, b: u8) -> u64 {
    let idx = ((b as u64) ^ fp) as usize & 0xFF;
    (fp >> 8) ^ FP64_BYTE_MOD_TABLE[idx]
}

#[inline]
fn fp64_extend_i32(mut fp: u64, x: i32) -> u64 {
    for &b in &x.to_le_bytes() {
        fp = fp64_extend_byte(fp, b);
    }
    fp
}

#[inline]
fn fp64_extend_i64(mut fp: u64, x: i64) -> u64 {
    for &b in &x.to_le_bytes() {
        fp = fp64_extend_byte(fp, b);
    }
    fp
}

#[inline]
fn fp64_extend_str(mut fp: u64, s: &str) -> u64 {
    for c in s.encode_utf16() {
        fp = fp64_extend_byte(fp, (c & 0xFF) as u8);
    }
    fp
}

#[inline]
fn standalone_string_fp64(name: &str) -> u64 {
    let fp = fp64_extend_i64(FP64_INIT, STRINGVALUE);
    let fp = fp64_extend_i32(fp, name.len() as i32);
    fp64_extend_str(fp, name)
}

/// Freeze the current interner state for lock-free lookup during BFS.
///
/// Call after parsing/compilation is complete and before BFS workers are
/// spawned. This snapshots the current lookup table so that `intern_name()`
/// and `lookup_name_id()` can bypass the RwLock entirely.
///
/// Safe to call multiple times (replaces the previous snapshot).
/// Part of #2955: eliminates RwLock contention that caused 30x CPU overhead
/// at 16 workers.
pub fn freeze_interner() {
    let guard = global_interner().read();
    let frozen = Box::new(FrozenInterner {
        lookup: guard.lookup.clone(),
        names: guard.names.clone(),
        string_fp64: guard.string_fp64.clone(),
    });
    let old = FROZEN.swap(Box::into_raw(frozen), Ordering::AcqRel);
    drop_frozen_after_readers_drain(old);
}

/// Remove the frozen interner snapshot.
///
/// Called by `clear_global_name_interner()` to ensure stale frozen data
/// doesn't outlive a test's interner reset.
fn unfreeze_interner() {
    let old = FROZEN.swap(std::ptr::null_mut(), Ordering::AcqRel);
    drop_frozen_after_readers_drain(old);
}

/// Intern a name in the global interner.
///
/// This is the main entry point for interning variable names.
///
/// # Thread Safety
///
/// When the interner is frozen (after `freeze_interner()`), lookups are
/// lock-free via an atomic pointer load + HashMap lookup. Falls back to
/// the RwLock path for names not in the frozen snapshot or when not frozen.
///
/// Part of #2955: Frozen path eliminates RwLock contention during BFS.
#[inline]
pub fn intern_name(name: &str) -> NameId {
    // Fast path: frozen snapshot (no lock, just atomic pointer load)
    {
        let _frozen_read = FrozenReadGuard::enter();
        let frozen_ptr = FROZEN.load(Ordering::Acquire);
        if !frozen_ptr.is_null() {
            // SAFETY: frozen_ptr was created by Box::into_raw in
            // freeze_interner(). The reader guard prevents old snapshots from
            // being dropped while this thread can still access the raw pointer.
            if let Some(&id) = unsafe { &*frozen_ptr }.lookup.get(name) {
                return id;
            }
        }
    }
    // Medium path: read lock for already-interned names
    if let Some(&id) = global_interner().read().lookup.get(name) {
        return id;
    }
    // Slow path: write lock for new names (has internal re-check for races)
    global_interner().write().intern(name)
}

/// Look up a name's NameId without interning.
///
/// Returns `None` if the name hasn't been interned yet.
/// Lock-free when interner is frozen; falls back to read lock otherwise.
///
/// Part of #188, #2955.
#[inline]
pub fn lookup_name_id(name: &str) -> Option<NameId> {
    // Fast path: frozen snapshot
    {
        let _frozen_read = FrozenReadGuard::enter();
        let frozen_ptr = FROZEN.load(Ordering::Acquire);
        if !frozen_ptr.is_null() {
            // SAFETY: same as intern_name frozen path
            if let Some(&id) = unsafe { &*frozen_ptr }.lookup.get(name) {
                return Some(id);
            }
        }
    }
    global_interner().read().lookup.get(name).copied()
}

/// Resolve a NameId back to its Arc<str> name string.
///
/// Lock-free when interner is frozen; falls back to read lock otherwise.
///
/// Part of #2955: Used by BindingChain to carry name strings for captured_env
/// materialization.
///
/// # Panics
///
/// Panics if the NameId is out of range (was not produced by this interner).
#[inline]
pub fn resolve_name_id(id: NameId) -> Arc<str> {
    // Fast path: frozen snapshot
    {
        let _frozen_read = FrozenReadGuard::enter();
        let frozen_ptr = FROZEN.load(Ordering::Acquire);
        if !frozen_ptr.is_null() {
            // SAFETY: same as intern_name frozen path
            let frozen = unsafe { &*frozen_ptr };
            if (id.0 as usize) < frozen.names.len() {
                return Arc::clone(&frozen.names[id.0 as usize]);
            }
        }
    }
    let guard = global_interner().read();
    Arc::clone(&guard.names[id.0 as usize])
}

/// Resolve a NameId to its cached standalone string FP64 fingerprint.
///
/// This returns the same scalar as fingerprinting `Value::String(name)` without
/// cloning the shared `Arc<str>` or recomputing the FP64 bytes on the hot path.
///
/// Lock-free when the interner is frozen; falls back to a read lock otherwise.
///
/// # Panics
///
/// Panics if the NameId is out of range (was not produced by this interner).
#[inline]
pub fn resolve_name_id_string_fp64(id: NameId) -> u64 {
    {
        let _frozen_read = FrozenReadGuard::enter();
        let frozen_ptr = FROZEN.load(Ordering::Acquire);
        if !frozen_ptr.is_null() {
            // SAFETY: same as resolve_name_id frozen path
            let frozen = unsafe { &*frozen_ptr };
            if (id.0 as usize) < frozen.string_fp64.len() {
                return frozen.string_fp64[id.0 as usize];
            }
        }
    }
    let guard = global_interner().read();
    guard.string_fp64[id.0 as usize]
}

/// Clear the global name interner.
///
/// WARNING: This invalidates all existing NameIds!
/// Only use for testing or when completely resetting state.
///
/// Note: Named `clear_global_name_interner` to distinguish from
/// `tla_check::clear_global_value_interner()` which clears value handles.
pub fn clear_global_name_interner() {
    unfreeze_interner();
    global_interner().write().clear();
}

/// Get the number of interned names.
pub fn interned_name_count() -> usize {
    global_interner().read().len()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_name_interner_basic() {
        let mut interner = NameInterner::new();

        let id1 = interner.intern("foo");
        let id2 = interner.intern("bar");
        let id3 = interner.intern("foo"); // Same as id1

        assert_eq!(id1, id3);
        assert_ne!(id1, id2);
        assert_eq!(interner.resolve(id1), "foo");
        assert_eq!(interner.resolve(id2), "bar");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_name_interner_sequential_ids() {
        let mut interner = NameInterner::new();

        let id1 = interner.intern("a");
        let id2 = interner.intern("b");
        let id3 = interner.intern("c");

        assert_eq!(id1.0, 0);
        assert_eq!(id2.0, 1);
        assert_eq!(id3.0, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_name_id_invalid() {
        assert!(!NameId::INVALID.is_valid());
        assert!(NameId(0).is_valid());
        assert!(NameId(100).is_valid());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_global_interner() {
        // Clear any previous state
        clear_global_name_interner();

        let id1 = intern_name("global_test");
        let id2 = intern_name("global_test");

        assert_eq!(id1, id2);

        {
            let guard = global_interner().read();
            assert_eq!(guard.resolve(id1), "global_test");
        } // read lock dropped before write lock needed below

        // Clean up
        clear_global_name_interner();
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_name_id_string_fp64_matches_standalone_before_and_after_freeze() {
        clear_global_name_interner();

        let names = ["alpha", "beta_123", "RecordField"];
        let ids: Vec<_> = names.iter().map(|name| intern_name(name)).collect();

        for (name, id) in names.iter().zip(ids.iter().copied()) {
            assert_eq!(
                resolve_name_id_string_fp64(id),
                standalone_string_fp64(name)
            );
        }

        freeze_interner();

        for (name, id) in names.iter().zip(ids.iter().copied()) {
            assert_eq!(
                resolve_name_id_string_fp64(id),
                standalone_string_fp64(name)
            );
        }

        clear_global_name_interner();
    }
}
