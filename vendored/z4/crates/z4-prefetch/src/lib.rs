// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Platform-specific software prefetch hints.
//!
//! Provides a single function [`prefetch_read_l2`] that issues a non-blocking
//! L2 cache prefetch hint for a memory address. Used by z4-sat's BCP loop
//! to hide main-memory latency (~60-80 cycles) when scanning watch lists.
//!
//! This crate exists to isolate the `unsafe` inline assembly required for
//! prefetch hints, allowing z4-sat to maintain `#![forbid(unsafe_code)]`.
//!
//! # Platform support
//!
//! - **aarch64**: `prfm pldl2keep, [addr]` (prefetch for read, L2, keep)
//! - **x86_64**: `prefetcht1 [addr]` (prefetch to L2 cache)
//! - **Other**: no-op (hardware prefetchers handle it)
//!
//! # Safety
//!
//! Software prefetch is always safe: the CPU treats it as a performance hint.
//! Invalid addresses are silently ignored (no fault, no UB). The `unsafe`
//! block is required only because inline assembly is syntactically `unsafe`
//! in Rust, not because the operation has any safety preconditions.
//!
//! Reference: CaDiCaL propagate.cpp:160-166 (`__builtin_prefetch`).

/// Issue a non-blocking L2 cache prefetch hint for the given address.
///
/// This is a performance hint only — it has no semantic effect. The CPU
/// will attempt to bring the cache line containing `ptr` into L2 cache.
/// If `ptr` is null or invalid, the hint is silently ignored.
#[inline(always)]
pub fn prefetch_read_l2<T>(ptr: *const T) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: PRFM is a hint instruction that never faults.
        // Invalid addresses are silently ignored by the CPU.
        // Reference: ARM Architecture Reference Manual, PRFM instruction.
        unsafe {
            core::arch::asm!(
                "prfm pldl2keep, [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: PREFETCHT1 is a hint instruction that never faults.
        // Invalid addresses are silently ignored by the CPU.
        // Reference: Intel SDM, PREFETCH instruction.
        unsafe {
            core::arch::asm!(
                "prefetcht1 [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    // On unsupported platforms, let hardware prefetchers handle it.
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = ptr;
    }
}

/// Unchecked slice index for `i8` arrays (val lookup in BCP hot path).
///
/// In debug builds, performs a normal bounds-checked access (panics on OOB).
/// In release builds, uses `get_unchecked` to skip the bounds check.
///
/// This eliminates one `cmp + jae` (comparison + conditional branch to panic)
/// per val lookup in the BCP inner loop. CaDiCaL uses `signed char *vals`
/// (raw pointer, no bounds check). Z4 uses `Vec<i8>` which has bounds
/// checking on every index. On benchmarks with millions of val lookups per
/// second, the cumulative branch predictor pressure and decode-slot cost is
/// measurable.
///
/// # Safety contract
///
/// The caller must ensure `index < slice.len()`. In debug builds this is
/// enforced by a panic. In release builds, violating this is UB.
///
/// The function is safe to call because z4-sat's invariant guarantees that
/// every `Literal::index()` is `< 2 * num_vars == vals.len()`. This is
/// established at construction and maintained across all assignment operations.
#[inline(always)]
pub fn val_at(vals: &[i8], index: usize) -> i8 {
    debug_assert!(
        index < vals.len(),
        "val_at: index {index} out of bounds for vals of length {}",
        vals.len()
    );
    #[cfg(debug_assertions)]
    {
        vals[index]
    }
    #[cfg(not(debug_assertions))]
    {
        // SAFETY: caller ensures index < vals.len(). In z4-sat, every
        // Literal::index() is < 2*num_vars == vals.len() by construction.
        unsafe { *vals.get_unchecked(index) }
    }
}

/// Unchecked slice index for `u32` arrays (arena word lookup in BCP hot path).
///
/// Same safety contract as [`val_at`] but for `u32` slices. Used for arena
/// literal access during the BCP replacement scan where the clause offset +
/// literal index is known to be within the arena's allocated words.
#[inline(always)]
pub fn word_at(words: &[u32], index: usize) -> u32 {
    debug_assert!(
        index < words.len(),
        "word_at: index {index} out of bounds for words of length {}",
        words.len()
    );
    #[cfg(debug_assertions)]
    {
        words[index]
    }
    #[cfg(not(debug_assertions))]
    {
        // SAFETY: caller ensures index < words.len(). In z4-sat, arena offsets
        // are validated at clause creation and never exceed words.len().
        unsafe { *words.get_unchecked(index) }
    }
}

/// Unchecked slice read for `u64` arrays (watch entry load in BCP hot path).
///
/// Same safety contract as [`val_at`] but for `u64` slices. Used in the BCP
/// blocker fast path to read packed watch entries without bounds checks.
/// Eliminates the `cmp + b.hs` bounds check branch that prevents LLVM from
/// hoisting the slice data pointer into a register (#3758).
#[inline(always)]
pub fn entry_at(entries: &[u64], index: usize) -> u64 {
    debug_assert!(
        index < entries.len(),
        "entry_at: index {index} out of bounds for entries of length {}",
        entries.len()
    );
    #[cfg(debug_assertions)]
    {
        entries[index]
    }
    #[cfg(not(debug_assertions))]
    {
        // SAFETY: caller ensures index < entries.len(). In the BCP fast path,
        // the loop condition `i < watch_len` where `watch_len = entries.len()`
        // guarantees in-bounds access for reads. The compaction invariant
        // `j <= i` guarantees in-bounds access for writes.
        unsafe { *entries.get_unchecked(index) }
    }
}

/// Unchecked mutable slice write for `u64` arrays (watch entry store in BCP).
///
/// Same safety contract as [`val_set`] but for `u64` slices. Used in the BCP
/// blocker fast path for the speculative copy `entries[j] = entries[i]`.
/// The compaction invariant `j <= i < entries.len()` guarantees safety.
/// Eliminates the `cmp + b.hs` bounds check branch that prevents LLVM from
/// hoisting the slice data pointer into a register (#3758).
#[inline(always)]
pub fn entry_set(entries: &mut [u64], index: usize, value: u64) {
    debug_assert!(
        index < entries.len(),
        "entry_set: index {index} out of bounds for entries of length {}",
        entries.len()
    );
    #[cfg(debug_assertions)]
    {
        entries[index] = value;
    }
    #[cfg(not(debug_assertions))]
    {
        // SAFETY: caller ensures index < entries.len(). See entry_at for
        // the invariant proof.
        unsafe {
            *entries.get_unchecked_mut(index) = value;
        }
    }
}

/// Unchecked mutable slice write for `i8` arrays (val store in enqueue).
///
/// Same safety contract as [`val_at`] but for writes. Used in `enqueue()`
/// to set `vals[lit] = 1` and `vals[¬lit] = -1` without bounds checks.
#[inline(always)]
pub fn val_set(vals: &mut [i8], index: usize, value: i8) {
    debug_assert!(
        index < vals.len(),
        "val_set: index {index} out of bounds for vals of length {}",
        vals.len()
    );
    #[cfg(debug_assertions)]
    {
        vals[index] = value;
    }
    #[cfg(not(debug_assertions))]
    {
        // SAFETY: caller ensures index < vals.len().
        unsafe {
            *vals.get_unchecked_mut(index) = value;
        }
    }
}

/// Issue a non-blocking L2 cache prefetch hint for a specific offset
/// within a `u32` slice (clause arena data prefetch).
///
/// Prefetches the cache line containing `slice[offset]`. The CPU will
/// bring in ~16 u32 words (64-byte cache line), covering a typical clause
/// header (5 words) + first 11 literal words.
///
/// Used by the BCP loop to prefetch the next clause's arena data while
/// processing the current clause, hiding main-memory latency (~60-80 cycles).
///
/// If `offset >= slice.len()`, the prefetch hint targets a valid but
/// potentially unmapped address — the CPU silently ignores it (no fault).
///
/// Reference: CaDiCaL propagate.cpp clause data prefetch pattern (#8000).
#[inline(always)]
pub fn prefetch_arena_at(words: &[u32], offset: usize) {
    // SAFETY: prefetch never faults. Even if offset >= words.len(),
    // the resulting address is silently ignored by the CPU.
    // We use get() to stay within safe Rust for the pointer derivation.
    if let Some(word_ref) = words.get(offset) {
        prefetch_read_l2(std::ptr::from_ref::<u32>(word_ref));
    }
}

// --- Raw pointer helpers for unsafe BCP (#7989) ---

/// L1 cache prefetch hint. Closer than L2, used when data will be
/// accessed within ~10 cycles (e.g., watch list entries during active scan).
///
/// Reference: CaDiCaL propagate.cpp:160-166.
#[inline(always)]
pub fn prefetch_read_l1<T>(ptr: *const T) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: PRFM is a hint instruction that never faults.
        unsafe {
            core::arch::asm!(
                "prfm pldl1keep, [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: PREFETCHT0 is a hint instruction that never faults.
        unsafe {
            core::arch::asm!(
                "prefetcht0 [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = ptr;
    }
}

/// Get raw mutable pointer range for in-place watch list iteration.
/// Returns (begin, end) pointers.
/// CaDiCaL pattern: `watch_iterator j = ws.begin(); const_watch_iterator i = j;`
///
/// The returned pointers are valid for the lifetime of the mutable borrow.
#[inline(always)]
pub fn watch_iter_raw(entries: &mut [u64]) -> (*mut u64, *const u64) {
    let len = entries.len();
    let ptr = entries.as_mut_ptr();
    // SAFETY: ptr.add(len) is one-past-end, valid for pointer comparison.
    let end = unsafe { ptr.add(len) as *const u64 };
    (ptr, end)
}

/// Read a literal u32 from the clause arena using raw pointer arithmetic.
/// Equivalent to CaDiCaL's `lits[k]` where `lits = clause->begin()`.
///
/// # Safety
/// Caller must ensure `clause_offset + header_words + lit_index` is within
/// the arena's allocated words.
#[inline(always)]
pub unsafe fn arena_literal_raw(
    words_ptr: *const u32,
    clause_offset: usize,
    header_words: usize,
    lit_index: usize,
) -> u32 {
    *words_ptr.add(clause_offset + header_words + lit_index)
}

/// Read a clause header word via raw pointer.
///
/// # Safety
/// Caller must ensure `clause_offset + word_index` is within the arena.
#[inline(always)]
pub unsafe fn arena_header_word_raw(
    words_ptr: *const u32,
    clause_offset: usize,
    word_index: usize,
) -> u32 {
    *words_ptr.add(clause_offset + word_index)
}

/// Get raw const pointer to vals array for pointer-based val lookup.
/// CaDiCaL pattern: uses `signed char *vals` directly.
#[inline(always)]
pub fn vals_ptr(vals: &[i8]) -> *const i8 {
    vals.as_ptr()
}

/// Read val at index using raw pointer. No bounds check.
///
/// # Safety
/// `index` must be `< vals.len()` where `vals` is the slice that produced `ptr`.
#[inline(always)]
pub unsafe fn val_raw(ptr: *const i8, index: usize) -> i8 {
    *ptr.add(index)
}

/// Set the length of a `Vec<u64>` after in-place compaction.
/// CaDiCaL pattern: `ws.resize(j - ws.begin())`
///
/// # Safety
/// `new_len` must be `<= vec.capacity()`, and all elements `[0..new_len)` must
/// be initialized.
#[inline(always)]
pub unsafe fn vec_set_len(vec: &mut Vec<u64>, new_len: usize) {
    debug_assert!(new_len <= vec.capacity());
    vec.set_len(new_len);
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
