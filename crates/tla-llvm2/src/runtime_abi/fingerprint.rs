// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! xxh3-based fingerprint functions for flat i64 state buffers.
//!
//! These functions compute SIMD-accelerated xxh3 hashes of flat state buffers
//! for BFS deduplication. They are `extern "C"` so JIT-compiled code can call
//! them directly via symbol registration.
//!
//! Extracted from `tla-jit::bfs_step` — Part of #4199.

// ============================================================================
// Canonical compiled-fingerprint extern — shared with tla-check.
// ============================================================================
//
// `tla2_compiled_fp_u64` is defined with `#[no_mangle]` in
// `crates/tla-check/src/check/model_checker/invariants/eval.rs` as the single
// canonical entry point for compiled-path state fingerprinting (Phase 1 of
// #4319). That definition routes through
// `fingerprint_flat_xxh3_u64_with_seed(state, FLAT_COMPILED_DOMAIN_SEED)`,
// which is the exact same function the Rust-side BFS driver uses via
// `fingerprint_flat_compiled`. Because `tla-check` is part of every final
// binary that links `tla-llvm2`, we can reference the symbol here via an
// `extern "C"` declaration and hand its address to the LLVM2 JIT's extern
// symbol map (see `compile::register_fp_symbols`). The emitted IR in
// `compiled_fingerprint::emit_fingerprint_64_ir` calls this symbol so that
// JIT-compiled actions hash flat buffers through the same xxh3 + seed
// pipeline as the interpreter-side compiled path — single symbol, single
// hash family, single seed.
//
// # Test-only fallback (under `#[cfg(test)]`)
//
// `cargo test -p tla-llvm2` builds integration tests that do **not** link
// `tla-check`, so the `tla2_compiled_fp_u64` symbol would otherwise be
// undefined at link time. Under `#[cfg(test)]` we therefore define a
// byte-equivalent `#[no_mangle]` fallback *with the same name* so the
// `extern "C"` reference resolves. Release/production builds set `cfg(test)
// == false`, the fallback is NOT compiled, and the `#[no_mangle]` symbol
// comes exclusively from tla-check — no duplicate-symbol linker error.
//
// The fallback pins the same seed value as tla-check
// (`FLAT_COMPILED_DOMAIN_SEED = 0xD1CE4E5B9F4A7C15`). Any drift between the
// two would be a soundness bug, caught by the byte-level parity tests in
// `tla-llvm2/src/compiled_fingerprint.rs` and in tla-check's
// `canonical_extern_tests`.
//
// Part of #4319 Phase 2.
#[cfg(not(test))]
extern "C" {
    /// Canonical compiled-fingerprint extern. See the module comment above.
    ///
    /// # Safety
    /// `buf` must point to `len` initialised bytes. Passing `(null, 0)` is
    /// allowed — the empty-buffer fingerprint is computed from a zero-length
    /// slice. `len` need not be a multiple of 8; trailing bytes that do not
    /// form a full `i64` slot are still hashed.
    pub fn tla2_compiled_fp_u64(buf: *const u8, len: usize) -> u64;
}

/// Test-only fallback definition of `tla2_compiled_fp_u64`.
///
/// Only compiled under `#[cfg(test)]`. The real production definition lives
/// in `tla-check` and is what the final `tla2` binary links. This fallback
/// exists solely so that `cargo test -p tla-llvm2` can link integration
/// tests without pulling in the entire `tla-check` crate.
///
/// Byte-identical to the production definition by construction: same seed
/// (`0xD1CE4E5B9F4A7C15`), same `xxh3_64_with_seed(buf, seed)` call.
///
/// # Safety
/// `buf` must point to `len` initialised bytes.
#[cfg(test)]
#[no_mangle]
pub unsafe extern "C" fn tla2_compiled_fp_u64(buf: *const u8, len: usize) -> u64 {
    // Mirror of `FLAT_COMPILED_DOMAIN_SEED` from tla-check; must match
    // `crates/tla-check/src/state/flat_fingerprint.rs:FLAT_COMPILED_DOMAIN_SEED`.
    const FLAT_COMPILED_DOMAIN_SEED_MIRROR: u64 = 0xD1CE4E5B9F4A7C15;
    // SAFETY: caller guarantees the buffer is valid for `len` bytes.
    let bytes = if len == 0 {
        &[][..]
    } else {
        unsafe { std::slice::from_raw_parts(buf, len) }
    };
    xxhash_rust::xxh3::xxh3_64_with_seed(bytes, FLAT_COMPILED_DOMAIN_SEED_MIRROR)
}

/// xxh3-based 64-bit fingerprint of a flat i64 state buffer.
///
/// Reinterprets the i64 state array as a byte slice and computes xxh3_64.
/// The result is used as a deduplication key in the fingerprint set.
///
/// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
#[no_mangle]
pub extern "C" fn jit_xxh3_fingerprint_64(state_ptr: *const i64, state_len: u32) -> u64 {
    let len = state_len as usize;
    if len == 0 {
        return xxhash_rust::xxh3::xxh3_64(&[]);
    }
    // SAFETY: The caller (JIT-compiled code) guarantees that state_ptr points
    // to a valid i64 array of `state_len` elements. The byte reinterpretation
    // is safe because u8 has alignment 1.
    let bytes = unsafe {
        std::slice::from_raw_parts(state_ptr.cast::<u8>(), len * std::mem::size_of::<i64>())
    };
    xxhash_rust::xxh3::xxh3_64(bytes)
}

/// xxh3-based 128-bit fingerprint of a flat i64 state buffer.
///
/// Returns the 128-bit fingerprint as two u64 values via out-parameters
/// (low 64 bits and high 64 bits), since extern "C" cannot return u128.
///
/// Part of #3987.
#[no_mangle]
pub extern "C" fn jit_xxh3_fingerprint_128(
    state_ptr: *const i64,
    state_len: u32,
    out_lo: *mut u64,
    out_hi: *mut u64,
) {
    let len = state_len as usize;
    let fp = if len == 0 {
        xxhash_rust::xxh3::xxh3_128(&[])
    } else {
        // SAFETY: same as jit_xxh3_fingerprint_64.
        let bytes = unsafe {
            std::slice::from_raw_parts(state_ptr.cast::<u8>(), len * std::mem::size_of::<i64>())
        };
        xxhash_rust::xxh3::xxh3_128(bytes)
    };
    // SAFETY: caller provides valid out-parameter pointers.
    unsafe {
        *out_lo = fp as u64;
        *out_hi = (fp >> 64) as u64;
    }
}

/// Batch-fingerprint N states from a contiguous arena.
///
/// Reads `state_count` states of `state_len` i64 slots each from `arena_ptr`,
/// writes `state_count` u64 fingerprints to `out_fps`.
///
/// Part of #3987.
#[no_mangle]
pub extern "C" fn jit_xxh3_batch_fingerprint_64(
    arena_ptr: *const i64,
    state_len: u32,
    state_count: u32,
    out_fps: *mut u64,
) {
    let len = state_len as usize;
    let count = state_count as usize;
    if count == 0 {
        return;
    }

    if len == 0 {
        let fp = xxhash_rust::xxh3::xxh3_64(&[]);
        for state_idx in 0..count {
            // SAFETY: The caller guarantees `out_fps` points to writable storage
            // for `state_count` u64 values.
            unsafe {
                *out_fps.add(state_idx) = fp;
            }
        }
        return;
    }

    let state_bytes_len = len * std::mem::size_of::<i64>();
    for state_idx in 0..count {
        // SAFETY: The caller guarantees `arena_ptr` points to a contiguous arena
        // containing `state_count * state_len` i64 slots and `out_fps` points to
        // `state_count` writable u64 values.
        unsafe {
            let state_ptr = arena_ptr.add(state_idx * len);
            let bytes = std::slice::from_raw_parts(state_ptr.cast::<u8>(), state_bytes_len);
            *out_fps.add(state_idx) = xxhash_rust::xxh3::xxh3_64(bytes);
        }
    }
}

/// Batch-fingerprint N states to 128-bit fingerprints.
///
/// Reads `state_count` states of `state_len` i64 slots each from `arena_ptr`,
/// writes `[lo0, hi0, lo1, hi1, ...]` pairs to `out_fps`.
///
/// Part of #3987.
#[no_mangle]
pub extern "C" fn jit_xxh3_batch_fingerprint_128(
    arena_ptr: *const i64,
    state_len: u32,
    state_count: u32,
    out_fps: *mut u64,
) {
    let len = state_len as usize;
    let count = state_count as usize;
    if count == 0 {
        return;
    }

    if len == 0 {
        let fp = xxhash_rust::xxh3::xxh3_128(&[]);
        let lo = fp as u64;
        let hi = (fp >> 64) as u64;
        for state_idx in 0..count {
            let out_idx = state_idx * 2;
            // SAFETY: The caller guarantees `out_fps` points to writable storage
            // for `state_count * 2` u64 values.
            unsafe {
                *out_fps.add(out_idx) = lo;
                *out_fps.add(out_idx + 1) = hi;
            }
        }
        return;
    }

    let state_bytes_len = len * std::mem::size_of::<i64>();
    for state_idx in 0..count {
        let out_idx = state_idx * 2;
        // SAFETY: The caller guarantees `arena_ptr` points to a contiguous arena
        // containing `state_count * state_len` i64 slots and `out_fps` points to
        // `state_count * 2` writable u64 values.
        unsafe {
            let state_ptr = arena_ptr.add(state_idx * len);
            let bytes = std::slice::from_raw_parts(state_ptr.cast::<u8>(), state_bytes_len);
            let fp = xxhash_rust::xxh3::xxh3_128(bytes);
            *out_fps.add(out_idx) = fp as u64;
            *out_fps.add(out_idx + 1) = (fp >> 64) as u64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_64_deterministic() {
        let buf = [1i64, 2, 3, 4, 5];
        let fp1 = jit_xxh3_fingerprint_64(buf.as_ptr(), 5);
        let fp2 = jit_xxh3_fingerprint_64(buf.as_ptr(), 5);
        assert_eq!(fp1, fp2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_64_different_inputs() {
        let buf_a = [1i64, 2, 3];
        let buf_b = [1i64, 2, 4];
        let fp_a = jit_xxh3_fingerprint_64(buf_a.as_ptr(), 3);
        let fp_b = jit_xxh3_fingerprint_64(buf_b.as_ptr(), 3);
        assert_ne!(fp_a, fp_b);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_64_empty() {
        let fp = jit_xxh3_fingerprint_64(std::ptr::null(), 0);
        assert_ne!(fp, 0); // xxh3 of empty is a specific non-zero value
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_128_outputs() {
        let buf = [10i64, 20, 30];
        let mut lo = 0u64;
        let mut hi = 0u64;
        jit_xxh3_fingerprint_128(buf.as_ptr(), 3, &mut lo, &mut hi);
        assert!(lo != 0 || hi != 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fingerprint_64() {
        let arena = [1i64, 2, 3, 4, 5, 6]; // 2 states of 3 slots each
        let mut fps = [0u64; 2];
        jit_xxh3_batch_fingerprint_64(arena.as_ptr(), 3, 2, fps.as_mut_ptr());
        assert_ne!(fps[0], fps[1]); // different states, different fps
    }
}
