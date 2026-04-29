// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled fingerprint functions for the LLVM2 backend.
//!
//! Provides compiled fingerprint functions that operate directly on flat
//! `i64[]` state buffers, bypassing Value materialization entirely.
//!
//! # Architecture
//!
//! Emits LLVM IR text for a thin wrapper that calls the canonical
//! `tla2_compiled_fp_u64` extern. The byte length of the state buffer is
//! baked as a constant, eliminating per-call parameter setup overhead.
//!
//! ```text
//! compiled_fp64(state_ptr: ptr) -> i64
//!   +-- iconst state_len_bytes  (= state_len * 8)
//!   +-- call tla2_compiled_fp_u64(state_ptr, state_len_bytes) -> i64
//! ```
//!
//! # Canonical extern (#4319 Phase 2)
//!
//! The emitted IR calls `@tla2_compiled_fp_u64(ptr, i64)` — the canonical
//! `#[no_mangle]` compiled-fingerprint symbol defined in
//! `crates/tla-check/src/check/model_checker/invariants/eval.rs` (Phase 1).
//! That symbol hashes through
//! `xxh3_64_with_seed(buf, FLAT_COMPILED_DOMAIN_SEED)`, which is the same
//! function the Rust-side BFS driver uses via `fingerprint_flat_compiled`.
//! Single symbol, single hash family, single seed — this is the soundness
//! property that closes #4319 (mixed compiled/interpreter BFS fingerprints
//! live in one hash domain).
//!
//! Symbol registration lives in `crate::compile::register_fp_symbols`.
//!
//! **Historical note.** Phase 1 scaffolding emitted calls to
//! `@jit_xxh3_fingerprint_64`, which used bare `xxh3_64` (seed 0) — a
//! different hash family from the Rust driver's seeded path. That code
//! path was dead (not yet invoked by BFS), but is retired by Phase 2 to
//! eliminate the latent divergence.
//!
//! # Future work
//!
//! A hot-path optimisation would inline xxh3 as tMIR instructions to avoid
//! the extern call overhead entirely. That is a separate performance issue
//! (#4198 Phase 3), not a soundness concern.
//!
//! Part of #4319 Phase 2 (canonical extern retarget) and #4198 (tMIR
//! lowering for compiled fingerprinting).

use std::fmt::Write;

/// Generate LLVM IR text for a 64-bit fingerprint wrapper function.
///
/// The generated function has signature:
///   `fn <name>(state_ptr: ptr) -> i64`
///
/// It calls the canonical `tla2_compiled_fp_u64(state_ptr, state_len_bytes)`
/// extern with `state_len_bytes = state_len * 8` baked as a constant, then
/// returns the 64-bit hash. See the module-level doc for the soundness
/// rationale for routing through `tla2_compiled_fp_u64` (#4319 Phase 2).
///
/// # Arguments
///
/// * `state_len` - Number of `i64` slots in the state buffer. The emitted IR
///   bakes the byte length (`state_len * 8`) as a constant so the canonical
///   extern receives `(buf: *const u8, len: usize)` in its declared units.
/// * `name` - Function name for the compiled wrapper.
///
/// # Returns
///
/// Complete LLVM IR module text (`.ll` format) ready for compilation.
pub(crate) fn emit_fingerprint_64_ir(state_len: usize, name: &str) -> String {
    let mut ir = String::with_capacity(512);

    // Bake the byte length at IR-emit time. The canonical extern
    // `tla2_compiled_fp_u64(buf: *const u8, len: usize) -> u64` takes the
    // byte length, not the slot count.
    let state_len_bytes = state_len.saturating_mul(core::mem::size_of::<i64>());

    // Module header.
    writeln!(ir, "; ModuleID = '{name}'").unwrap();
    writeln!(ir, "source_filename = \"{name}\"").unwrap();
    writeln!(
        ir,
        "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
    )
    .unwrap();
    writeln!(ir).unwrap();

    // Declare the canonical compiled-fingerprint extern. Part of #4319
    // Phase 2 — retargeted from `@jit_xxh3_fingerprint_64(ptr, i32)` to
    // `@tla2_compiled_fp_u64(ptr, i64)` so the emitted IR and the Rust
    // driver's `fingerprint_flat_compiled` share one symbol and one seed.
    writeln!(ir, "declare i64 @tla2_compiled_fp_u64(ptr, i64)").unwrap();
    writeln!(ir).unwrap();

    // Define the wrapper function.
    writeln!(ir, "define i64 @{name}(ptr %0) {{").unwrap();
    writeln!(ir, "entry:").unwrap();
    writeln!(
        ir,
        "  %1 = call i64 @tla2_compiled_fp_u64(ptr %0, i64 {state_len_bytes})"
    )
    .unwrap();
    writeln!(ir, "  ret i64 %1").unwrap();
    writeln!(ir, "}}").unwrap();

    ir
}

/// Generate LLVM IR text for a 128-bit fingerprint wrapper function.
///
/// The generated function has signature:
///   `fn <name>(state_ptr: ptr, out_lo: ptr, out_hi: ptr)`
///
/// It calls `jit_xxh3_fingerprint_128(state_ptr, state_len, out_lo, out_hi)`
/// with `state_len` baked as a constant.
///
/// # Arguments
///
/// * `state_len` - Number of i64 slots in the state buffer.
/// * `name` - Function name for the compiled wrapper.
pub(crate) fn emit_fingerprint_128_ir(state_len: usize, name: &str) -> String {
    let mut ir = String::with_capacity(512);

    writeln!(ir, "; ModuleID = '{name}'").unwrap();
    writeln!(ir, "source_filename = \"{name}\"").unwrap();
    writeln!(
        ir,
        "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
    )
    .unwrap();
    writeln!(ir).unwrap();

    // Declare the external helper.
    writeln!(
        ir,
        "declare void @jit_xxh3_fingerprint_128(ptr, i32, ptr, ptr)"
    )
    .unwrap();
    writeln!(ir).unwrap();

    // Define the wrapper function.
    writeln!(ir, "define void @{name}(ptr %0, ptr %1, ptr %2) {{").unwrap();
    writeln!(ir, "entry:").unwrap();
    writeln!(
        ir,
        "  call void @jit_xxh3_fingerprint_128(ptr %0, i32 {state_len}, ptr %1, ptr %2)"
    )
    .unwrap();
    writeln!(ir, "  ret void").unwrap();
    writeln!(ir, "}}").unwrap();

    ir
}

/// Generate LLVM IR text for a batch 64-bit fingerprint wrapper function.
///
/// The generated function has signature:
///   `fn <name>(arena_ptr: ptr, state_count: i32, out_fps: ptr)`
///
/// Calls `jit_xxh3_batch_fingerprint_64(arena_ptr, state_len, state_count, out_fps)`
/// with `state_len` baked as a constant.
pub(crate) fn emit_batch_fingerprint_64_ir(state_len: usize, name: &str) -> String {
    let mut ir = String::with_capacity(512);

    writeln!(ir, "; ModuleID = '{name}'").unwrap();
    writeln!(ir, "source_filename = \"{name}\"").unwrap();
    writeln!(
        ir,
        "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
    )
    .unwrap();
    writeln!(ir).unwrap();

    writeln!(
        ir,
        "declare void @jit_xxh3_batch_fingerprint_64(ptr, i32, i32, ptr)"
    )
    .unwrap();
    writeln!(ir).unwrap();

    // Wrapper: (arena_ptr, state_count, out_fps) -> void
    writeln!(ir, "define void @{name}(ptr %0, i32 %1, ptr %2) {{").unwrap();
    writeln!(ir, "entry:").unwrap();
    writeln!(
        ir,
        "  call void @jit_xxh3_batch_fingerprint_64(ptr %0, i32 {state_len}, i32 %1, ptr %2)"
    )
    .unwrap();
    writeln!(ir, "  ret void").unwrap();
    writeln!(ir, "}}").unwrap();

    ir
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // IR emission tests (always available, no feature gate)
    // =========================================================================

    #[test]
    fn test_emit_fingerprint_64_ir_structure() {
        // state_len=5 -> 5 * 8 = 40 bytes baked into IR.
        let ir = emit_fingerprint_64_ir(5, "compiled_fp64");

        // Module header.
        assert!(
            ir.contains("; ModuleID = 'compiled_fp64'"),
            "Should have module ID. IR:\n{ir}"
        );

        // External declaration of the canonical #4319 extern.
        assert!(
            ir.contains("declare i64 @tla2_compiled_fp_u64(ptr, i64)"),
            "Should declare canonical extern. IR:\n{ir}"
        );

        // Legacy symbol must NOT appear — Phase 2 retargets away from it.
        assert!(
            !ir.contains("@jit_xxh3_fingerprint_64"),
            "Legacy `@jit_xxh3_fingerprint_64` must not be emitted (Phase 2 retarget). IR:\n{ir}"
        );

        // Wrapper function definition.
        assert!(
            ir.contains("define i64 @compiled_fp64(ptr %0)"),
            "Should define wrapper with ptr param. IR:\n{ir}"
        );

        // Baked byte-length constant: 5 slots * 8 bytes = 40.
        assert!(
            ir.contains("i64 40"),
            "Should bake state_len_bytes=40 as i64 constant. IR:\n{ir}"
        );

        // Call to canonical extern.
        assert!(
            ir.contains("call i64 @tla2_compiled_fp_u64(ptr %0, i64 40)"),
            "Should call canonical extern with baked byte length. IR:\n{ir}"
        );

        // Return.
        assert!(
            ir.contains("ret i64 %1"),
            "Should return the fingerprint. IR:\n{ir}"
        );
    }

    #[test]
    fn test_emit_fingerprint_128_ir_structure() {
        let ir = emit_fingerprint_128_ir(3, "compiled_fp128");

        assert!(
            ir.contains("declare void @jit_xxh3_fingerprint_128(ptr, i32, ptr, ptr)"),
            "Should declare extern fp128 helper. IR:\n{ir}"
        );

        assert!(
            ir.contains("define void @compiled_fp128(ptr %0, ptr %1, ptr %2)"),
            "Should define fp128 wrapper with 3 ptr params. IR:\n{ir}"
        );

        assert!(
            ir.contains("call void @jit_xxh3_fingerprint_128(ptr %0, i32 3, ptr %1, ptr %2)"),
            "Should call fp128 helper with baked state_len=3. IR:\n{ir}"
        );

        assert!(
            ir.contains("ret void"),
            "fp128 wrapper should return void. IR:\n{ir}"
        );
    }

    #[test]
    fn test_emit_batch_fingerprint_64_ir_structure() {
        let ir = emit_batch_fingerprint_64_ir(7, "compiled_batch_fp64");

        assert!(
            ir.contains("declare void @jit_xxh3_batch_fingerprint_64(ptr, i32, i32, ptr)"),
            "Should declare extern batch helper. IR:\n{ir}"
        );

        assert!(
            ir.contains("define void @compiled_batch_fp64(ptr %0, i32 %1, ptr %2)"),
            "Should define batch wrapper. IR:\n{ir}"
        );

        assert!(
            ir.contains("call void @jit_xxh3_batch_fingerprint_64(ptr %0, i32 7, i32 %1, ptr %2)"),
            "Should call batch helper with baked state_len=7. IR:\n{ir}"
        );
    }

    #[test]
    fn test_emit_fingerprint_64_empty_state() {
        // state_len=0 -> 0 bytes.
        let ir = emit_fingerprint_64_ir(0, "fp64_empty");
        assert!(
            ir.contains("i64 0"),
            "Should bake state_len_bytes=0. IR:\n{ir}"
        );
        assert!(
            ir.contains("call i64 @tla2_compiled_fp_u64(ptr %0, i64 0)"),
            "Should call canonical extern with 0-byte constant. IR:\n{ir}"
        );
    }

    #[test]
    fn test_emit_fingerprint_64_large_state() {
        // state_len=1000 -> 1000 * 8 = 8000 bytes.
        let ir = emit_fingerprint_64_ir(1000, "fp64_large");
        assert!(
            ir.contains("i64 8000"),
            "Should bake state_len_bytes=8000. IR:\n{ir}"
        );
        assert!(
            ir.contains("call i64 @tla2_compiled_fp_u64(ptr %0, i64 8000)"),
            "Should call canonical extern with 8000-byte constant. IR:\n{ir}"
        );
    }

    #[test]
    fn test_emit_fingerprint_64_different_lens_differ() {
        let ir_5 = emit_fingerprint_64_ir(5, "fp64");
        let ir_10 = emit_fingerprint_64_ir(10, "fp64");
        // The only difference is the baked byte-length constant (5*8 vs 10*8).
        assert!(ir_5.contains("i64 40"));
        assert!(ir_10.contains("i64 80"));
        assert_ne!(ir_5, ir_10);
    }

    // =========================================================================
    // Native compilation + execution tests (requires `native` feature)
    // =========================================================================

    #[cfg(feature = "native")]
    mod native_tests {
        use super::*;
        use crate::runtime_abi::fingerprint::{jit_xxh3_fingerprint_128, jit_xxh3_fingerprint_64};

        /// Helper: compile IR text through the LLVM2 native pipeline.
        ///
        /// The `compile_and_link` path is deprecated; instead we test that the
        /// IR text is well-formed and structurally correct. End-to-end native
        /// execution would require piping the IR text into the LLVM2 JIT, which
        /// currently only accepts tMIR modules. Phase 2 will build proper tMIR
        /// modules that compile natively.
        ///
        /// For now, we verify correctness by calling the runtime helpers directly
        /// and confirming the IR structure matches expectations.

        #[test]
        fn test_fingerprint_64_ir_is_well_formed() {
            let ir = emit_fingerprint_64_ir(5, "fp64_native_test");

            // Structural checks that match LLVM IR grammar.
            assert!(ir.contains("define i64 @fp64_native_test(ptr %0) {"));
            assert!(ir.contains("entry:"));
            assert!(ir.contains("ret i64"));
            // Canonical extern (#4319 Phase 2).
            assert!(ir.contains("declare i64 @tla2_compiled_fp_u64(ptr, i64)"));
        }

        #[test]
        fn test_fingerprint_64_runtime_helper_correctness() {
            // Verify the runtime helper itself works correctly.
            // This confirms the function we'd call from compiled code is sound.
            let state = [1i64, 2, 3, 4, 5];
            let fp1 = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
            let fp2 = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
            assert_eq!(fp1, fp2, "fingerprint must be deterministic");
            assert_ne!(fp1, 0, "fingerprint of non-empty data should be non-zero");

            // Different inputs produce different fingerprints.
            let state2 = [1i64, 2, 3, 4, 6];
            let fp3 = jit_xxh3_fingerprint_64(state2.as_ptr(), 5);
            assert_ne!(
                fp1, fp3,
                "different inputs must produce different fingerprints"
            );
        }

        #[test]
        fn test_fingerprint_128_runtime_helper_correctness() {
            let state = [10i64, 20, 30];
            let mut lo1: u64 = 0;
            let mut hi1: u64 = 0;
            let mut lo2: u64 = 0;
            let mut hi2: u64 = 0;
            jit_xxh3_fingerprint_128(state.as_ptr(), 3, &mut lo1, &mut hi1);
            jit_xxh3_fingerprint_128(state.as_ptr(), 3, &mut lo2, &mut hi2);
            assert_eq!(lo1, lo2, "fp128 low must be deterministic");
            assert_eq!(hi1, hi2, "fp128 high must be deterministic");
            assert!(lo1 != 0 || hi1 != 0, "fp128 should be non-zero");
        }

        #[test]
        fn test_fingerprint_64_collision_resistance() {
            // Run the runtime helper on 200 distinct single-slot states
            // and verify no collisions.
            let mut seen = std::collections::HashSet::new();
            for i in 0i64..200 {
                let state = [i];
                let fp = jit_xxh3_fingerprint_64(state.as_ptr(), 1);
                assert!(seen.insert(fp), "collision at i={}: {:#018x}", i, fp,);
            }
            assert_eq!(seen.len(), 200);
        }
    }

    // =========================================================================
    // Canonical extern soundness (#4319 Phase 2)
    // =========================================================================
    //
    // These tests verify that `tla2_compiled_fp_u64` — the symbol the emitted
    // IR now calls — produces byte-identical fingerprints to the Rust driver's
    // `xxh3_64_with_seed(buf, FLAT_COMPILED_DOMAIN_SEED)` path. If this
    // parity ever drifts, mixed compiled/interpreter BFS fingerprints would
    // land in different hash domains and state dedup would silently break —
    // exactly the class of soundness bug #4319 closes.

    /// Must match `FLAT_COMPILED_DOMAIN_SEED` in tla-check's
    /// `crates/tla-check/src/state/flat_fingerprint.rs`.
    const FLAT_COMPILED_DOMAIN_SEED_MIRROR: u64 = 0xD1CE4E5B9F4A7C15;

    #[test]
    fn test_tla2_compiled_fp_u64_matches_seeded_xxh3_empty() {
        use crate::runtime_abi::tla2_compiled_fp_u64;
        // SAFETY: (null, 0) is explicitly documented as allowed.
        let actual = unsafe { tla2_compiled_fp_u64(std::ptr::null(), 0) };
        let expected = xxhash_rust::xxh3::xxh3_64_with_seed(&[], FLAT_COMPILED_DOMAIN_SEED_MIRROR);
        assert_eq!(
            actual, expected,
            "tla2_compiled_fp_u64 must match seeded xxh3 on empty buffer \
             (soundness gate for #4319 mixed BFS fingerprints)"
        );
    }

    #[test]
    fn test_tla2_compiled_fp_u64_matches_seeded_xxh3_various_sizes() {
        use crate::runtime_abi::tla2_compiled_fp_u64;
        // A spread of state-buffer sizes spanning the tail cases xxh3
        // handles differently (<=16, 17-128, 129-240, >240 bytes).
        for state_len in [0, 1, 2, 5, 17, 32, 64, 128, 256, 1000] {
            let state: Vec<i64> = (0..state_len as i64).map(|i| i.wrapping_mul(31)).collect();
            // SAFETY: state is a live Vec for the duration of the call; u8
            // has alignment 1 so reinterpreting [i64] bytes is sound.
            let bytes = unsafe {
                std::slice::from_raw_parts(
                    state.as_ptr().cast::<u8>(),
                    state.len() * std::mem::size_of::<i64>(),
                )
            };
            // SAFETY: bytes points to a valid slice of state.
            let actual = unsafe { tla2_compiled_fp_u64(bytes.as_ptr(), bytes.len()) };
            let expected =
                xxhash_rust::xxh3::xxh3_64_with_seed(bytes, FLAT_COMPILED_DOMAIN_SEED_MIRROR);
            assert_eq!(
                actual, expected,
                "tla2_compiled_fp_u64 diverged from seeded xxh3 at state_len={state_len} \
                 (soundness gate for #4319 mixed BFS fingerprints)"
            );
        }
    }

    #[test]
    fn test_tla2_compiled_fp_u64_does_not_collide_with_bare_xxh3() {
        use crate::runtime_abi::tla2_compiled_fp_u64;
        // Regression guard for the Phase 1 scaffolding bug: the legacy
        // `jit_xxh3_fingerprint_64` used bare `xxh3_64` (seed 0). The
        // canonical extern uses `FLAT_COMPILED_DOMAIN_SEED`. If the two
        // match on a non-trivial buffer, someone has dropped the seed.
        let buf: [i64; 5] = [1, 2, 3, 4, 5];
        // SAFETY: u8 has alignment 1; buf lives through both calls.
        let bytes = unsafe {
            std::slice::from_raw_parts(buf.as_ptr().cast::<u8>(), std::mem::size_of_val(&buf))
        };
        // SAFETY: bytes is a valid slice of buf.
        let seeded = unsafe { tla2_compiled_fp_u64(bytes.as_ptr(), bytes.len()) };
        let bare = xxhash_rust::xxh3::xxh3_64(bytes);
        assert_ne!(
            seeded, bare,
            "tla2_compiled_fp_u64 MUST be domain-separated from bare xxh3_64 \
             (regression: Phase 1 scaffolding called unseeded xxh3 — would \
             collide with interpreter-path seeded fingerprints in #4319)"
        );
    }
}
