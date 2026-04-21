// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compiled fingerprint functions for JIT V2 Phase 4.
//!
//! Provides standalone compiled fingerprint functions that operate directly
//! on flat `i64[]` state buffers, bypassing Value materialization entirely.
//! Two variants:
//!
//! 1. **64-bit** (`CompiledFingerprintFn`): single xxh3_64 call, returns u64.
//!    Used for fingerprint-set dedup in the BFS inner loop.
//! 2. **128-bit** (`CompiledFingerprint128Fn`): single xxh3_128 call, writes
//!    two u64 out-params. Used for soundness at high state counts where
//!    64-bit birthday-bound collisions become likely.
//!
//! The compiled functions delegate to the extern "C" helpers
//! [`crate::bfs_step::jit_xxh3_fingerprint_64`] and
//! [`crate::bfs_step::jit_xxh3_fingerprint_128`] which are already registered
//! as Cranelift symbols. The compilation step generates a thin wrapper that
//! loads the state_len constant and forwards the call, eliminating per-call
//! parameter setup overhead.
//!
//! # Architecture
//!
//! ```text
//! CompiledFingerprintFn(state_ptr) -> u64
//!   +-- iconst state_len
//!   +-- call jit_xxh3_fingerprint_64(state_ptr, state_len) -> u64
//! ```
//!
//! Part of #3987: JIT V2 Phase 4 compiled fingerprinting.

use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use std::collections::HashMap;

/// Compiled 64-bit fingerprint function.
///
/// Takes a pointer to a flat i64 state buffer and returns a 64-bit
/// xxh3 fingerprint. The state length is baked into the compiled code.
///
/// # Safety
///
/// The pointer must point to a valid `[i64; N]` where N is the state_len
/// that was passed to `FingerprintCompiler::compile_64`.
pub type CompiledFingerprintFn = unsafe extern "C" fn(state_ptr: *const i64) -> u64;

/// Compiled 128-bit fingerprint function.
///
/// Takes a pointer to a flat i64 state buffer and two out-parameter
/// pointers for the low and high 64-bit halves of the 128-bit fingerprint.
///
/// # Safety
///
/// `state_ptr` must point to a valid `[i64; N]`. `out_lo` and `out_hi`
/// must point to valid, writable `u64` locations.
pub type CompiledFingerprint128Fn =
    unsafe extern "C" fn(state_ptr: *const i64, out_lo: *mut u64, out_hi: *mut u64);

/// Compiled 64-bit batch fingerprint function.
///
/// Takes a pointer to a contiguous arena of flat states, the number of states,
/// and an output buffer for one u64 fingerprint per state. The state length is
/// baked into the compiled code.
///
/// # Safety
///
/// `arena_ptr` must point to `state_count * state_len` contiguous i64 slots and
/// `out_fps` must point to `state_count` writable u64 values.
pub(crate) type CompiledBatchFingerprintFn =
    unsafe extern "C" fn(arena_ptr: *const i64, state_count: u32, out_fps: *mut u64);

fn validate_batch_arena(arena: &[i64], state_len: usize) -> (u32, u32) {
    assert!(
        state_len != 0,
        "batch_fingerprint_arena_*: state_len must be non-zero for a non-empty arena",
    );
    assert_eq!(
        arena.len() % state_len,
        0,
        "batch_fingerprint_arena_*: arena len {} is not divisible by state_len {}",
        arena.len(),
        state_len,
    );

    let state_len_u32 =
        u32::try_from(state_len).expect("batch_fingerprint_arena_*: state_len exceeds u32::MAX");
    let state_count = arena.len() / state_len;
    let state_count_u32 = u32::try_from(state_count)
        .expect("batch_fingerprint_arena_*: state_count exceeds u32::MAX");
    (state_len_u32, state_count_u32)
}

/// Batch fingerprint a contiguous arena of flat states.
///
/// Takes a raw arena of `state_count * state_len` slots, computes one xxh3_64
/// fingerprint per state, and returns the results in a new Vec.
pub(crate) fn batch_fingerprint_arena_64(arena: &[i64], state_len: usize) -> Vec<u64> {
    if arena.is_empty() {
        return Vec::new();
    }

    let (state_len_u32, state_count_u32) = validate_batch_arena(arena, state_len);
    let mut out = vec![0u64; state_count_u32 as usize];
    crate::bfs_step::jit_xxh3_batch_fingerprint_64(
        arena.as_ptr(),
        state_len_u32,
        state_count_u32,
        out.as_mut_ptr(),
    );
    out
}

/// Batch fingerprint a contiguous arena of flat states to 128-bit fingerprints.
///
/// Takes a raw arena of `state_count * state_len` slots, computes one xxh3_128
/// fingerprint per state, and returns the results in a new Vec.
pub(crate) fn batch_fingerprint_arena_128(arena: &[i64], state_len: usize) -> Vec<u128> {
    if arena.is_empty() {
        return Vec::new();
    }

    let (state_len_u32, state_count_u32) = validate_batch_arena(arena, state_len);
    let mut halves = vec![0u64; state_count_u32 as usize * 2];
    crate::bfs_step::jit_xxh3_batch_fingerprint_128(
        arena.as_ptr(),
        state_len_u32,
        state_count_u32,
        halves.as_mut_ptr(),
    );

    halves
        .chunks_exact(2)
        .map(|pair| ((pair[1] as u128) << 64) | (pair[0] as u128))
        .collect()
}

/// Compiler for standalone fingerprint functions.
///
/// Each call to `compile_64` or `compile_128` generates a Cranelift function
/// with the state length baked in as a constant. The resulting function
/// pointer can be called directly from the BFS hot path.
///
/// Part of #3987.
pub(crate) struct FingerprintCompiler {
    func_counter: u32,
    /// Retains ownership of JIT modules whose code pages back the compiled
    /// function pointers. Previously these were `Box::leak`'d, causing
    /// unbounded memory growth (#4082). Modules are dropped when the
    /// compiler is dropped, freeing the mmap'd code pages.
    _modules: Vec<JITModule>,
}

impl FingerprintCompiler {
    /// Create a new fingerprint compiler.
    pub(crate) fn new() -> Self {
        FingerprintCompiler {
            func_counter: 0,
            _modules: Vec::new(),
        }
    }

    /// Compile a 64-bit fingerprint function for states of `state_len` slots.
    ///
    /// The generated function has signature `fn(*const i64) -> u64` and
    /// calls `jit_xxh3_fingerprint_64(ptr, state_len)` with the length
    /// constant baked in.
    pub(crate) fn compile_64(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledFingerprintFn, JitError> {
        let mut module = crate::create_jit_module()?;
        let ptr_type = module.target_config().pointer_type();

        // Declare the xxh3_64 import: (ptr, u32) -> i64
        let mut xxh3_sig = module.make_signature();
        xxh3_sig.params.push(AbiParam::new(ptr_type));
        xxh3_sig.params.push(AbiParam::new(types::I32));
        xxh3_sig.returns.push(AbiParam::new(types::I64));
        let xxh3_func_id =
            module.declare_function("jit_xxh3_fingerprint_64", Linkage::Import, &xxh3_sig)?;

        // Declare our wrapper function: (ptr) -> i64
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type));
        sig.returns.push(AbiParam::new(types::I64));

        let func_name = format!("compiled_fp64_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = module.declare_function(&func_name, Linkage::Local, &sig)?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let xxh3_ref = module.declare_func_in_func(xxh3_func_id, builder.func);

            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let state_ptr = builder.block_params(entry)[0];
            let len_val = builder.ins().iconst(types::I32, state_len as i64);
            let call = builder.ins().call(xxh3_ref, &[state_ptr, len_val]);
            let result = builder.inst_results(call)[0];
            builder.ins().return_(&[result]);

            builder.finalize();
        }

        module.define_function(func_id, &mut ctx).map_err(|e| {
            module.clear_context(&mut ctx);
            JitError::CompileError(e.to_string())
        })?;

        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize fp64: {e}")))?;

        let code_ptr = module.get_finalized_function(func_id);
        // Retain the module so its mmap'd code pages stay alive.
        // Previously Box::leak'd (#4082) — now owned by the compiler.
        self._modules.push(module);

        // SAFETY: The compiled function has the same calling convention and
        // parameter layout as CompiledFingerprintFn: extern "C" fn(*const i64) -> u64.
        // The module is retained in self._modules so the code pointer remains valid.
        debug_assert!(!code_ptr.is_null(), "compiled fp64 code pointer is null");
        let fp_fn: CompiledFingerprintFn = unsafe { std::mem::transmute(code_ptr) };
        Ok(fp_fn)
    }

    /// Compile a 128-bit fingerprint function for states of `state_len` slots.
    ///
    /// The generated function has signature
    /// `fn(*const i64, *mut u64, *mut u64)` and calls
    /// `jit_xxh3_fingerprint_128(ptr, state_len, out_lo, out_hi)`.
    pub(crate) fn compile_128(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledFingerprint128Fn, JitError> {
        let mut module = crate::create_jit_module()?;
        let ptr_type = module.target_config().pointer_type();

        // Declare the xxh3_128 import: (ptr, u32, ptr, ptr) -> void
        let mut xxh3_sig = module.make_signature();
        xxh3_sig.params.push(AbiParam::new(ptr_type)); // state_ptr
        xxh3_sig.params.push(AbiParam::new(types::I32)); // state_len
        xxh3_sig.params.push(AbiParam::new(ptr_type)); // out_lo
        xxh3_sig.params.push(AbiParam::new(ptr_type)); // out_hi
        let xxh3_func_id =
            module.declare_function("jit_xxh3_fingerprint_128", Linkage::Import, &xxh3_sig)?;

        // Declare our wrapper: (ptr, ptr, ptr) -> void
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // state_ptr
        sig.params.push(AbiParam::new(ptr_type)); // out_lo
        sig.params.push(AbiParam::new(ptr_type)); // out_hi

        let func_name = format!("compiled_fp128_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = module.declare_function(&func_name, Linkage::Local, &sig)?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let xxh3_ref = module.declare_func_in_func(xxh3_func_id, builder.func);

            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let state_ptr = builder.block_params(entry)[0];
            let out_lo = builder.block_params(entry)[1];
            let out_hi = builder.block_params(entry)[2];
            let len_val = builder.ins().iconst(types::I32, state_len as i64);
            builder
                .ins()
                .call(xxh3_ref, &[state_ptr, len_val, out_lo, out_hi]);
            builder.ins().return_(&[]);

            builder.finalize();
        }

        module.define_function(func_id, &mut ctx).map_err(|e| {
            module.clear_context(&mut ctx);
            JitError::CompileError(e.to_string())
        })?;

        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize fp128: {e}")))?;

        let code_ptr = module.get_finalized_function(func_id);
        // Retain the module so its mmap'd code pages stay alive (#4082).
        self._modules.push(module);

        // SAFETY: Same rationale as compile_64 -- calling convention matches,
        // module is retained in self._modules so code remains valid.
        debug_assert!(!code_ptr.is_null(), "compiled fp128 code pointer is null");
        let fp_fn: CompiledFingerprint128Fn = unsafe { std::mem::transmute(code_ptr) };
        Ok(fp_fn)
    }

    /// Compile a batch fingerprint function for states of `state_len` slots.
    ///
    /// The generated function has signature
    /// `fn(*const i64, u32, *mut u64)` and forwards to
    /// `jit_xxh3_batch_fingerprint_64(arena_ptr, state_len, state_count, out_fps)`.
    pub(crate) fn compile_batch_64(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledBatchFingerprintFn, JitError> {
        let baked_state_len = i64::from(u32::try_from(state_len).map_err(|_| {
            JitError::CompileError(format!(
                "batch fingerprint state_len {state_len} exceeds u32::MAX"
            ))
        })?);
        let mut module = crate::create_jit_module()?;
        let ptr_type = module.target_config().pointer_type();

        let mut batch_sig = module.make_signature();
        batch_sig.params.push(AbiParam::new(ptr_type));
        batch_sig.params.push(AbiParam::new(types::I32));
        batch_sig.params.push(AbiParam::new(types::I32));
        batch_sig.params.push(AbiParam::new(ptr_type));
        let batch_func_id = module.declare_function(
            "jit_xxh3_batch_fingerprint_64",
            Linkage::Import,
            &batch_sig,
        )?;

        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type));
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(ptr_type));

        let func_name = format!("compiled_batch_fp64_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = module.declare_function(&func_name, Linkage::Local, &sig)?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
            let batch_ref = module.declare_func_in_func(batch_func_id, builder.func);

            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let arena_ptr = builder.block_params(entry)[0];
            let state_count = builder.block_params(entry)[1];
            let out_fps = builder.block_params(entry)[2];
            let len_val = builder.ins().iconst(types::I32, baked_state_len);
            builder
                .ins()
                .call(batch_ref, &[arena_ptr, len_val, state_count, out_fps]);
            builder.ins().return_(&[]);

            builder.finalize();
        }

        module.define_function(func_id, &mut ctx).map_err(|e| {
            module.clear_context(&mut ctx);
            JitError::CompileError(e.to_string())
        })?;

        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize batch fp64: {e}")))?;

        let code_ptr = module.get_finalized_function(func_id);
        // Retain the module so its mmap'd code pages stay alive (#4082).
        self._modules.push(module);

        // SAFETY: The compiled function has the same calling convention and
        // parameter layout as CompiledBatchFingerprintFn. The module is retained
        // in self._modules so the code pointer remains valid.
        debug_assert!(
            !code_ptr.is_null(),
            "compiled batch fp64 code pointer is null"
        );
        let fp_fn: CompiledBatchFingerprintFn = unsafe { std::mem::transmute(code_ptr) };
        Ok(fp_fn)
    }
}

/// Cache of compiled fingerprint functions keyed by state length.
///
/// Avoids recompiling the same fingerprint function when multiple specs
/// or model checking runs share the same state length. Thread-safe via
/// interior mutability (the compiled function pointers are Send + Sync).
///
/// Part of #3987.
pub(crate) struct CompiledFingerprintSet {
    fp64_cache: HashMap<usize, CompiledFingerprintFn>,
    fp128_cache: HashMap<usize, CompiledFingerprint128Fn>,
    batch64_cache: HashMap<usize, CompiledBatchFingerprintFn>,
    compiler: FingerprintCompiler,
}

impl CompiledFingerprintSet {
    /// Create a new empty fingerprint set.
    pub(crate) fn new() -> Self {
        Self {
            fp64_cache: HashMap::new(),
            fp128_cache: HashMap::new(),
            batch64_cache: HashMap::new(),
            compiler: FingerprintCompiler::new(),
        }
    }

    /// Get or compile a 64-bit fingerprint function for the given state length.
    pub(crate) fn get_or_compile_64(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledFingerprintFn, JitError> {
        if let Some(&fp_fn) = self.fp64_cache.get(&state_len) {
            return Ok(fp_fn);
        }
        let fp_fn = self.compiler.compile_64(state_len)?;
        self.fp64_cache.insert(state_len, fp_fn);
        Ok(fp_fn)
    }

    /// Get or compile a 128-bit fingerprint function for the given state length.
    pub(crate) fn get_or_compile_128(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledFingerprint128Fn, JitError> {
        if let Some(&fp_fn) = self.fp128_cache.get(&state_len) {
            return Ok(fp_fn);
        }
        let fp_fn = self.compiler.compile_128(state_len)?;
        self.fp128_cache.insert(state_len, fp_fn);
        Ok(fp_fn)
    }

    /// Get or compile a batch 64-bit fingerprint function for the given state length.
    ///
    /// Previously, `compile_batch_64` was not wired into the cache, so repeated
    /// calls with the same state_len would create redundant JIT modules (#4082).
    pub(crate) fn get_or_compile_batch_64(
        &mut self,
        state_len: usize,
    ) -> Result<CompiledBatchFingerprintFn, JitError> {
        if let Some(&fp_fn) = self.batch64_cache.get(&state_len) {
            return Ok(fp_fn);
        }
        let fp_fn = self.compiler.compile_batch_64(state_len)?;
        self.batch64_cache.insert(state_len, fp_fn);
        Ok(fp_fn)
    }

    /// Number of cached 64-bit functions.
    #[must_use]
    pub(crate) fn cached_64_count(&self) -> usize {
        self.fp64_cache.len()
    }

    /// Number of cached 128-bit functions.
    #[must_use]
    pub(crate) fn cached_128_count(&self) -> usize {
        self.fp128_cache.len()
    }

    /// Number of cached batch 64-bit functions.
    #[must_use]
    pub(crate) fn cached_batch64_count(&self) -> usize {
        self.batch64_cache.len()
    }
}

/// Emit Cranelift IR for fingerprint computation followed by dedup probe.
///
/// This is a helper for the BFS step compiler that inlines the fingerprint
/// + dedup sequence into a single block of Cranelift IR. The sequence:
///
/// 1. Call `jit_xxh3_fingerprint_64(state_ptr, state_len)` -> fingerprint
/// 2. Call `jit_fp_set_probe(fp_set_ptr, fingerprint)` -> seen (0=new, 1=seen)
/// 3. Branch: if seen, jump to `seen_block`; if new, jump to `new_block`
///
/// Returns the fingerprint Cranelift value (available in both branches).
///
/// Part of #3987.
pub(crate) fn emit_fingerprint_and_dedup(
    builder: &mut FunctionBuilder,
    xxh3_ref: cranelift_codegen::ir::FuncRef,
    probe_ref: cranelift_codegen::ir::FuncRef,
    state_ptr: cranelift_codegen::ir::Value,
    state_len: usize,
    fp_set_ptr: cranelift_codegen::ir::Value,
    seen_block: cranelift_codegen::ir::Block,
    new_block: cranelift_codegen::ir::Block,
) -> cranelift_codegen::ir::Value {
    // Step 1: compute fingerprint
    let len_val = builder.ins().iconst(types::I32, state_len as i64);
    let fp_call = builder.ins().call(xxh3_ref, &[state_ptr, len_val]);
    let fingerprint = builder.inst_results(fp_call)[0];

    // Step 2: probe the dedup set
    let probe_call = builder.ins().call(probe_ref, &[fp_set_ptr, fingerprint]);
    let seen_val = builder.inst_results(probe_call)[0];

    // Step 3: branch on result
    let zero = builder.ins().iconst(types::I32, 0);
    let is_seen = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::NotEqual,
        seen_val,
        zero,
    );
    builder.ins().brif(is_seen, seen_block, &[], new_block, &[]);

    fingerprint
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfs_step::{jit_xxh3_fingerprint_128, jit_xxh3_fingerprint_64};

    fn make_test_arena(state_count: usize, state_len: usize) -> Vec<i64> {
        let mut arena = Vec::with_capacity(state_count * state_len);
        for state_idx in 0..state_count {
            for slot_idx in 0..state_len {
                let mixed = (state_idx as i64)
                    .wrapping_mul(0x9E37)
                    .wrapping_add((slot_idx as i64).wrapping_mul(0x85EB))
                    .wrapping_sub((state_idx as i64) << (slot_idx % 7));
                arena.push(mixed ^ ((slot_idx as i64) << 32));
            }
        }
        arena
    }

    // ====================================================================
    // FingerprintCompiler 64-bit tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_matches_extern_single_slot() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(1).expect("compile fp64 state_len=1");

        let state = [42i64];
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 1);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "compiled fp64 must match extern for 1 slot"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_matches_extern_5_slots() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(5).expect("compile fp64 state_len=5");

        let state = [1i64, 2, 3, 4, 5];
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "compiled fp64 must match extern for 5 slots"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_matches_extern_15_slots() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(15).expect("compile fp64 state_len=15");

        let state: Vec<i64> = (0..15).collect();
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 15);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "compiled fp64 must match extern for 15 slots"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_matches_extern_20_slots() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(20).expect("compile fp64 state_len=20");

        let state: Vec<i64> = (100..120).collect();
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 20);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "compiled fp64 must match extern for 20 slots"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_empty_state() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(0).expect("compile fp64 state_len=0");

        let state: [i64; 0] = [];
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 0);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "compiled fp64 must match extern for empty state"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_deterministic() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(5).expect("compile fp64");

        let state = [7i64, 11, 42, -99, 0];
        let r1 = unsafe { fp_fn(state.as_ptr()) };
        let r2 = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(r1, r2, "compiled fp64 must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_different_inputs_differ() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(3).expect("compile fp64");

        let a = [1i64, 2, 3];
        let b = [1i64, 2, 4];
        let fa = unsafe { fp_fn(a.as_ptr()) };
        let fb = unsafe { fp_fn(b.as_ptr()) };
        assert_ne!(
            fa, fb,
            "compiled fp64 must produce different results for different inputs"
        );
    }

    // ====================================================================
    // Batch fingerprint tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fp64_matches_individual() {
        let state_len = 5usize;
        let state_count = 128usize;
        let arena = make_test_arena(state_count, state_len);

        let batch = batch_fingerprint_arena_64(&arena, state_len);
        let expected: Vec<u64> = arena
            .chunks_exact(state_len)
            .map(|state| jit_xxh3_fingerprint_64(state.as_ptr(), state_len as u32))
            .collect();

        assert_eq!(batch, expected, "batch fp64 must match per-state hashing");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fp128_matches_individual() {
        let state_len = 6usize;
        let state_count = 96usize;
        let arena = make_test_arena(state_count, state_len);

        let batch = batch_fingerprint_arena_128(&arena, state_len);
        let expected: Vec<u128> = arena
            .chunks_exact(state_len)
            .map(|state| {
                let mut lo = 0u64;
                let mut hi = 0u64;
                jit_xxh3_fingerprint_128(state.as_ptr(), state_len as u32, &mut lo, &mut hi);
                ((hi as u128) << 64) | (lo as u128)
            })
            .collect();

        assert_eq!(batch, expected, "batch fp128 must match per-state hashing");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fp64_empty_arena() {
        let arena: [i64; 0] = [];
        let batch = batch_fingerprint_arena_64(&arena, 0);
        assert!(batch.is_empty(), "empty arena must produce no fingerprints");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fp64_single_state() {
        let arena = [11i64, -7, 42, 0];
        let batch = batch_fingerprint_arena_64(&arena, arena.len());
        let expected = vec![jit_xxh3_fingerprint_64(arena.as_ptr(), arena.len() as u32)];
        assert_eq!(batch, expected, "single-state batch must hash correctly");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_batch_fp64_large_batch() {
        let state_len = 4usize;
        let state_count = 10_000usize;
        let arena = make_test_arena(state_count, state_len);
        let batch = batch_fingerprint_arena_64(&arena, state_len);

        assert_eq!(batch.len(), state_count);

        let mut seen = std::collections::HashSet::with_capacity(state_count);
        for (state_idx, fp) in batch.into_iter().enumerate() {
            assert!(
                seen.insert(fp),
                "unexpected 64-bit collision in large batch at state {state_idx}: {fp:#018x}",
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_batch_fp64_matches_extern() {
        let state_len = 7usize;
        let state_count = 257usize;
        let arena = make_test_arena(state_count, state_len);

        let expected = batch_fingerprint_arena_64(&arena, state_len);

        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler
            .compile_batch_64(state_len)
            .expect("compile batch fp64");
        let mut actual = vec![0u64; state_count];
        // SAFETY: `arena` contains `state_count * state_len` contiguous slots and
        // `actual` has exactly `state_count` writable u64 outputs.
        unsafe {
            fp_fn(arena.as_ptr(), state_count as u32, actual.as_mut_ptr());
        }

        assert_eq!(
            actual, expected,
            "compiled batch fp64 must match the extern batch helper"
        );
    }

    // ====================================================================
    // FingerprintCompiler 128-bit tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp128_matches_extern_5_slots() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_128(5).expect("compile fp128 state_len=5");

        let state = [10i64, 20, 30, 40, 50];
        let mut expected_lo: u64 = 0;
        let mut expected_hi: u64 = 0;
        jit_xxh3_fingerprint_128(state.as_ptr(), 5, &mut expected_lo, &mut expected_hi);

        let mut actual_lo: u64 = 0;
        let mut actual_hi: u64 = 0;
        unsafe { fp_fn(state.as_ptr(), &mut actual_lo, &mut actual_hi) };

        assert_eq!(
            actual_lo, expected_lo,
            "compiled fp128 low bits must match extern"
        );
        assert_eq!(
            actual_hi, expected_hi,
            "compiled fp128 high bits must match extern"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp128_matches_extern_15_slots() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler
            .compile_128(15)
            .expect("compile fp128 state_len=15");

        let state: Vec<i64> = (0..15).collect();
        let mut expected_lo: u64 = 0;
        let mut expected_hi: u64 = 0;
        jit_xxh3_fingerprint_128(state.as_ptr(), 15, &mut expected_lo, &mut expected_hi);

        let mut actual_lo: u64 = 0;
        let mut actual_hi: u64 = 0;
        unsafe { fp_fn(state.as_ptr(), &mut actual_lo, &mut actual_hi) };

        assert_eq!(actual_lo, expected_lo);
        assert_eq!(actual_hi, expected_hi);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp128_empty_state() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_128(0).expect("compile fp128 state_len=0");

        let state: [i64; 0] = [];
        let mut expected_lo: u64 = 0;
        let mut expected_hi: u64 = 0;
        jit_xxh3_fingerprint_128(state.as_ptr(), 0, &mut expected_lo, &mut expected_hi);

        let mut actual_lo: u64 = 0;
        let mut actual_hi: u64 = 0;
        unsafe { fp_fn(state.as_ptr(), &mut actual_lo, &mut actual_hi) };

        assert_eq!(actual_lo, expected_lo);
        assert_eq!(actual_hi, expected_hi);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp128_deterministic() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_128(5).expect("compile fp128");

        let state = [7i64, 11, 42, -99, 0];
        let mut lo1: u64 = 0;
        let mut hi1: u64 = 0;
        let mut lo2: u64 = 0;
        let mut hi2: u64 = 0;
        unsafe {
            fp_fn(state.as_ptr(), &mut lo1, &mut hi1);
            fp_fn(state.as_ptr(), &mut lo2, &mut hi2);
        }
        assert_eq!(lo1, lo2, "compiled fp128 must be deterministic (lo)");
        assert_eq!(hi1, hi2, "compiled fp128 must be deterministic (hi)");
    }

    // ====================================================================
    // CompiledFingerprintSet caching tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_set_caching_64() {
        let mut set = CompiledFingerprintSet::new();
        assert_eq!(set.cached_64_count(), 0);

        let fp_fn_a = set
            .get_or_compile_64(5)
            .expect("first compile for state_len=5");
        assert_eq!(set.cached_64_count(), 1);

        let fp_fn_b = set
            .get_or_compile_64(5)
            .expect("cached compile for state_len=5");
        // Function pointers should be the same (cached).
        assert_eq!(
            fp_fn_a as usize, fp_fn_b as usize,
            "cached fp64 must return the same function pointer"
        );
        assert_eq!(set.cached_64_count(), 1);

        // Different state_len should create a new entry.
        let _fp_fn_c = set.get_or_compile_64(10).expect("compile for state_len=10");
        assert_eq!(set.cached_64_count(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_set_caching_128() {
        let mut set = CompiledFingerprintSet::new();
        assert_eq!(set.cached_128_count(), 0);

        let fp_fn_a = set
            .get_or_compile_128(5)
            .expect("first compile for state_len=5");
        assert_eq!(set.cached_128_count(), 1);

        let fp_fn_b = set
            .get_or_compile_128(5)
            .expect("cached compile for state_len=5");
        assert_eq!(
            fp_fn_a as usize, fp_fn_b as usize,
            "cached fp128 must return the same function pointer"
        );
        assert_eq!(set.cached_128_count(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_set_caching_batch64() {
        let mut set = CompiledFingerprintSet::new();
        assert_eq!(set.cached_batch64_count(), 0);

        let fp_fn_a = set
            .get_or_compile_batch_64(7)
            .expect("first compile for state_len=7");
        assert_eq!(set.cached_batch64_count(), 1);

        let fp_fn_b = set
            .get_or_compile_batch_64(7)
            .expect("cached compile for state_len=7");
        // Function pointers should be the same (cached).
        assert_eq!(
            fp_fn_a as usize, fp_fn_b as usize,
            "cached batch fp64 must return the same function pointer"
        );
        assert_eq!(set.cached_batch64_count(), 1);

        // Different state_len should create a new entry.
        let _fp_fn_c = set
            .get_or_compile_batch_64(12)
            .expect("compile for state_len=12");
        assert_eq!(set.cached_batch64_count(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fingerprint_set_correctness() {
        let mut set = CompiledFingerprintSet::new();
        let fp_fn = set.get_or_compile_64(5).expect("compile fp64 via set");

        let state = [1i64, 2, 3, 4, 5];
        let expected = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
        let actual = unsafe { fp_fn(state.as_ptr()) };
        assert_eq!(
            actual, expected,
            "fingerprint from cached set must match direct extern call"
        );
    }

    // ====================================================================
    // Cross-validation with compiled_bfs::state_fingerprint
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_matches_compiled_bfs_state_fingerprint() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(5).expect("compile fp64");

        let state = [7i64, 11, 42, -99, 0];
        let compiled_fp = unsafe { fp_fn(state.as_ptr()) };
        let bfs_fp = crate::compiled_bfs::state_fingerprint(&state);
        assert_eq!(
            compiled_fp, bfs_fp,
            "compiled fp64 must match compiled_bfs::state_fingerprint"
        );
    }

    // ====================================================================
    // Collision resistance
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_fp64_collision_resistance() {
        let mut compiler = FingerprintCompiler::new();
        let fp_fn = compiler.compile_64(1).expect("compile fp64");

        let mut seen = std::collections::HashSet::new();
        for i in 0i64..200 {
            let state = [i];
            let fp = unsafe { fp_fn(state.as_ptr()) };
            assert!(
                seen.insert(fp),
                "compiled fp64 collision at i={}: {:#018x}",
                i,
                fp,
            );
        }
        assert_eq!(seen.len(), 200);
    }

    // ====================================================================
    // Memory leak regression tests (#4082)
    // ====================================================================

    /// Verify that creating and dropping FingerprintCompilers does not leak
    /// JIT code pages. Previously, Memory::drop used mem::forget to leak
    /// mmap'd pages, causing unbounded growth when compilers were dropped
    /// and recreated (#4082).
    ///
    /// Strategy: compile many fingerprint functions across fresh compilers,
    /// drop each compiler, and check that RSS stays bounded. On macOS we
    /// use `mach_task_basic_info` for precise RSS; on other platforms the
    /// test still exercises the create/drop cycle but skips the RSS check.
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_compiled_fingerprint_no_leak_on_drop() {
        // Helper: get current RSS in bytes (macOS only; returns None elsewhere).
        fn current_rss_bytes() -> Option<usize> {
            #[cfg(target_os = "macos")]
            {
                use std::mem::MaybeUninit;
                // SAFETY: mach_task_self() is always valid; task_info fills the
                // struct and sets count. No aliasing or lifetime concerns.
                unsafe {
                    let mut info = MaybeUninit::<libc::mach_task_basic_info_data_t>::zeroed();
                    let mut count = (std::mem::size_of::<libc::mach_task_basic_info_data_t>()
                        / std::mem::size_of::<libc::natural_t>())
                        as libc::mach_msg_type_number_t;
                    let kr = libc::task_info(
                        libc::mach_task_self(),
                        libc::MACH_TASK_BASIC_INFO,
                        info.as_mut_ptr() as libc::task_info_t,
                        &mut count,
                    );
                    if kr == libc::KERN_SUCCESS {
                        Some(info.assume_init().resident_size as usize)
                    } else {
                        None
                    }
                }
            }
            #[cfg(not(target_os = "macos"))]
            {
                None
            }
        }

        // Warm up: compile one function to trigger any one-time init.
        {
            let mut compiler = FingerprintCompiler::new();
            let _ = compiler.compile_64(4).expect("warmup compile_64");
            // compiler + module dropped here
        }

        let rss_before = current_rss_bytes();

        // Create and drop 100 compilers, each compiling 3 functions.
        // Without the fix, each iteration leaks ~64KB+ of mmap'd pages.
        // 100 iterations * ~64KB = ~6.4MB growth.
        let iterations = 100;
        for i in 0..iterations {
            let state_len = (i % 20) + 1;
            let mut compiler = FingerprintCompiler::new();
            let fp64 = compiler.compile_64(state_len).expect("compile_64");
            let _fp128 = compiler.compile_128(state_len).expect("compile_128");
            let _batch = compiler
                .compile_batch_64(state_len)
                .expect("compile_batch_64");

            // Verify the function still works before we drop the compiler.
            let state: Vec<i64> = (0..state_len as i64).collect();
            let result = unsafe { fp64(state.as_ptr()) };
            assert_ne!(result, 0, "compiled fp64 should produce non-zero hash");

            // compiler + all 3 modules dropped here
        }

        // Check RSS growth is bounded. Allow 4MB slack for allocator overhead,
        // test infrastructure, etc. Without the fix, growth would be >6MB.
        if let (Some(before), Some(after)) = (rss_before, current_rss_bytes()) {
            let growth = after.saturating_sub(before);
            let max_allowed = 4 * 1024 * 1024; // 4 MB
            assert!(
                growth < max_allowed,
                "RSS grew by {:.2} MB after {iterations} compile/drop cycles — \
                 likely leaking JIT code pages (#4082). Before: {before}, After: {after}",
                growth as f64 / (1024.0 * 1024.0),
            );
        }
    }

    /// Same as above but for CompiledFingerprintSet: verify that replacing
    /// one set with another releases the old modules' code pages.
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_compiled_fingerprint_set_no_leak_on_drop() {
        // Warm up.
        {
            let mut set = CompiledFingerprintSet::new();
            let _ = set.get_or_compile_64(4).expect("warmup");
        }

        // Create and drop 100 sets, each caching functions for 5 state lengths.
        for _ in 0..100 {
            let mut set = CompiledFingerprintSet::new();
            for state_len in 1..=5 {
                let fp64 = set.get_or_compile_64(state_len).expect("get_or_compile_64");
                let _fp128 = set
                    .get_or_compile_128(state_len)
                    .expect("get_or_compile_128");
                let _batch = set
                    .get_or_compile_batch_64(state_len)
                    .expect("get_or_compile_batch_64");

                // Verify correctness.
                let state: Vec<i64> = (0..state_len as i64).collect();
                let expected = jit_xxh3_fingerprint_64(state.as_ptr(), state_len as u32);
                let actual = unsafe { fp64(state.as_ptr()) };
                assert_eq!(
                    actual, expected,
                    "fingerprint mismatch in leak test at state_len={state_len}"
                );
            }
            assert_eq!(set.cached_64_count(), 5);
            assert_eq!(set.cached_128_count(), 5);
            assert_eq!(set.cached_batch64_count(), 5);
            // set + compiler + all modules dropped here
        }
    }
}
