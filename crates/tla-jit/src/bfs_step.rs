// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled BFS step function — Phase 5 of the JIT V2 SPIN-class plan.
//!
//! Generates a single Cranelift function per spec that performs the entire
//! BFS inner loop in native code:
//!   guard check -> successor write -> fingerprint -> dedup -> invariant check
//!
//! # Architecture
//!
//! ```text
//! bfs_step(state_in, successors_out, result_out) -> u32
//!   for each (action, binding) pair:
//!     ┌─ guard: cmp + branch ─────────────────────┐
//!     │  successor: store to output i64[]          │
//!     │  fingerprint: placeholder (xxhash3/SIMD)   │
//!     │  dedup: placeholder (atomic CAS probe)     │
//!     │  if new: write to output slot              │
//!     └────────────────────────────────────────────┘
//!   for each invariant:
//!     ┌─ scalar check on flat buffer ──────────────┐
//!     │  if violation: set invariant_ok = false     │
//!     └────────────────────────────────────────────┘
//!   return successor_count
//! ```
//!
//! # Status
//!
//! This is **scaffolding** — it generates structurally correct Cranelift IR
//! with the right block structure and control flow, but uses placeholder
//! logic for fingerprinting and deduplication. Guard evaluation and
//! successor construction will be wired to real bytecode lowering in
//! subsequent phases.
//!
//! Part of #3988.
//!
//! # Design Reference
//!
//! See `designs/2026-04-10-jit-v2-spin-class-plan.md`, Phase 5.

use crate::compiled_fingerprint::emit_fingerprint_and_dedup;
use crate::compound_layout::StateLayout;
use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, Block, InstBuilder, UserFuncName};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};

/// Function pointer type for a compiled BFS step function.
///
/// # Parameters
///
/// - `state_in`: pointer to the current state as `&[i64; STATE_LEN]`
/// - `successors_out`: pointer to output buffer as `&mut [[i64; STATE_LEN]]`
///   (pre-allocated by caller with capacity for max successors)
/// - `max_successors`: maximum number of successors that fit in the output buffer
/// - `result_out`: pointer to a `BfsStepResult` struct
///
/// # Returns
///
/// Number of new successors written to `successors_out`.
///
/// # Safety
///
/// All pointers must be valid. `successors_out` must have room for at least
/// `max_successors * state_len` i64 slots. `result_out` must point to a valid
/// `BfsStepResult`.
pub type JitBfsStepFn = unsafe extern "C" fn(
    state_in: *const i64,
    successors_out: *mut i64,
    max_successors: u32,
    result_out: *mut BfsStepResult,
) -> u32;

/// Output struct for a compiled BFS step function.
///
/// Written by the JIT-compiled `bfs_step` function to communicate
/// status back to the Rust BFS loop.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BfsStepResult {
    /// Number of successors generated (before dedup filtering).
    pub successors_generated: u32,
    /// Number of new successors (after dedup filtering).
    /// This equals the return value of the function.
    pub successors_new: u32,
    /// Whether all invariants passed for all new successors.
    /// 0 = at least one invariant violation, 1 = all ok.
    pub invariant_ok: u32,
    /// Index of the first invariant that failed (valid when invariant_ok == 0).
    pub failed_invariant_idx: u32,
    /// Index of the successor state that caused the invariant violation
    /// (valid when invariant_ok == 0).
    pub failed_successor_idx: u32,
    /// Status: 0 = ok, 1 = runtime error, 2 = buffer overflow (too many successors).
    pub status: u32,
}

impl Default for BfsStepResult {
    fn default() -> Self {
        BfsStepResult {
            successors_generated: 0,
            successors_new: 0,
            invariant_ok: 1,
            failed_invariant_idx: 0,
            failed_successor_idx: 0,
            status: 0,
        }
    }
}

/// Status codes for `BfsStepResult::status`.
pub(crate) mod status {
    /// BFS step completed successfully.
    pub const OK: u32 = 0;
    /// A runtime error occurred during evaluation.
    pub const RUNTIME_ERROR: u32 = 1;
    /// The output buffer is full — more successors exist but could not be written.
    pub const BUFFER_OVERFLOW: u32 = 2;
}

/// Re-export of [`ActionDescriptor`] from `tla-jit-abi`.
///
/// Moved to `tla-jit-abi::tier_types` in Wave 14 TL-R1 (Part of #4267 Stage 2d)
/// so callers in `tla-check` can assemble descriptor vectors without importing
/// `tla-jit` and its Cranelift forks.
pub use tla_jit_abi::ActionDescriptor;

/// Re-export of [`InvariantDescriptor`] from `tla-jit-abi`.
///
/// Moved to `tla-jit-abi::tier_types` in Wave 14 TL-R1 (Part of #4267 Stage 2d).
pub use tla_jit_abi::InvariantDescriptor;

/// Re-export of [`BfsStepSpec`] from `tla-jit-runtime`.
///
/// `BfsStepSpec` was migrated to `tla-jit-runtime::bfs_descriptors` in
/// Wave 12 (Part of #4267) so `tla-check` can assemble a step spec through
/// a backend-agnostic path.
pub use tla_jit_runtime::BfsStepSpec;

/// Compiler for BFS step functions.
///
/// Takes a spec's actions, invariants, and state layout and generates
/// a single Cranelift function that performs the entire BFS inner loop
/// in native code.
///
/// # Usage
///
/// ```text
/// let spec = BfsStepSpec { ... };
/// let mut compiler = BfsStepCompiler::new()?;
/// let step_fn = compiler.compile(&spec)?;
///
/// // In the BFS loop:
/// let mut result = BfsStepResult::default();
/// let n_new = unsafe {
///     step_fn(
///         state.as_ptr(),
///         succ_buf.as_mut_ptr(),
///         max_successors,
///         &mut result,
///     )
/// };
/// ```
pub struct BfsStepCompiler {
    module: JITModule,
    ctx: Context,
    builder_ctx: FunctionBuilderContext,
    func_counter: u32,
    /// Retains ownership of JIT modules whose code pages back compiled
    /// function pointers from `compile_with_actions`. Previously these
    /// were `Box::leak`'d, causing unbounded memory growth (#4082).
    _extra_modules: Vec<JITModule>,
}

impl BfsStepCompiler {
    /// Create a new BFS step compiler.
    pub fn new() -> Result<Self, JitError> {
        let module = crate::create_jit_module()?;
        let ctx = module.make_context();
        Ok(BfsStepCompiler {
            module,
            ctx,
            builder_ctx: FunctionBuilderContext::new(),
            func_counter: 0,
            _extra_modules: Vec::new(),
        })
    }

    /// Compile a BFS step function for the given spec.
    ///
    /// Generates Cranelift IR that:
    /// 1. Iterates over all (action, binding) pairs
    /// 2. For each enabled action, writes the successor to the output buffer
    /// 3. Checks invariants on each new successor
    /// 4. Returns the count of new successors
    ///
    /// The generated function has the signature:
    /// ```text
    /// fn bfs_step(state_in: *const i64, successors_out: *mut i64,
    ///             max_successors: u32, result_out: *mut BfsStepResult) -> u32
    /// ```
    pub fn compile(&mut self, spec: &BfsStepSpec) -> Result<JitBfsStepFn, JitError> {
        let ptr_type = self.module.target_config().pointer_type();

        // Build function signature
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // state_in: *const i64
        sig.params.push(AbiParam::new(ptr_type)); // successors_out: *mut i64
        sig.params.push(AbiParam::new(types::I32)); // max_successors: u32
        sig.params.push(AbiParam::new(ptr_type)); // result_out: *mut BfsStepResult
        sig.returns.push(AbiParam::new(types::I32)); // -> u32 (new successor count)

        let func_name = format!("bfs_step_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = self
            .module
            .declare_function(&func_name, Linkage::Local, &sig)?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

            // Create Cranelift variables for mutable state across blocks
            let v_succ_count = Variable::from_u32(0);
            builder.declare_var(v_succ_count, types::I32);

            // Create blocks for the function structure:
            //   entry -> [action_0 -> action_0_write -> action_1 -> ...] -> invariant_check -> exit
            let entry_block = builder.create_block();
            let exit_block = builder.create_block();

            // One guard block + one write block per action
            let action_blocks: Vec<(Block, Block)> = spec
                .actions
                .iter()
                .map(|_| {
                    let guard = builder.create_block();
                    let write = builder.create_block();
                    (guard, write)
                })
                .collect();

            // Invariant check block (entered after all actions complete)
            let invariant_block = builder.create_block();

            // --- Entry block ---
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let state_in = builder.block_params(entry_block)[0];
            let successors_out = builder.block_params(entry_block)[1];
            let max_successors = builder.block_params(entry_block)[2];
            let result_out = builder.block_params(entry_block)[3];

            // Initialize successor count to 0
            let zero_i32 = builder.ins().iconst(types::I32, 0);
            builder.def_var(v_succ_count, zero_i32);

            // Jump to first action block (or invariant block if no actions)
            if action_blocks.is_empty() {
                builder.ins().jump(invariant_block, &[]);
            } else {
                builder.ins().jump(action_blocks[0].0, &[]);
            }

            // --- Action blocks ---
            let state_len_i64 = spec.state_len as i64;

            for (action_idx, (action, (guard_block, write_block))) in
                spec.actions.iter().zip(action_blocks.iter()).enumerate()
            {
                // Determine the next block to jump to if guard fails
                let next_block = if action_idx + 1 < action_blocks.len() {
                    action_blocks[action_idx + 1].0
                } else {
                    invariant_block
                };

                // --- Guard block ---
                // Evaluate the action's guard condition.
                // SCAFFOLDING: placeholder guard that always enables the action.
                // Real implementation will lower the action's guard bytecode here.
                builder.switch_to_block(*guard_block);
                builder.seal_block(*guard_block);

                // Placeholder: load first state variable as a proxy guard
                // In the real implementation, this will be the action's guard
                // expression compiled to Cranelift IR.
                //
                // For now, emit `guard = 1` (always enabled) so the IR structure
                // is exercised.
                let guard_val = builder.ins().iconst(types::I32, 1);
                let zero = builder.ins().iconst(types::I32, 0);
                let guard_cmp = builder.ins().icmp(
                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                    guard_val,
                    zero,
                );
                builder
                    .ins()
                    .brif(guard_cmp, *write_block, &[], next_block, &[]);

                // --- Write block ---
                // Action is enabled: write successor to output buffer.
                builder.switch_to_block(*write_block);
                builder.seal_block(*write_block);

                let current_count = builder.use_var(v_succ_count);

                // Check buffer capacity: if count >= max_successors, jump to exit
                // with BUFFER_OVERFLOW status.
                let overflow_cmp = builder.ins().icmp(
                    cranelift_codegen::ir::condcodes::IntCC::UnsignedGreaterThanOrEqual,
                    current_count,
                    max_successors,
                );
                // Create an overflow handler block
                let overflow_block = builder.create_block();
                let write_continue = builder.create_block();
                builder
                    .ins()
                    .brif(overflow_cmp, overflow_block, &[], write_continue, &[]);

                // --- Overflow block ---
                builder.switch_to_block(overflow_block);
                builder.seal_block(overflow_block);
                // Write BUFFER_OVERFLOW to result_out.status (offset 20 = 5th u32 field)
                let overflow_status = builder
                    .ins()
                    .iconst(types::I32, status::BUFFER_OVERFLOW as i64);
                builder.ins().store(
                    cranelift_codegen::ir::MemFlags::trusted(),
                    overflow_status,
                    result_out,
                    // status is at byte offset 20 (6th field: 5 * sizeof(u32) = 20)
                    20i32,
                );
                // Also write the partial count to result before exiting
                let partial_count = builder.use_var(v_succ_count);
                builder.ins().store(
                    cranelift_codegen::ir::MemFlags::trusted(),
                    partial_count,
                    result_out,
                    0i32, // successors_generated
                );
                builder.ins().store(
                    cranelift_codegen::ir::MemFlags::trusted(),
                    partial_count,
                    result_out,
                    4i32, // successors_new
                );
                builder.ins().jump(exit_block, &[]);

                // --- Write continue block ---
                builder.switch_to_block(write_continue);
                builder.seal_block(write_continue);

                // Compute output pointer: successors_out + count * state_len * 8
                let count_i64 = builder.ins().uextend(types::I64, current_count);
                let state_bytes = builder.ins().iconst(types::I64, state_len_i64 * 8);
                let offset = builder.ins().imul(count_i64, state_bytes);
                let succ_ptr = builder.ins().iadd(successors_out, offset);

                // SCAFFOLDING: Copy state_in to successor slot (identity transition).
                // Real implementation will apply the action's primed variable writes.
                //
                // For now, emit a variable-by-variable copy loop unrolled at
                // compile time: for each slot, load from state_in and store to succ_ptr.
                for slot_idx in 0..spec.state_len {
                    let byte_offset = (slot_idx as i32) * 8;
                    let val = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        state_in,
                        byte_offset,
                    );
                    builder.ins().store(
                        cranelift_codegen::ir::MemFlags::trusted(),
                        val,
                        succ_ptr,
                        byte_offset,
                    );
                }

                // SCAFFOLDING: Apply action-specific modifications.
                // For actions with known write_vars, we would store the computed
                // primed values here. Currently a no-op (successor == parent).
                //
                // Placeholder: tag the successor with the action index by
                // XOR-ing the first slot. This makes successors distinguishable
                // in tests without requiring real action evaluation.
                if spec.state_len > 0 && !action.write_vars.is_empty() {
                    let first_val = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        succ_ptr,
                        0i32,
                    );
                    let action_tag = builder
                        .ins()
                        .iconst(types::I64, (action_idx as i64 + 1) * 1000);
                    let tagged = builder.ins().bxor(first_val, action_tag);
                    builder.ins().store(
                        cranelift_codegen::ir::MemFlags::trusted(),
                        tagged,
                        succ_ptr,
                        0i32,
                    );
                }

                // NOTE: Fingerprint + dedup is implemented in `compile_with_actions()`.
                // That method uses `emit_fingerprint_and_dedup()` to inline
                // xxh3 fingerprinting + atomic CAS dedup into the Cranelift IR.
                // This scaffolding `compile()` intentionally skips fingerprinting
                // to keep the IR structure simple for unit testing.
                // See: compiled_fingerprint.rs, Part of #3987.

                // Increment successor count
                let one_i32 = builder.ins().iconst(types::I32, 1);
                let new_count = builder.ins().iadd(current_count, one_i32);
                builder.def_var(v_succ_count, new_count);

                // Jump to next action's guard block
                builder.ins().jump(next_block, &[]);
            }

            // --- Invariant check block ---
            // SCAFFOLDING: Check invariants on all new successors.
            // Real implementation will lower each invariant's bytecode to
            // inline Cranelift IR and check against each successor.
            //
            // For now, we set invariant_ok = 1 (all pass) unconditionally.
            builder.switch_to_block(invariant_block);
            builder.seal_block(invariant_block);

            let final_count = builder.use_var(v_succ_count);

            // Write results to result_out struct.
            // BfsStepResult layout (all u32, repr(C)):
            //   offset  0: successors_generated
            //   offset  4: successors_new
            //   offset  8: invariant_ok
            //   offset 12: failed_invariant_idx
            //   offset 16: failed_successor_idx
            //   offset 20: status
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                final_count,
                result_out,
                0i32, // successors_generated
            );
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                final_count,
                result_out,
                4i32, // successors_new (== generated when no dedup)
            );
            let inv_ok = builder.ins().iconst(types::I32, 1);
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                inv_ok,
                result_out,
                8i32, // invariant_ok
            );
            let ok_status = builder.ins().iconst(types::I32, status::OK as i64);
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                ok_status,
                result_out,
                20i32, // status
            );

            builder.ins().jump(exit_block, &[]);

            // --- Exit block ---
            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);

            let return_count = builder.use_var(v_succ_count);
            builder.ins().return_(&[return_count]);

            builder.finalize();
        }

        // Compile to machine code
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| {
                self.module.clear_context(&mut self.ctx);
                JitError::CompileError(e.to_string())
            })?;

        self.module.clear_context(&mut self.ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize: {e}")))?;

        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: The transmute from `*const u8` to `JitBfsStepFn` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` (platform C
        //    ABI). `JitBfsStepFn` is `unsafe extern "C" fn(...)`, matching exactly.
        // 2. Signature: The Cranelift IR function takes (ptr, ptr, I32, ptr) -> I32,
        //    matching `JitBfsStepFn`'s `(*const i64, *mut i64, u32, *mut BfsStepResult) -> u32`.
        //    Params declared at lines 231-235 above.
        // 3. Lifetime: Code buffer owned by `self.module`, outlives the returned fn ptr.
        // 4. Validity: `get_finalized_function` returns a non-null pointer to executable
        //    memory only after `finalize_definitions()` succeeds above.
        debug_assert!(!code_ptr.is_null(), "JIT BFS step code pointer is null");
        let jit_fn: JitBfsStepFn = unsafe { std::mem::transmute(code_ptr) };

        Ok(jit_fn)
    }
}

// `CompiledActionFn` / `CompiledInvariantFn` pure-data wrappers moved to
// `tla-jit-runtime` in Wave 12 (#4267). Re-exported here for back-compat.
pub use tla_jit_runtime::{CompiledActionFn, CompiledInvariantFn};

#[cfg(test)]
static BFS_STEP_TEST_FP_PROBE_CALLS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static BFS_STEP_TEST_LAST_FP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
#[cfg(test)]
static BFS_STEP_TEST_LAST_FP_SET: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static BFS_STEP_TEST_FP_PROBE_LOCK: std::sync::OnceLock<std::sync::Mutex<()>> =
    std::sync::OnceLock::new();

#[cfg(test)]
fn bfs_step_test_fp_probe_lock() -> &'static std::sync::Mutex<()> {
    BFS_STEP_TEST_FP_PROBE_LOCK.get_or_init(|| std::sync::Mutex::new(()))
}

#[cfg(test)]
fn reset_bfs_step_test_fp_probe() {
    use std::sync::atomic::Ordering;

    BFS_STEP_TEST_FP_PROBE_CALLS.store(0, Ordering::SeqCst);
    BFS_STEP_TEST_LAST_FP.store(0, Ordering::SeqCst);
    BFS_STEP_TEST_LAST_FP_SET.store(0, Ordering::SeqCst);
}

#[cfg(test)]
fn bfs_step_test_fp_probe_snapshot() -> (usize, u64, usize) {
    use std::sync::atomic::Ordering;

    (
        BFS_STEP_TEST_FP_PROBE_CALLS.load(Ordering::SeqCst),
        BFS_STEP_TEST_LAST_FP.load(Ordering::SeqCst),
        BFS_STEP_TEST_LAST_FP_SET.load(Ordering::SeqCst),
    )
}

/// xxh3-based 64-bit fingerprint of a flat i64 state buffer.
///
/// Callable from JIT-compiled code as an extern "C" symbol. Reinterprets
/// the i64 array as bytes and hashes with xxh3_64 for a fast, high-quality
/// fingerprint. The 64-bit output is used for fingerprint-set dedup (the
/// set uses u64 keys).
///
/// For full 128-bit fingerprinting (used by the Rust-side `FlatFingerprintStrategy`),
/// see [`jit_xxh3_fingerprint_128`].
///
/// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
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
/// This is the SIMD-accelerated path for compiled BFS fingerprinting.
///
/// Part of #3987.
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
            // for `state_count` u64 values. This branch does not read `arena_ptr`.
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
            // for `state_count * 2` u64 values. This branch does not read `arena_ptr`.
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

/// Fingerprint-set probe helper for JIT-generated BFS step code.
pub extern "C" fn jit_fp_set_probe(fp_set: *const u8, fingerprint: u64) -> u32 {
    #[cfg(test)]
    {
        use std::sync::atomic::Ordering;

        BFS_STEP_TEST_FP_PROBE_CALLS.fetch_add(1, Ordering::SeqCst);
        BFS_STEP_TEST_LAST_FP.store(fingerprint, Ordering::SeqCst);
        BFS_STEP_TEST_LAST_FP_SET.store(fp_set as usize, Ordering::SeqCst);
    }

    crate::atomic_fp_set::atomic_fp_set_probe(fp_set, fingerprint)
}

fn create_bfs_step_module_with_symbols(
    extra_symbols: &[(String, *const u8)],
) -> Result<JITModule, JitError> {
    use cranelift_codegen::settings::Configurable;

    let mut flag_builder = cranelift_codegen::settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| JitError::InitError(e.to_string()))?;
    flag_builder
        .set("is_pic", "false")
        .map_err(|e| JitError::InitError(e.to_string()))?;
    flag_builder
        .set("opt_level", "speed")
        .map_err(|e| JitError::InitError(e.to_string()))?;

    let isa_builder = crate::jit_native::native_isa_builder()
        .map_err(|e| JitError::InitError(format!("Native ISA not available: {e}")))?;
    let isa = isa_builder
        .finish(cranelift_codegen::settings::Flags::new(flag_builder))
        .map_err(|e| JitError::InitError(e.to_string()))?;

    let mut builder =
        crate::jit_native::JITBuilder::with_isa(isa, crate::jit_native::default_libcall_names());

    builder.symbol(
        "jit_pow_i64",
        crate::bytecode_lower::scalar_ops::jit_pow_i64 as *const u8,
    );
    builder.symbol(
        "jit_set_contains_i64",
        crate::abi::jit_set_contains_i64 as *const u8,
    );
    builder.symbol(
        "jit_record_get_i64",
        crate::abi::jit_record_get_i64 as *const u8,
    );
    builder.symbol(
        "jit_func_apply_i64",
        crate::abi::jit_func_apply_i64 as *const u8,
    );
    builder.symbol(
        "jit_compound_count",
        crate::abi::jit_compound_count as *const u8,
    );
    builder.symbol("jit_seq_get_i64", crate::abi::jit_seq_get_i64 as *const u8);
    builder.symbol(
        "jit_func_set_membership_check",
        crate::abi::jit_func_set_membership_check as *const u8,
    );
    builder.symbol(
        "jit_record_new_scalar",
        crate::abi::jit_record_new_scalar as *const u8,
    );
    builder.symbol(
        "jit_set_diff_i64",
        crate::abi::jit_set_diff_i64 as *const u8,
    );
    builder.symbol("jit_fp_set_probe", jit_fp_set_probe as *const u8);
    builder.symbol(
        "jit_xxh3_fingerprint_64",
        jit_xxh3_fingerprint_64 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_fingerprint_128",
        jit_xxh3_fingerprint_128 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_batch_fingerprint_64",
        jit_xxh3_batch_fingerprint_64 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_batch_fingerprint_128",
        jit_xxh3_batch_fingerprint_128 as *const u8,
    );

    for (name, ptr) in extra_symbols {
        builder.symbol(name.clone(), *ptr);
    }

    Ok(JITModule::new(builder))
}

fn validate_compiled_functions(
    spec: &BfsStepSpec,
    action_fns: &[CompiledActionFn],
    invariant_fns: &[CompiledInvariantFn],
) -> Result<(), JitError> {
    if action_fns.len() != spec.actions.len() {
        return Err(JitError::CompileError(format!(
            "expected {} compiled actions, got {}",
            spec.actions.len(),
            action_fns.len()
        )));
    }
    if invariant_fns.len() != spec.invariants.len() {
        return Err(JitError::CompileError(format!(
            "expected {} compiled invariants, got {}",
            spec.invariants.len(),
            invariant_fns.len()
        )));
    }

    for (idx, (expected, compiled)) in spec.actions.iter().zip(action_fns.iter()).enumerate() {
        if expected.name != compiled.descriptor.name
            || expected.action_idx != compiled.descriptor.action_idx
            || expected.binding_values != compiled.descriptor.binding_values
            || expected.read_vars != compiled.descriptor.read_vars
            || expected.write_vars != compiled.descriptor.write_vars
        {
            return Err(JitError::CompileError(format!(
                "compiled action metadata mismatch at index {idx}"
            )));
        }
    }

    for (idx, (expected, compiled)) in spec.invariants.iter().zip(invariant_fns.iter()).enumerate()
    {
        if expected.name != compiled.descriptor.name
            || expected.invariant_idx != compiled.descriptor.invariant_idx
        {
            return Err(JitError::CompileError(format!(
                "compiled invariant metadata mismatch at index {idx}"
            )));
        }
    }

    Ok(())
}

fn emit_bfs_step_result(
    builder: &mut FunctionBuilder,
    result_out: cranelift_codegen::ir::Value,
    generated_count: cranelift_codegen::ir::Value,
    new_count: cranelift_codegen::ir::Value,
    invariant_ok: cranelift_codegen::ir::Value,
    failed_invariant_idx: cranelift_codegen::ir::Value,
    failed_successor_idx: cranelift_codegen::ir::Value,
    status_value: cranelift_codegen::ir::Value,
) {
    let mem_flags = cranelift_codegen::ir::MemFlags::trusted();
    builder.ins().store(
        mem_flags,
        generated_count,
        result_out,
        std::mem::offset_of!(BfsStepResult, successors_generated) as i32,
    );
    builder.ins().store(
        mem_flags,
        new_count,
        result_out,
        std::mem::offset_of!(BfsStepResult, successors_new) as i32,
    );
    builder.ins().store(
        mem_flags,
        invariant_ok,
        result_out,
        std::mem::offset_of!(BfsStepResult, invariant_ok) as i32,
    );
    builder.ins().store(
        mem_flags,
        failed_invariant_idx,
        result_out,
        std::mem::offset_of!(BfsStepResult, failed_invariant_idx) as i32,
    );
    builder.ins().store(
        mem_flags,
        failed_successor_idx,
        result_out,
        std::mem::offset_of!(BfsStepResult, failed_successor_idx) as i32,
    );
    builder.ins().store(
        mem_flags,
        status_value,
        result_out,
        std::mem::offset_of!(BfsStepResult, status) as i32,
    );
}

impl BfsStepCompiler {
    /// Compile a BFS step that dispatches through already-compiled action and invariant functions.
    pub fn compile_with_actions(
        &mut self,
        spec: &BfsStepSpec,
        action_fns: &[CompiledActionFn],
        invariant_fns: &[CompiledInvariantFn],
        fp_set_ptr: Option<*const u8>,
    ) -> Result<JitBfsStepFn, JitError> {
        use cranelift_codegen::ir::condcodes::IntCC;
        use cranelift_codegen::ir::StackSlotData;

        validate_compiled_functions(spec, action_fns, invariant_fns)?;

        let compile_idx = self.func_counter;
        self.func_counter += 1;

        let mut extra_symbols = Vec::with_capacity(action_fns.len() + invariant_fns.len());
        let mut action_symbol_names = Vec::with_capacity(action_fns.len());
        let mut invariant_symbol_names = Vec::with_capacity(invariant_fns.len());

        for (idx, action) in action_fns.iter().enumerate() {
            let name = format!("jit_bfs_action_{compile_idx}_{idx}");
            extra_symbols.push((name.clone(), action.func as *const u8));
            action_symbol_names.push(name);
        }
        for (idx, invariant) in invariant_fns.iter().enumerate() {
            let name = format!("jit_bfs_invariant_{compile_idx}_{idx}");
            extra_symbols.push((name.clone(), invariant.func as *const u8));
            invariant_symbol_names.push(name);
        }

        let mut module = create_bfs_step_module_with_symbols(&extra_symbols)?;
        let ptr_type = module.target_config().pointer_type();

        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type));
        sig.params.push(AbiParam::new(ptr_type));
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(ptr_type));
        sig.returns.push(AbiParam::new(types::I32));

        let func_name = format!("bfs_step_with_actions_{compile_idx}");
        let func_id = module.declare_function(&func_name, Linkage::Local, &sig)?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

            let v_generated_count = Variable::from_u32(0);
            let v_new_count = Variable::from_u32(1);
            let v_invariant_ok = Variable::from_u32(2);
            let v_failed_invariant_idx = Variable::from_u32(3);
            let v_failed_successor_idx = Variable::from_u32(4);

            builder.declare_var(v_generated_count, types::I32);
            builder.declare_var(v_new_count, types::I32);
            builder.declare_var(v_invariant_ok, types::I32);
            builder.declare_var(v_failed_invariant_idx, types::I32);
            builder.declare_var(v_failed_successor_idx, types::I32);

            let action_func_refs: Vec<_> = action_symbol_names
                .iter()
                .map(|name| {
                    let mut action_sig = module.make_signature();
                    action_sig.params.push(AbiParam::new(ptr_type));
                    action_sig.params.push(AbiParam::new(ptr_type));
                    action_sig.params.push(AbiParam::new(ptr_type));
                    action_sig.params.push(AbiParam::new(types::I32));
                    let func_id = module.declare_function(name, Linkage::Import, &action_sig)?;
                    Ok(module.declare_func_in_func(func_id, builder.func))
                })
                .collect::<Result<Vec<_>, JitError>>()?;

            let invariant_func_refs: Vec<_> = invariant_symbol_names
                .iter()
                .map(|name| {
                    let mut inv_sig = module.make_signature();
                    inv_sig.params.push(AbiParam::new(ptr_type));
                    inv_sig.params.push(AbiParam::new(ptr_type));
                    inv_sig.params.push(AbiParam::new(types::I32));
                    let func_id = module.declare_function(name, Linkage::Import, &inv_sig)?;
                    Ok(module.declare_func_in_func(func_id, builder.func))
                })
                .collect::<Result<Vec<_>, JitError>>()?;

            let mut probe_sig = module.make_signature();
            probe_sig.params.push(AbiParam::new(ptr_type));
            probe_sig.params.push(AbiParam::new(types::I64));
            probe_sig.returns.push(AbiParam::new(types::I32));
            let probe_func_id =
                module.declare_function("jit_fp_set_probe", Linkage::Import, &probe_sig)?;
            let probe_func_ref = module.declare_func_in_func(probe_func_id, builder.func);

            // xxh3 fingerprint: (ptr, i32) -> i64
            let mut xxh3_sig = module.make_signature();
            xxh3_sig.params.push(AbiParam::new(ptr_type)); // state_ptr
            xxh3_sig.params.push(AbiParam::new(types::I32)); // state_len
            xxh3_sig.returns.push(AbiParam::new(types::I64)); // fingerprint
            let xxh3_func_id =
                module.declare_function("jit_xxh3_fingerprint_64", Linkage::Import, &xxh3_sig)?;
            let xxh3_func_ref = module.declare_func_in_func(xxh3_func_id, builder.func);

            let entry_block = builder.create_block();
            let exit_block = builder.create_block();
            let runtime_error_block = builder.create_block();
            let overflow_block = builder.create_block();
            let action_blocks: Vec<Block> =
                action_fns.iter().map(|_| builder.create_block()).collect();

            let temp_state_slot = builder.create_sized_stack_slot(StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                (spec.state_len.max(1) * 8) as u32,
                8,
            ));
            let call_out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                std::mem::size_of::<crate::abi::JitCallOut>() as u32,
                8,
            ));

            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let state_in = builder.block_params(entry_block)[0];
            let successors_out = builder.block_params(entry_block)[1];
            let max_successors = builder.block_params(entry_block)[2];
            let result_out = builder.block_params(entry_block)[3];

            let zero_i32 = builder.ins().iconst(types::I32, 0);
            let one_i32 = builder.ins().iconst(types::I32, 1);
            let zero_i64 = builder.ins().iconst(types::I64, 0);
            let ok_status_i8 = builder
                .ins()
                .iconst(types::I8, crate::abi::JitStatus::Ok as i64);
            let state_len_val = builder.ins().iconst(types::I32, spec.state_len as i64);
            let fp_set_const = builder
                .ins()
                .iconst(ptr_type, fp_set_ptr.map_or(0i64, |ptr| ptr as i64));
            let state_bytes = builder
                .ins()
                .iconst(types::I64, (spec.state_len as i64) * 8);

            builder.def_var(v_generated_count, zero_i32);
            builder.def_var(v_new_count, zero_i32);
            builder.def_var(v_invariant_ok, one_i32);
            builder.def_var(v_failed_invariant_idx, zero_i32);
            builder.def_var(v_failed_successor_idx, zero_i32);

            if let Some(first_block) = action_blocks.first().copied() {
                builder.ins().jump(first_block, &[]);
            } else {
                builder.ins().jump(exit_block, &[]);
            }

            let call_out_status_offset =
                std::mem::offset_of!(crate::abi::JitCallOut, status) as i32;
            let call_out_value_offset = std::mem::offset_of!(crate::abi::JitCallOut, value) as i32;

            for (action_idx, action_block) in action_blocks.iter().copied().enumerate() {
                let next_action_block = action_blocks
                    .get(action_idx + 1)
                    .copied()
                    .unwrap_or(exit_block);

                builder.switch_to_block(action_block);
                builder.seal_block(action_block);

                let action_continue_block = builder.create_block();
                let action_enabled_block = builder.create_block();
                let dedup_seen_block = builder.create_block();
                let dedup_new_block = builder.create_block();
                let copy_successor_block = builder.create_block();

                let call_out_ptr = builder.ins().stack_addr(ptr_type, call_out_slot, 0);
                let temp_state_ptr = builder.ins().stack_addr(ptr_type, temp_state_slot, 0);
                let call_inst = builder.ins().call(
                    action_func_refs[action_idx],
                    &[call_out_ptr, state_in, temp_state_ptr, state_len_val],
                );
                let _ = call_inst;

                let action_status = builder.ins().load(
                    types::I8,
                    cranelift_codegen::ir::MemFlags::trusted(),
                    call_out_ptr,
                    call_out_status_offset,
                );
                let action_ok = builder
                    .ins()
                    .icmp(IntCC::Equal, action_status, ok_status_i8);
                builder.ins().brif(
                    action_ok,
                    action_continue_block,
                    &[],
                    runtime_error_block,
                    &[],
                );

                builder.switch_to_block(action_continue_block);
                builder.seal_block(action_continue_block);

                let action_enabled_val = builder.ins().load(
                    types::I64,
                    cranelift_codegen::ir::MemFlags::trusted(),
                    call_out_ptr,
                    call_out_value_offset,
                );
                let action_enabled =
                    builder
                        .ins()
                        .icmp(IntCC::NotEqual, action_enabled_val, zero_i64);
                builder.ins().brif(
                    action_enabled,
                    action_enabled_block,
                    &[],
                    next_action_block,
                    &[],
                );

                builder.switch_to_block(action_enabled_block);
                builder.seal_block(action_enabled_block);

                let generated_count = builder.use_var(v_generated_count);
                let next_generated_count = builder.ins().iadd(generated_count, one_i32);
                builder.def_var(v_generated_count, next_generated_count);

                let _fingerprint = emit_fingerprint_and_dedup(
                    &mut builder,
                    xxh3_func_ref,
                    probe_func_ref,
                    temp_state_ptr,
                    spec.state_len,
                    fp_set_const,
                    dedup_seen_block,
                    dedup_new_block,
                );

                builder.switch_to_block(dedup_seen_block);
                builder.seal_block(dedup_seen_block);
                builder.ins().jump(next_action_block, &[]);

                builder.switch_to_block(dedup_new_block);
                builder.seal_block(dedup_new_block);

                let successor_idx = builder.use_var(v_new_count);
                let overflow = builder.ins().icmp(
                    IntCC::UnsignedGreaterThanOrEqual,
                    successor_idx,
                    max_successors,
                );
                builder
                    .ins()
                    .brif(overflow, overflow_block, &[], copy_successor_block, &[]);

                builder.switch_to_block(copy_successor_block);
                builder.seal_block(copy_successor_block);

                for (inv_idx, inv_func_ref) in invariant_func_refs.iter().copied().enumerate() {
                    let inv_status_ok_block = builder.create_block();
                    let inv_pass_block = builder.create_block();
                    let inv_fail_block = builder.create_block();
                    let inv_record_block = builder.create_block();
                    let inv_after_record_block = builder.create_block();
                    let inv_continue_block = builder.create_block();

                    let inv_out_ptr = builder.ins().stack_addr(ptr_type, call_out_slot, 0);
                    let inv_call = builder
                        .ins()
                        .call(inv_func_ref, &[inv_out_ptr, temp_state_ptr, state_len_val]);
                    let _ = inv_call;

                    let inv_status = builder.ins().load(
                        types::I8,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        inv_out_ptr,
                        call_out_status_offset,
                    );
                    let inv_ok = builder.ins().icmp(IntCC::Equal, inv_status, ok_status_i8);
                    builder
                        .ins()
                        .brif(inv_ok, inv_status_ok_block, &[], runtime_error_block, &[]);

                    builder.switch_to_block(inv_status_ok_block);
                    builder.seal_block(inv_status_ok_block);

                    let inv_value = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        inv_out_ptr,
                        call_out_value_offset,
                    );
                    let inv_passed = builder.ins().icmp(IntCC::NotEqual, inv_value, zero_i64);
                    builder
                        .ins()
                        .brif(inv_passed, inv_pass_block, &[], inv_fail_block, &[]);

                    builder.switch_to_block(inv_pass_block);
                    builder.seal_block(inv_pass_block);
                    builder.ins().jump(inv_continue_block, &[]);

                    builder.switch_to_block(inv_fail_block);
                    builder.seal_block(inv_fail_block);

                    let invariant_ok = builder.use_var(v_invariant_ok);
                    let needs_record = builder.ins().icmp(IntCC::Equal, invariant_ok, one_i32);
                    builder.ins().brif(
                        needs_record,
                        inv_record_block,
                        &[],
                        inv_after_record_block,
                        &[],
                    );

                    builder.switch_to_block(inv_record_block);
                    builder.seal_block(inv_record_block);
                    builder.def_var(v_invariant_ok, zero_i32);
                    let failed_invariant_idx_val = builder.ins().iconst(
                        types::I32,
                        invariant_fns[inv_idx].descriptor.invariant_idx as i64,
                    );
                    builder.def_var(v_failed_invariant_idx, failed_invariant_idx_val);
                    builder.def_var(v_failed_successor_idx, successor_idx);
                    builder.ins().jump(inv_after_record_block, &[]);

                    builder.switch_to_block(inv_after_record_block);
                    builder.seal_block(inv_after_record_block);
                    builder.ins().jump(inv_continue_block, &[]);

                    builder.switch_to_block(inv_continue_block);
                    builder.seal_block(inv_continue_block);
                }

                let succ_idx_i64 = builder.ins().uextend(types::I64, successor_idx);
                let succ_offset = builder.ins().imul(succ_idx_i64, state_bytes);
                let succ_ptr = builder.ins().iadd(successors_out, succ_offset);
                for slot_idx in 0..spec.state_len {
                    let byte_offset = (slot_idx as i32) * 8;
                    let slot_val = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        temp_state_ptr,
                        byte_offset,
                    );
                    builder.ins().store(
                        cranelift_codegen::ir::MemFlags::trusted(),
                        slot_val,
                        succ_ptr,
                        byte_offset,
                    );
                }

                let next_new_count = builder.ins().iadd(successor_idx, one_i32);
                builder.def_var(v_new_count, next_new_count);
                builder.ins().jump(next_action_block, &[]);
            }

            builder.switch_to_block(runtime_error_block);
            builder.seal_block(runtime_error_block);
            let runtime_generated = builder.use_var(v_generated_count);
            let runtime_new = builder.use_var(v_new_count);
            let runtime_inv_ok = builder.use_var(v_invariant_ok);
            let runtime_failed_inv = builder.use_var(v_failed_invariant_idx);
            let runtime_failed_succ = builder.use_var(v_failed_successor_idx);
            let runtime_status = builder
                .ins()
                .iconst(types::I32, status::RUNTIME_ERROR as i64);
            emit_bfs_step_result(
                &mut builder,
                result_out,
                runtime_generated,
                runtime_new,
                runtime_inv_ok,
                runtime_failed_inv,
                runtime_failed_succ,
                runtime_status,
            );
            builder.ins().return_(&[runtime_new]);

            builder.switch_to_block(overflow_block);
            builder.seal_block(overflow_block);
            let overflow_generated = builder.use_var(v_generated_count);
            let overflow_new = builder.use_var(v_new_count);
            let overflow_inv_ok = builder.use_var(v_invariant_ok);
            let overflow_failed_inv = builder.use_var(v_failed_invariant_idx);
            let overflow_failed_succ = builder.use_var(v_failed_successor_idx);
            let overflow_status = builder
                .ins()
                .iconst(types::I32, status::BUFFER_OVERFLOW as i64);
            emit_bfs_step_result(
                &mut builder,
                result_out,
                overflow_generated,
                overflow_new,
                overflow_inv_ok,
                overflow_failed_inv,
                overflow_failed_succ,
                overflow_status,
            );
            builder.ins().return_(&[overflow_new]);

            builder.switch_to_block(exit_block);
            builder.seal_block(exit_block);
            let final_generated = builder.use_var(v_generated_count);
            let final_new = builder.use_var(v_new_count);
            let final_inv_ok = builder.use_var(v_invariant_ok);
            let final_failed_inv = builder.use_var(v_failed_invariant_idx);
            let final_failed_succ = builder.use_var(v_failed_successor_idx);
            let ok_status = builder.ins().iconst(types::I32, status::OK as i64);
            emit_bfs_step_result(
                &mut builder,
                result_out,
                final_generated,
                final_new,
                final_inv_ok,
                final_failed_inv,
                final_failed_succ,
                ok_status,
            );
            builder.ins().return_(&[final_new]);

            builder.finalize();
        }

        module.define_function(func_id, &mut ctx).map_err(|e| {
            module.clear_context(&mut ctx);
            JitError::CompileError(e.to_string())
        })?;

        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize: {e}")))?;

        let code_ptr = module.get_finalized_function(func_id);
        // Retain the module so its mmap'd code pages stay alive (#4082).
        // Previously Box::leak'd — now owned by the compiler.
        self._extra_modules.push(module);
        // SAFETY: The transmute from `*const u8` to `JitBfsStepFn` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` (platform C
        //    ABI). `JitBfsStepFn` is `unsafe extern "C" fn(...)`, matching exactly.
        // 2. Signature: The Cranelift IR function takes (ptr, ptr, I32, ptr) -> I32,
        //    matching `JitBfsStepFn`'s `(*const i64, *mut i64, u32, *mut BfsStepResult) -> u32`.
        // 3. Lifetime: Code buffer is kept alive via self._extra_modules — the module
        //    and its mmap'd pages persist until the compiler is dropped.
        // 4. Validity: `get_finalized_function` returns a non-null pointer to executable
        //    memory only after `finalize_definitions()` succeeds above.
        debug_assert!(
            !code_ptr.is_null(),
            "JIT BFS step code pointer is null (compile_with_actions)"
        );
        let jit_fn: JitBfsStepFn = unsafe { std::mem::transmute(code_ptr) };
        Ok(jit_fn)
    }

    /// Compile a fused BFS level function that processes an entire frontier
    /// in a single Cranelift function.
    ///
    /// Unlike `compile_with_actions` which processes one parent per call,
    /// this generates a function that loops over all parents in a contiguous
    /// arena, dispatches actions, fingerprints, deduplicates, checks invariants,
    /// and writes new successors to an output buffer -- all in one native
    /// function call with zero Rust-to-JIT boundary crossings per parent.
    ///
    /// The generated function has the [`JitBfsLevelFn`] signature:
    /// ```text
    /// fn(parents_ptr, parent_count, succ_out, succ_capacity, result_out) -> u32
    /// ```
    ///
    /// Part of #3988: JIT V2 Phase 5 fused BFS level function.
    pub fn compile_fused_level(
        &mut self,
        spec: &BfsStepSpec,
        action_fns: &[CompiledActionFn],
        invariant_fns: &[CompiledInvariantFn],
        fp_set_ptr: Option<*const u8>,
    ) -> Result<crate::compiled_bfs_level::JitBfsLevelFn, JitError> {
        use cranelift_codegen::ir::condcodes::IntCC;
        use cranelift_codegen::ir::StackSlotData;

        validate_compiled_functions(spec, action_fns, invariant_fns)?;

        let compile_idx = self.func_counter;
        self.func_counter += 1;

        // Register action and invariant symbols.
        let mut extra_symbols = Vec::with_capacity(action_fns.len() + invariant_fns.len());
        let mut action_symbol_names = Vec::with_capacity(action_fns.len());
        let mut invariant_symbol_names = Vec::with_capacity(invariant_fns.len());

        for (idx, action) in action_fns.iter().enumerate() {
            let name = format!("jit_fused_action_{compile_idx}_{idx}");
            extra_symbols.push((name.clone(), action.func as *const u8));
            action_symbol_names.push(name);
        }
        for (idx, invariant) in invariant_fns.iter().enumerate() {
            let name = format!("jit_fused_invariant_{compile_idx}_{idx}");
            extra_symbols.push((name.clone(), invariant.func as *const u8));
            invariant_symbol_names.push(name);
        }

        let mut module = create_bfs_step_module_with_symbols(&extra_symbols)?;
        let ptr_type = module.target_config().pointer_type();

        // Function signature: (parents_ptr, parent_count, succ_out, succ_capacity, result_out) -> u32
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type));    // parents_ptr: *const i64
        sig.params.push(AbiParam::new(types::I32));  // parent_count: u32
        sig.params.push(AbiParam::new(ptr_type));    // succ_out: *mut i64
        sig.params.push(AbiParam::new(types::I32));  // succ_capacity: u32
        sig.params.push(AbiParam::new(ptr_type));    // result_out: *mut BfsLevelLoopResult
        sig.returns.push(AbiParam::new(types::I32)); // -> u32 (total_new)

        let func_name = format!("bfs_fused_level_{compile_idx}");
        let func_id = module.declare_function(&func_name, Linkage::Local, &sig)?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

            // Mutable variables across blocks.
            let v_parent_idx = Variable::from_u32(0);
            let v_total_generated = Variable::from_u32(1);
            let v_total_new = Variable::from_u32(2);
            let v_invariant_ok = Variable::from_u32(3);
            let v_failed_invariant_idx = Variable::from_u32(4);
            let v_failed_parent_idx = Variable::from_u32(5);
            let v_failed_successor_idx = Variable::from_u32(6);

            builder.declare_var(v_parent_idx, types::I32);
            builder.declare_var(v_total_generated, types::I32);
            builder.declare_var(v_total_new, types::I32);
            builder.declare_var(v_invariant_ok, types::I32);
            builder.declare_var(v_failed_invariant_idx, types::I32);
            builder.declare_var(v_failed_parent_idx, types::I32);
            builder.declare_var(v_failed_successor_idx, types::I32);

            // Declare action function imports.
            let action_func_refs: Vec<_> = action_symbol_names
                .iter()
                .map(|name| {
                    let mut action_sig = module.make_signature();
                    action_sig.params.push(AbiParam::new(ptr_type)); // out
                    action_sig.params.push(AbiParam::new(ptr_type)); // state_in
                    action_sig.params.push(AbiParam::new(ptr_type)); // state_out
                    action_sig.params.push(AbiParam::new(types::I32)); // state_len
                    let fid = module.declare_function(name, Linkage::Import, &action_sig)?;
                    Ok(module.declare_func_in_func(fid, builder.func))
                })
                .collect::<Result<Vec<_>, JitError>>()?;

            // Declare invariant function imports.
            let invariant_func_refs: Vec<_> = invariant_symbol_names
                .iter()
                .map(|name| {
                    let mut inv_sig = module.make_signature();
                    inv_sig.params.push(AbiParam::new(ptr_type)); // out
                    inv_sig.params.push(AbiParam::new(ptr_type)); // state
                    inv_sig.params.push(AbiParam::new(types::I32)); // state_len
                    let fid = module.declare_function(name, Linkage::Import, &inv_sig)?;
                    Ok(module.declare_func_in_func(fid, builder.func))
                })
                .collect::<Result<Vec<_>, JitError>>()?;

            // Declare xxh3 and fp_probe imports.
            let mut xxh3_sig = module.make_signature();
            xxh3_sig.params.push(AbiParam::new(ptr_type));
            xxh3_sig.params.push(AbiParam::new(types::I32));
            xxh3_sig.returns.push(AbiParam::new(types::I64));
            let xxh3_func_id =
                module.declare_function("jit_xxh3_fingerprint_64", Linkage::Import, &xxh3_sig)?;
            let xxh3_func_ref = module.declare_func_in_func(xxh3_func_id, builder.func);

            let mut probe_sig = module.make_signature();
            probe_sig.params.push(AbiParam::new(ptr_type));
            probe_sig.params.push(AbiParam::new(types::I64));
            probe_sig.returns.push(AbiParam::new(types::I32));
            let probe_func_id =
                module.declare_function("jit_fp_set_probe", Linkage::Import, &probe_sig)?;
            let probe_func_ref = module.declare_func_in_func(probe_func_id, builder.func);

            // Stack slots for temporary state and call_out.
            let temp_state_slot = builder.create_sized_stack_slot(StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                (spec.state_len.max(1) * 8) as u32,
                8,
            ));
            let call_out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                std::mem::size_of::<crate::abi::JitCallOut>() as u32,
                8,
            ));

            // Create blocks.
            let entry_block = builder.create_block();
            let parent_loop_header = builder.create_block();
            let parent_loop_tail = builder.create_block();
            let write_result_block = builder.create_block();
            let overflow_block = builder.create_block();
            let runtime_error_block = builder.create_block();

            // --- Entry block ---
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let parents_ptr = builder.block_params(entry_block)[0];
            let parent_count = builder.block_params(entry_block)[1];
            let succ_out = builder.block_params(entry_block)[2];
            let succ_capacity = builder.block_params(entry_block)[3];
            let result_out = builder.block_params(entry_block)[4];

            let zero_i32 = builder.ins().iconst(types::I32, 0);
            let one_i32 = builder.ins().iconst(types::I32, 1);
            let zero_i64 = builder.ins().iconst(types::I64, 0);
            let ok_status_i8 = builder
                .ins()
                .iconst(types::I8, crate::abi::JitStatus::Ok as i64);
            let state_len_val = builder.ins().iconst(types::I32, spec.state_len as i64);
            let fp_set_const = builder
                .ins()
                .iconst(ptr_type, fp_set_ptr.map_or(0i64, |ptr| ptr as i64));
            let state_bytes_i64 = builder
                .ins()
                .iconst(types::I64, (spec.state_len as i64) * 8);

            builder.def_var(v_parent_idx, zero_i32);
            builder.def_var(v_total_generated, zero_i32);
            builder.def_var(v_total_new, zero_i32);
            builder.def_var(v_invariant_ok, one_i32);
            builder.def_var(v_failed_invariant_idx, zero_i32);
            builder.def_var(v_failed_parent_idx, zero_i32);
            builder.def_var(v_failed_successor_idx, zero_i32);

            // Declare v_parent_ptr variable before entering the loop.
            let v_parent_ptr = Variable::from_u32(7);
            builder.declare_var(v_parent_ptr, ptr_type);
            builder.def_var(v_parent_ptr, parents_ptr); // dummy initial value

            let call_out_status_offset =
                std::mem::offset_of!(crate::abi::JitCallOut, status) as i32;
            let call_out_value_offset = std::mem::offset_of!(crate::abi::JitCallOut, value) as i32;

            builder.ins().jump(parent_loop_header, &[]);

            // --- Parent loop header (condition check only) ---
            builder.switch_to_block(parent_loop_header);

            let pidx = builder.use_var(v_parent_idx);
            let loop_done = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, pidx, parent_count);

            // Create a loop body block for parent pointer computation.
            let loop_body_block = builder.create_block();
            builder
                .ins()
                .brif(loop_done, write_result_block, &[], loop_body_block, &[]);

            // --- Loop body: compute parent_ptr, then fall through to actions ---
            builder.switch_to_block(loop_body_block);
            builder.seal_block(loop_body_block);

            let pidx_body = builder.use_var(v_parent_idx);
            let pidx_i64 = builder.ins().uextend(types::I64, pidx_body);
            let parent_offset = builder.ins().imul(pidx_i64, state_bytes_i64);
            let parent_ptr_val = builder.ins().iadd(parents_ptr, parent_offset);
            builder.def_var(v_parent_ptr, parent_ptr_val);

            // Create the first action block (or go to loop tail if no actions).
            let first_action_block = if action_fns.is_empty() {
                parent_loop_tail
            } else {
                builder.create_block()
            };
            builder.ins().jump(first_action_block, &[]);

            // --- Action blocks (one per action) ---
            let mut action_blocks = Vec::with_capacity(action_fns.len());
            if !action_fns.is_empty() {
                action_blocks.push(first_action_block);
                for _ in 1..action_fns.len() {
                    action_blocks.push(builder.create_block());
                }
            }

            for (action_idx, action_block) in action_blocks.iter().copied().enumerate() {
                let next_action_or_tail = action_blocks
                    .get(action_idx + 1)
                    .copied()
                    .unwrap_or(parent_loop_tail);

                builder.switch_to_block(action_block);

                let action_continue_block = builder.create_block();
                let action_enabled_block = builder.create_block();
                let dedup_seen_block = builder.create_block();
                let dedup_new_block = builder.create_block();
                let copy_successor_block = builder.create_block();

                let call_out_ptr = builder.ins().stack_addr(ptr_type, call_out_slot, 0);
                let temp_state_ptr = builder.ins().stack_addr(ptr_type, temp_state_slot, 0);
                let parent_ptr = builder.use_var(v_parent_ptr);

                // Call action function.
                builder.ins().call(
                    action_func_refs[action_idx],
                    &[call_out_ptr, parent_ptr, temp_state_ptr, state_len_val],
                );

                // Check action status.
                let action_status = builder.ins().load(
                    types::I8,
                    cranelift_codegen::ir::MemFlags::trusted(),
                    call_out_ptr,
                    call_out_status_offset,
                );
                let action_ok =
                    builder.ins().icmp(IntCC::Equal, action_status, ok_status_i8);
                builder.ins().brif(
                    action_ok,
                    action_continue_block,
                    &[],
                    runtime_error_block,
                    &[],
                );

                builder.switch_to_block(action_continue_block);
                builder.seal_block(action_continue_block);

                // Check if action is enabled (value != 0).
                let action_enabled_val = builder.ins().load(
                    types::I64,
                    cranelift_codegen::ir::MemFlags::trusted(),
                    call_out_ptr,
                    call_out_value_offset,
                );
                let action_enabled =
                    builder
                        .ins()
                        .icmp(IntCC::NotEqual, action_enabled_val, zero_i64);
                builder.ins().brif(
                    action_enabled,
                    action_enabled_block,
                    &[],
                    next_action_or_tail,
                    &[],
                );

                builder.switch_to_block(action_enabled_block);
                builder.seal_block(action_enabled_block);

                // Increment total_generated.
                let gen_count = builder.use_var(v_total_generated);
                let next_gen_count = builder.ins().iadd(gen_count, one_i32);
                builder.def_var(v_total_generated, next_gen_count);

                // Fingerprint + dedup.
                let _fingerprint = emit_fingerprint_and_dedup(
                    &mut builder,
                    xxh3_func_ref,
                    probe_func_ref,
                    temp_state_ptr,
                    spec.state_len,
                    fp_set_const,
                    dedup_seen_block,
                    dedup_new_block,
                );

                // Seen -> skip to next action.
                builder.switch_to_block(dedup_seen_block);
                builder.seal_block(dedup_seen_block);
                builder.ins().jump(next_action_or_tail, &[]);

                // New -> check capacity, invariants, copy.
                builder.switch_to_block(dedup_new_block);
                builder.seal_block(dedup_new_block);

                let successor_idx = builder.use_var(v_total_new);
                let overflow = builder.ins().icmp(
                    IntCC::UnsignedGreaterThanOrEqual,
                    successor_idx,
                    succ_capacity,
                );
                builder
                    .ins()
                    .brif(overflow, overflow_block, &[], copy_successor_block, &[]);

                builder.switch_to_block(copy_successor_block);
                builder.seal_block(copy_successor_block);

                // Check invariants on the new successor (temp_state).
                for (inv_idx, inv_func_ref) in invariant_func_refs.iter().copied().enumerate() {
                    let inv_status_ok_block = builder.create_block();
                    let inv_pass_block = builder.create_block();
                    let inv_fail_block = builder.create_block();
                    let inv_record_block = builder.create_block();
                    let inv_after_record_block = builder.create_block();
                    let inv_continue_block = builder.create_block();

                    let inv_out_ptr = builder.ins().stack_addr(ptr_type, call_out_slot, 0);
                    let inv_temp_ptr = builder.ins().stack_addr(ptr_type, temp_state_slot, 0);
                    builder
                        .ins()
                        .call(inv_func_ref, &[inv_out_ptr, inv_temp_ptr, state_len_val]);

                    let inv_status = builder.ins().load(
                        types::I8,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        inv_out_ptr,
                        call_out_status_offset,
                    );
                    let inv_ok = builder.ins().icmp(IntCC::Equal, inv_status, ok_status_i8);
                    builder
                        .ins()
                        .brif(inv_ok, inv_status_ok_block, &[], runtime_error_block, &[]);

                    builder.switch_to_block(inv_status_ok_block);
                    builder.seal_block(inv_status_ok_block);

                    let inv_value = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        inv_out_ptr,
                        call_out_value_offset,
                    );
                    let inv_passed =
                        builder.ins().icmp(IntCC::NotEqual, inv_value, zero_i64);
                    builder
                        .ins()
                        .brif(inv_passed, inv_pass_block, &[], inv_fail_block, &[]);

                    builder.switch_to_block(inv_pass_block);
                    builder.seal_block(inv_pass_block);
                    builder.ins().jump(inv_continue_block, &[]);

                    builder.switch_to_block(inv_fail_block);
                    builder.seal_block(inv_fail_block);

                    // Record the first invariant failure.
                    let cur_inv_ok = builder.use_var(v_invariant_ok);
                    let needs_record =
                        builder.ins().icmp(IntCC::Equal, cur_inv_ok, one_i32);
                    builder.ins().brif(
                        needs_record,
                        inv_record_block,
                        &[],
                        inv_after_record_block,
                        &[],
                    );

                    builder.switch_to_block(inv_record_block);
                    builder.seal_block(inv_record_block);
                    builder.def_var(v_invariant_ok, zero_i32);
                    let failed_inv_val = builder.ins().iconst(
                        types::I32,
                        invariant_fns[inv_idx].descriptor.invariant_idx as i64,
                    );
                    builder.def_var(v_failed_invariant_idx, failed_inv_val);
                    let cur_pidx = builder.use_var(v_parent_idx);
                    builder.def_var(v_failed_parent_idx, cur_pidx);
                    builder.def_var(v_failed_successor_idx, successor_idx);
                    builder.ins().jump(inv_after_record_block, &[]);

                    builder.switch_to_block(inv_after_record_block);
                    builder.seal_block(inv_after_record_block);
                    builder.ins().jump(inv_continue_block, &[]);

                    builder.switch_to_block(inv_continue_block);
                    builder.seal_block(inv_continue_block);
                }

                // Copy temp_state -> succ_out[total_new * state_len * 8].
                let succ_idx_i64 = builder.ins().uextend(types::I64, successor_idx);
                let succ_offset = builder.ins().imul(succ_idx_i64, state_bytes_i64);
                let succ_ptr = builder.ins().iadd(succ_out, succ_offset);
                let temp_copy_ptr = builder.ins().stack_addr(ptr_type, temp_state_slot, 0);
                for slot_idx in 0..spec.state_len {
                    let byte_offset = (slot_idx as i32) * 8;
                    let slot_val = builder.ins().load(
                        types::I64,
                        cranelift_codegen::ir::MemFlags::trusted(),
                        temp_copy_ptr,
                        byte_offset,
                    );
                    builder.ins().store(
                        cranelift_codegen::ir::MemFlags::trusted(),
                        slot_val,
                        succ_ptr,
                        byte_offset,
                    );
                }

                // Increment total_new.
                let next_new = builder.ins().iadd(successor_idx, one_i32);
                builder.def_var(v_total_new, next_new);
                builder.ins().jump(next_action_or_tail, &[]);
            }

            // --- Parent loop tail ---
            builder.switch_to_block(parent_loop_tail);
            let cur_pidx = builder.use_var(v_parent_idx);
            let next_pidx = builder.ins().iadd(cur_pidx, one_i32);
            builder.def_var(v_parent_idx, next_pidx);
            builder.ins().jump(parent_loop_header, &[]);

            // Seal loop header now that both predecessors (entry, loop_tail) are complete.
            builder.seal_block(parent_loop_header);
            // Seal all action blocks (predecessors: loop_header for first, previous action for rest).
            for block in &action_blocks {
                builder.seal_block(*block);
            }
            builder.seal_block(parent_loop_tail);

            // --- Write result block ---
            builder.switch_to_block(write_result_block);
            builder.seal_block(write_result_block);
            {
                let final_parents = builder.use_var(v_parent_idx);
                let final_generated = builder.use_var(v_total_generated);
                let final_new = builder.use_var(v_total_new);
                let final_inv_ok = builder.use_var(v_invariant_ok);
                let final_failed_inv = builder.use_var(v_failed_invariant_idx);
                let final_failed_parent = builder.use_var(v_failed_parent_idx);
                let final_failed_succ = builder.use_var(v_failed_successor_idx);
                let ok_status = builder.ins().iconst(types::I32, status::OK as i64);

                emit_level_result(
                    &mut builder,
                    result_out,
                    final_parents,
                    final_generated,
                    final_new,
                    final_inv_ok,
                    final_failed_inv,
                    final_failed_parent,
                    final_failed_succ,
                    ok_status,
                );
                builder.ins().return_(&[final_new]);
            }

            // --- Overflow block ---
            builder.switch_to_block(overflow_block);
            builder.seal_block(overflow_block);
            {
                let ov_parents = builder.use_var(v_parent_idx);
                let ov_generated = builder.use_var(v_total_generated);
                let ov_new = builder.use_var(v_total_new);
                let ov_inv_ok = builder.use_var(v_invariant_ok);
                let ov_failed_inv = builder.use_var(v_failed_invariant_idx);
                let ov_failed_parent = builder.use_var(v_failed_parent_idx);
                let ov_failed_succ = builder.use_var(v_failed_successor_idx);
                let ov_status = builder
                    .ins()
                    .iconst(types::I32, status::BUFFER_OVERFLOW as i64);

                emit_level_result(
                    &mut builder,
                    result_out,
                    ov_parents,
                    ov_generated,
                    ov_new,
                    ov_inv_ok,
                    ov_failed_inv,
                    ov_failed_parent,
                    ov_failed_succ,
                    ov_status,
                );
                builder.ins().return_(&[ov_new]);
            }

            // --- Runtime error block ---
            builder.switch_to_block(runtime_error_block);
            builder.seal_block(runtime_error_block);
            {
                let re_parents = builder.use_var(v_parent_idx);
                let re_generated = builder.use_var(v_total_generated);
                let re_new = builder.use_var(v_total_new);
                let re_inv_ok = builder.use_var(v_invariant_ok);
                let re_failed_inv = builder.use_var(v_failed_invariant_idx);
                let re_failed_parent = builder.use_var(v_failed_parent_idx);
                let re_failed_succ = builder.use_var(v_failed_successor_idx);
                let re_status = builder
                    .ins()
                    .iconst(types::I32, status::RUNTIME_ERROR as i64);

                emit_level_result(
                    &mut builder,
                    result_out,
                    re_parents,
                    re_generated,
                    re_new,
                    re_inv_ok,
                    re_failed_inv,
                    re_failed_parent,
                    re_failed_succ,
                    re_status,
                );
                builder.ins().return_(&[re_new]);
            }

            builder.finalize();
        }

        module.define_function(func_id, &mut ctx).map_err(|e| {
            module.clear_context(&mut ctx);
            JitError::CompileError(e.to_string())
        })?;

        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize fused level: {e}")))?;

        let code_ptr = module.get_finalized_function(func_id);
        // Retain the module so its mmap'd code pages stay alive (#4082).
        self._extra_modules.push(module);

        // SAFETY: The transmute from `*const u8` to `JitBfsLevelFn` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` (platform C
        //    ABI). `JitBfsLevelFn` is `unsafe extern "C" fn(...)`, matching exactly.
        // 2. Signature: The Cranelift IR function takes (ptr, I32, ptr, I32, ptr) -> I32,
        //    matching `JitBfsLevelFn`'s parameters and return type.
        // 3. Lifetime: Code buffer is kept alive via self._extra_modules.
        // 4. Validity: `get_finalized_function` returns a non-null pointer to executable
        //    memory only after `finalize_definitions()` succeeds above.
        debug_assert!(
            !code_ptr.is_null(),
            "JIT fused BFS level code pointer is null"
        );
        let jit_fn: crate::compiled_bfs_level::JitBfsLevelFn =
            unsafe { std::mem::transmute(code_ptr) };
        Ok(jit_fn)
    }
}

/// Emit stores for a `BfsLevelLoopResult` struct.
fn emit_level_result(
    builder: &mut FunctionBuilder,
    result_out: cranelift_codegen::ir::Value,
    parents_processed: cranelift_codegen::ir::Value,
    total_generated: cranelift_codegen::ir::Value,
    total_new: cranelift_codegen::ir::Value,
    invariant_ok: cranelift_codegen::ir::Value,
    failed_invariant_idx: cranelift_codegen::ir::Value,
    failed_parent_idx: cranelift_codegen::ir::Value,
    failed_successor_idx: cranelift_codegen::ir::Value,
    status_value: cranelift_codegen::ir::Value,
) {
    use crate::compiled_bfs_level::BfsLevelLoopResult;
    let mem_flags = cranelift_codegen::ir::MemFlags::trusted();
    builder.ins().store(
        mem_flags,
        parents_processed,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, parents_processed) as i32,
    );
    builder.ins().store(
        mem_flags,
        total_generated,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, total_generated) as i32,
    );
    builder.ins().store(
        mem_flags,
        total_new,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, total_new) as i32,
    );
    builder.ins().store(
        mem_flags,
        invariant_ok,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, invariant_ok) as i32,
    );
    builder.ins().store(
        mem_flags,
        failed_invariant_idx,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, failed_invariant_idx) as i32,
    );
    builder.ins().store(
        mem_flags,
        failed_parent_idx,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, failed_parent_idx) as i32,
    );
    builder.ins().store(
        mem_flags,
        failed_successor_idx,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, failed_successor_idx) as i32,
    );
    builder.ins().store(
        mem_flags,
        status_value,
        result_out,
        std::mem::offset_of!(BfsLevelLoopResult, status) as i32,
    );
}

#[cfg(test)]
pub(crate) mod compile_with_actions_tests {
    use super::*;
    use crate::abi::JitCallOut;
    use crate::atomic_fp_set::AtomicFpSet;
    use crate::compound_layout::{StateLayout, VarLayout};

    fn make_test_spec(
        n_vars: usize,
        actions: Vec<ActionDescriptor>,
        invariants: Vec<InvariantDescriptor>,
    ) -> BfsStepSpec {
        BfsStepSpec {
            state_len: n_vars,
            state_layout: StateLayout::new(vec![VarLayout::ScalarInt; n_vars]),
            actions,
            invariants,
        }
    }

    fn expected_fingerprint(state: &[i64]) -> u64 {
        // Must match jit_xxh3_fingerprint_64 — the JIT now calls xxh3.
        super::jit_xxh3_fingerprint_64(state.as_ptr(), state.len() as u32)
    }

    unsafe extern "C" fn disabled_action(
        out: *mut JitCallOut,
        _state_in: *const i64,
        _state_out: *mut i64,
        _state_len: u32,
    ) {
        unsafe {
            *out = JitCallOut::ok(0);
        }
    }

    pub(crate) unsafe extern "C" fn increment_first_slot_action(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let state_len = state_len as usize;
        let state_in = unsafe { std::slice::from_raw_parts(state_in, state_len) };
        let state_out = unsafe { std::slice::from_raw_parts_mut(state_out, state_len) };
        state_out.copy_from_slice(state_in);
        if let Some(first) = state_out.first_mut() {
            *first += 1;
        }
        unsafe {
            *out = JitCallOut::ok(1);
        }
    }

    unsafe extern "C" fn set_first_slot_large_action(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let state_len = state_len as usize;
        let state_in = unsafe { std::slice::from_raw_parts(state_in, state_len) };
        let state_out = unsafe { std::slice::from_raw_parts_mut(state_out, state_len) };
        state_out.copy_from_slice(state_in);
        if let Some(first) = state_out.first_mut() {
            *first = 42;
        }
        unsafe {
            *out = JitCallOut::ok(1);
        }
    }

    unsafe extern "C" fn first_slot_lt_ten(
        out: *mut JitCallOut,
        state: *const i64,
        state_len: u32,
    ) {
        let state = unsafe { std::slice::from_raw_parts(state, state_len as usize) };
        let passed = state.first().copied().unwrap_or(0) < 10;
        unsafe {
            *out = JitCallOut::ok(passed as i64);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compile_with_actions_dispatches_and_hashes_successors() {
        let _lock = bfs_step_test_fp_probe_lock()
            .lock()
            .expect("fingerprint probe test lock");
        reset_bfs_step_test_fp_probe();

        let actions = vec![
            ActionDescriptor {
                name: "Disabled".to_string(),
                action_idx: 0,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![],
            },
            ActionDescriptor {
                name: "Inc".to_string(),
                action_idx: 1,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![0],
            },
        ];
        let spec = make_test_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![
            CompiledActionFn::new(actions[0].clone(), disabled_action),
            CompiledActionFn::new(actions[1].clone(), increment_first_slot_action),
        ];

        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let fp_set = AtomicFpSet::new(32);
        let fp_set_ptr = std::ptr::from_ref(&fp_set).cast::<u8>();
        let step_fn = compiler
            .compile_with_actions(&spec, &compiled_actions, &[], Some(fp_set_ptr))
            .expect("compile_with_actions");

        let state_in = [7i64, 11];
        let mut succ_buf = [0i64; 8];
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 4, &mut result) };

        assert_eq!(n, 1);
        assert_eq!(result.successors_generated, 1);
        assert_eq!(result.successors_new, 1);
        assert_eq!(result.status, status::OK);
        assert_eq!(&succ_buf[0..2], &[8, 11]);

        let (calls, fingerprint, seen_ptr) = bfs_step_test_fp_probe_snapshot();
        assert_eq!(calls, 1, "dedup probe should run for the enabled successor");
        assert_eq!(seen_ptr, fp_set_ptr as usize);
        assert_eq!(fingerprint, expected_fingerprint(&succ_buf[0..2]));
        assert_eq!(fp_set.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compile_with_actions_records_invariant_failures() {
        let _lock = bfs_step_test_fp_probe_lock()
            .lock()
            .expect("fingerprint probe test lock");
        reset_bfs_step_test_fp_probe();

        let actions = vec![ActionDescriptor {
            name: "SetLarge".to_string(),
            action_idx: 0,
            binding_values: vec![],
            read_vars: vec![0],
            write_vars: vec![0],
        }];
        let invariants = vec![InvariantDescriptor {
            name: "Slot0Lt10".to_string(),
            invariant_idx: 0,
        }];
        let spec = make_test_spec(2, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(
            actions[0].clone(),
            set_first_slot_large_action,
        )];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            first_slot_lt_ten,
        )];

        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler
            .compile_with_actions(&spec, &compiled_actions, &compiled_invariants, None)
            .expect("compile_with_actions");

        let state_in = [1i64, 2];
        let mut succ_buf = [0i64; 8];
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 4, &mut result) };

        assert_eq!(n, 1);
        assert_eq!(result.successors_generated, 1);
        assert_eq!(result.successors_new, 1);
        assert_eq!(result.invariant_ok, 0);
        assert_eq!(result.failed_invariant_idx, 0);
        assert_eq!(result.failed_successor_idx, 0);
        assert_eq!(result.status, status::OK);
        assert_eq!(&succ_buf[0..2], &[42, 2]);

        // Verify the dedup probe was called exactly once (for the one enabled successor)
        let (calls, _, _) = bfs_step_test_fp_probe_snapshot();
        assert_eq!(
            calls, 1,
            "dedup probe should be called once for the enabled successor"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compound_layout::{StateLayout, VarLayout};

    /// Build a simple spec with N scalar variables, M actions, and K invariants.
    fn make_test_spec(
        n_vars: usize,
        actions: Vec<ActionDescriptor>,
        invariants: Vec<InvariantDescriptor>,
    ) -> BfsStepSpec {
        let vars = vec![VarLayout::ScalarInt; n_vars];
        BfsStepSpec {
            state_len: n_vars,
            state_layout: StateLayout::new(vars),
            actions,
            invariants,
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_compiler_creation() {
        let compiler = BfsStepCompiler::new();
        assert!(compiler.is_ok(), "BfsStepCompiler should initialize");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_empty_spec() {
        let spec = make_test_spec(3, vec![], vec![]);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile empty spec");

        // Call with an empty state — should return 0 successors.
        let state_in: [i64; 3] = [10, 20, 30];
        let mut succ_buf: [i64; 30] = [0; 30]; // room for 10 successors
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 10, &mut result) };

        assert_eq!(n, 0, "no actions means no successors");
        assert_eq!(result.successors_generated, 0);
        assert_eq!(result.invariant_ok, 1);
        assert_eq!(result.status, status::OK);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_single_action_no_writes() {
        let actions = vec![ActionDescriptor {
            name: "Tick".to_string(),
            action_idx: 0,
            binding_values: vec![],
            read_vars: vec![0],
            write_vars: vec![], // no writes -> successor is identity copy
        }];
        let spec = make_test_spec(3, actions, vec![]);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile single action");

        let state_in: [i64; 3] = [10, 20, 30];
        let mut succ_buf: [i64; 30] = [0; 30];
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 10, &mut result) };

        assert_eq!(n, 1, "one action should produce one successor");
        assert_eq!(result.successors_generated, 1);
        assert_eq!(result.invariant_ok, 1);
        // Successor should be a copy of the input (no writes, no tagging)
        assert_eq!(&succ_buf[0..3], &[10, 20, 30]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_multiple_actions() {
        let actions = vec![
            ActionDescriptor {
                name: "ActionA".to_string(),
                action_idx: 0,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![0],
            },
            ActionDescriptor {
                name: "ActionB".to_string(),
                action_idx: 1,
                binding_values: vec![],
                read_vars: vec![1],
                write_vars: vec![1],
            },
            ActionDescriptor {
                name: "ActionC".to_string(),
                action_idx: 2,
                binding_values: vec![],
                read_vars: vec![0, 1],
                write_vars: vec![2],
            },
        ];
        let spec = make_test_spec(4, actions, vec![]);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile multiple actions");

        let state_in: [i64; 4] = [1, 2, 3, 4];
        let mut succ_buf: [i64; 40] = [0; 40]; // room for 10 successors
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 10, &mut result) };

        assert_eq!(n, 3, "three actions should produce three successors");
        assert_eq!(result.successors_generated, 3);
        assert_eq!(result.status, status::OK);

        // Each successor is at succ_buf[i*4 .. i*4+4]
        // ActionA tags slot 0: 1 XOR 1000
        assert_eq!(succ_buf[0], 1 ^ 1000, "ActionA should tag slot 0");
        // ActionB tags slot 0: 1 XOR 2000
        assert_eq!(succ_buf[4], 1 ^ 2000, "ActionB should tag slot 0");
        // ActionC tags slot 0: 1 XOR 3000
        assert_eq!(succ_buf[8], 1 ^ 3000, "ActionC should tag slot 0");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_buffer_overflow() {
        let actions = vec![
            ActionDescriptor {
                name: "A".to_string(),
                action_idx: 0,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![],
            },
            ActionDescriptor {
                name: "B".to_string(),
                action_idx: 1,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![],
            },
            ActionDescriptor {
                name: "C".to_string(),
                action_idx: 2,
                binding_values: vec![],
                read_vars: vec![0],
                write_vars: vec![],
            },
        ];
        let spec = make_test_spec(2, actions, vec![]);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile");

        let state_in: [i64; 2] = [5, 10];
        let mut succ_buf: [i64; 4] = [0; 4]; // room for only 2 successors
        let mut result = BfsStepResult::default();

        let n = unsafe {
            step_fn(
                state_in.as_ptr(),
                succ_buf.as_mut_ptr(),
                2, // max 2 successors
                &mut result,
            )
        };

        // Should write 2 successors, then detect overflow on the 3rd
        assert_eq!(n, 2, "should stop at buffer capacity");
        assert_eq!(result.status, status::BUFFER_OVERFLOW);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_result_default() {
        let result = BfsStepResult::default();
        assert_eq!(result.successors_generated, 0);
        assert_eq!(result.successors_new, 0);
        assert_eq!(result.invariant_ok, 1);
        assert_eq!(result.failed_invariant_idx, 0);
        assert_eq!(result.failed_successor_idx, 0);
        assert_eq!(result.status, status::OK);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_with_bindings() {
        // Simulate `\E i \in {0,1}: SendMsg(i)` producing 2 action entries
        let actions = vec![
            ActionDescriptor {
                name: "SendMsg".to_string(),
                action_idx: 0,
                binding_values: vec![0],
                read_vars: vec![0, 1],
                write_vars: vec![1],
            },
            ActionDescriptor {
                name: "SendMsg".to_string(),
                action_idx: 0,
                binding_values: vec![1],
                read_vars: vec![0, 1],
                write_vars: vec![1],
            },
        ];
        let spec = make_test_spec(3, actions, vec![]);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile with bindings");

        let state_in: [i64; 3] = [100, 200, 300];
        let mut succ_buf: [i64; 30] = [0; 30];
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 10, &mut result) };

        assert_eq!(
            n, 2,
            "two binding specializations should produce two successors"
        );
        assert_eq!(result.status, status::OK);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_with_invariants() {
        let actions = vec![ActionDescriptor {
            name: "Step".to_string(),
            action_idx: 0,
            binding_values: vec![],
            read_vars: vec![0],
            write_vars: vec![0],
        }];
        let invariants = vec![
            InvariantDescriptor {
                name: "TypeOK".to_string(),
                invariant_idx: 0,
            },
            InvariantDescriptor {
                name: "Safety".to_string(),
                invariant_idx: 1,
            },
        ];
        let spec = make_test_spec(2, actions, invariants);
        let mut compiler = BfsStepCompiler::new().expect("compiler init");
        let step_fn = compiler.compile(&spec).expect("compile with invariants");

        let state_in: [i64; 2] = [42, 99];
        let mut succ_buf: [i64; 20] = [0; 20];
        let mut result = BfsStepResult::default();

        let n = unsafe { step_fn(state_in.as_ptr(), succ_buf.as_mut_ptr(), 10, &mut result) };

        assert_eq!(n, 1);
        // Scaffolding invariant check always passes
        assert_eq!(result.invariant_ok, 1);
        assert_eq!(result.status, status::OK);
    }

    // ====================================================================
    // xxh3 fingerprint function tests (Part of #3987)
    // ====================================================================

    #[test]
    fn test_jit_xxh3_fingerprint_64_deterministic() {
        let state = [1i64, 2, 3, 4, 5];
        let fp1 = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
        let fp2 = jit_xxh3_fingerprint_64(state.as_ptr(), 5);
        assert_eq!(fp1, fp2, "xxh3_64 must be deterministic");
    }

    #[test]
    fn test_jit_xxh3_fingerprint_64_different_inputs_differ() {
        let a = [1i64, 2, 3];
        let b = [1i64, 2, 4];
        let fp_a = jit_xxh3_fingerprint_64(a.as_ptr(), 3);
        let fp_b = jit_xxh3_fingerprint_64(b.as_ptr(), 3);
        assert_ne!(
            fp_a, fp_b,
            "different inputs must produce different fingerprints"
        );
    }

    #[test]
    fn test_jit_xxh3_fingerprint_64_empty_state() {
        let state: [i64; 0] = [];
        let fp1 = jit_xxh3_fingerprint_64(state.as_ptr(), 0);
        let fp2 = jit_xxh3_fingerprint_64(state.as_ptr(), 0);
        assert_eq!(fp1, fp2, "empty state must be deterministic");
    }

    #[test]
    fn test_jit_xxh3_fingerprint_64_matches_xxhash_rust_crate() {
        // Verify jit_xxh3_fingerprint_64 produces the same result as
        // calling xxhash_rust::xxh3::xxh3_64 directly on the byte buffer.
        let state = [10i64, 20, 30, 40, 50];
        let bytes = unsafe {
            std::slice::from_raw_parts(
                state.as_ptr().cast::<u8>(),
                state.len() * std::mem::size_of::<i64>(),
            )
        };
        let expected = xxhash_rust::xxh3::xxh3_64(bytes);
        let actual = jit_xxh3_fingerprint_64(state.as_ptr(), state.len() as u32);
        assert_eq!(
            actual, expected,
            "jit_xxh3_fingerprint_64 must match xxh3_64"
        );
    }

    #[test]
    fn test_jit_xxh3_fingerprint_128_returns_both_halves() {
        let state = [42i64, -7, 0, i64::MAX, i64::MIN];
        let mut lo: u64 = 0;
        let mut hi: u64 = 0;
        jit_xxh3_fingerprint_128(state.as_ptr(), 5, &mut lo, &mut hi);
        // At least one half should be non-zero for a non-trivial input.
        assert!(lo != 0 || hi != 0, "128-bit fingerprint should be non-zero");
    }

    #[test]
    fn test_jit_xxh3_fingerprint_128_matches_xxhash_rust_crate() {
        let state = [10i64, 20, 30, 40, 50];
        let bytes = unsafe {
            std::slice::from_raw_parts(
                state.as_ptr().cast::<u8>(),
                state.len() * std::mem::size_of::<i64>(),
            )
        };
        let expected_128 = xxhash_rust::xxh3::xxh3_128(bytes);
        let expected_lo = expected_128 as u64;
        let expected_hi = (expected_128 >> 64) as u64;

        let mut lo: u64 = 0;
        let mut hi: u64 = 0;
        jit_xxh3_fingerprint_128(state.as_ptr(), state.len() as u32, &mut lo, &mut hi);

        assert_eq!(lo, expected_lo, "low 64 bits must match xxh3_128");
        assert_eq!(hi, expected_hi, "high 64 bits must match xxh3_128");
    }

    #[test]
    fn test_jit_xxh3_fingerprint_64_collision_resistance() {
        let mut seen = std::collections::HashSet::new();
        for i in 0i64..200 {
            let state = [i];
            let fp = jit_xxh3_fingerprint_64(state.as_ptr(), 1);
            assert!(
                seen.insert(fp),
                "xxh3_64 collision at i={}: fingerprint {:#018x} already seen",
                i,
                fp,
            );
        }
        assert_eq!(seen.len(), 200);
    }

    #[test]
    fn test_jit_xxh3_fingerprint_64_matches_compiled_bfs_state_fingerprint() {
        // Verify consistency between the extern "C" function and compiled_bfs::state_fingerprint.
        let state = [7i64, 11, 42, -99, 0];
        let jit_fp = jit_xxh3_fingerprint_64(state.as_ptr(), state.len() as u32);
        let bfs_fp = crate::compiled_bfs::state_fingerprint(&state);
        assert_eq!(
            jit_fp, bfs_fp,
            "JIT xxh3 and compiled_bfs::state_fingerprint must agree"
        );
    }
}
