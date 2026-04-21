// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compiled liveness predicate evaluation for JIT-accelerated fairness checking.
//!
//! # Overview
//!
//! During BFS model checking, liveness checking requires evaluating fairness
//! predicates (WF/SF conditions) for every state and transition. These
//! predicates are `LiveExpr` leaf nodes: `StatePred`, `ActionPred`, `Enabled`,
//! and `StateChanged`. The results are stored as bitmask bits in
//! `StateBitmaskMap` and `ActionBitmaskMap`.
//!
//! Without JIT, these predicates go through the tree-walking interpreter
//! (`eval_state_leaves_with_array_successors` / `eval_action_leaves_array`).
//! This module provides compiled alternatives that operate on flattened i64
//! state buffers, producing bitmask results directly.
//!
//! # Architecture
//!
//! ```text
//! LiveExpr leaves ──► LivenessPredicateCompiler ──► Cranelift IR ──► Native code
//!                                                                       │
//!     record_missing_state_results ◄── CompiledStatePredFn ◄────────────┘
//!     record_missing_action_results ◄── CompiledActionPredFn ◄──────────┘
//! ```
//!
//! ## Function signatures
//!
//! **State predicate batch:**
//! ```text
//! fn(state: *const i64, state_len: u32) -> u64  // returns bitmask of true tags
//! ```
//!
//! **Action predicate batch:**
//! ```text
//! fn(current: *const i64, next: *const i64, state_len: u32) -> u64  // returns bitmask
//! ```
//!
//! ## Integration
//!
//! The `CompiledLivenessBatch` holds compiled function pointers for state and
//! action predicate batches. When available, the inline liveness recording
//! path in `tla-check` calls these instead of the interpreter, falling back
//! to interpreted evaluation for predicates that could not be compiled
//! (e.g., those requiring ENABLED evaluation with existential quantifiers).
//!
//! # Compilation eligibility
//!
//! A `LiveExpr` leaf is eligible for compilation when:
//! - It is a `StatePred` or `ActionPred` (not `Enabled` or `StateChanged`)
//! - Its underlying AST expression is JIT-eligible (scalar operations only)
//! - Its tag is < 64 (fits in the u64 bitmask)
//!
//! `Enabled` predicates require successor enumeration and cannot be compiled
//! to a simple predicate function. `StateChanged` predicates compare subscript
//! values between current and next state, which may involve compound types.
//! Both fall back to interpreted evaluation.
//!
//! Part of #3992.

use crate::compound_layout::StateLayout;
use crate::error::JitError;
use crate::jit_native::JITModule;

/// Function pointer type for a compiled batch of state-level liveness predicates.
///
/// Takes a pointer to the current state as a flat i64 array and the number of
/// state variables. Returns a u64 bitmask where bit `tag` is set if predicate
/// with that tag evaluates to true.
///
/// # Safety
///
/// `state` must point to a valid `[i64; state_len]` array. The function reads
/// exactly `state_len` elements.
pub type CompiledStatePredBatchFn = unsafe extern "C" fn(state: *const i64, state_len: u32) -> u64;

/// Function pointer type for a compiled batch of action-level liveness predicates.
///
/// Takes pointers to the current and next state as flat i64 arrays and the
/// number of state variables. Returns a u64 bitmask where bit `tag` is set
/// if predicate with that tag evaluates to true for the transition.
///
/// # Safety
///
/// Both `current` and `next` must point to valid `[i64; state_len]` arrays.
pub type CompiledActionPredBatchFn =
    unsafe extern "C" fn(current: *const i64, next: *const i64, state_len: u32) -> u64;

/// Function pointer type for compiled SCC acceptance checking.
///
/// Takes a node/SCC bitmask plus a pointer to acceptance masks. Returns 1 if
/// every acceptance mask has at least one overlapping bit in
/// `node_state_bitmask`, otherwise returns 0.
///
/// # Safety
///
/// `acceptance_masks_ptr` must point to `num_masks` valid `u64` values unless
/// `num_masks == 0`.
pub type CompiledAcceptanceCheckFn = unsafe extern "C" fn(
    node_state_bitmask: u64,
    acceptance_masks_ptr: *const u64,
    num_masks: u32,
) -> u32;

/// Statistics from SCC helper compilation.
#[derive(Debug, Clone, Default)]
pub struct SccHelperStats {
    /// Number of promise masks tracked by the helper.
    pub num_promise_masks: usize,
    /// Number of AE state tags folded into `ae_state_tag_mask`.
    pub num_ae_state_tags: usize,
    /// Number of AE action tags folded into `ae_action_tag_mask`.
    pub num_ae_action_tags: usize,
    /// Compilation time in microseconds.
    pub compile_time_us: u64,
}

/// Compiled helpers for SCC-level liveness acceptance checks.
///
/// Promise masks are stored one-per-promise. AE state/action tags are folded
/// into aggregate bitmasks because SCC satisfaction is existential within each
/// category: any matching bit in the aggregate mask satisfies that category.
///
/// Part of #3992.
#[derive(Debug)]
pub struct CompiledSccHelpers {
    /// Compiled checker for the combined acceptance masks, if compilation ran.
    pub acceptance_fn: Option<CompiledAcceptanceCheckFn>,
    /// Per-promise bitmask: each set bit is a tag that fulfills that promise.
    pub promise_tag_masks: Vec<u64>,
    /// Combined bitmask for AE state tags.
    pub ae_state_tag_mask: u64,
    /// Combined bitmask for AE action tags.
    pub ae_action_tag_mask: u64,
    /// Compilation statistics.
    pub stats: SccHelperStats,
    /// Retains ownership of JIT modules whose code pages back the compiled
    /// function pointers. Previously leaked via std::mem::forget (#4082).
    _modules: Vec<JITModule>,
}

impl CompiledSccHelpers {
    /// Build compiled SCC acceptance helpers from promise and AE tag masks.
    ///
    /// AE tags are combined into a single mask per category. Promise masks are
    /// preserved one-per-promise because each promise must be satisfied.
    pub fn new(
        promise_tag_masks: Vec<u64>,
        ae_state_tags: &[u32],
        ae_action_tags: &[u32],
    ) -> Result<Self, JitError> {
        let start = std::time::Instant::now();
        let num_promise_masks = promise_tag_masks.len();

        let ae_state_tag_mask = build_tag_mask(ae_state_tags, "AE state")?;
        let ae_action_tag_mask = build_tag_mask(ae_action_tags, "AE action")?;

        let mut combined_masks = Vec::with_capacity(
            promise_tag_masks.len()
                + usize::from(ae_state_tag_mask != 0)
                + usize::from(ae_action_tag_mask != 0),
        );
        combined_masks.extend_from_slice(&promise_tag_masks);
        if ae_state_tag_mask != 0 {
            combined_masks.push(ae_state_tag_mask);
        }
        if ae_action_tag_mask != 0 {
            combined_masks.push(ae_action_tag_mask);
        }

        let mut modules = Vec::new();
        let acceptance_fn = if combined_masks.is_empty() {
            None
        } else {
            let (fn_ptr, module) = compile_acceptance_checker(&combined_masks)?;
            modules.push(module);
            Some(fn_ptr)
        };

        Ok(Self {
            acceptance_fn,
            promise_tag_masks,
            ae_state_tag_mask,
            ae_action_tag_mask,
            stats: SccHelperStats {
                num_promise_masks,
                num_ae_state_tags: ae_state_tags.len(),
                num_ae_action_tags: ae_action_tags.len(),
                compile_time_us: start.elapsed().as_micros() as u64,
            },
            _modules: modules,
        })
    }

    /// Check whether a node/SCC bitmask satisfies the configured acceptance
    /// constraints.
    #[must_use]
    pub fn check_node_acceptance(&self, node_state_bitmask: u64) -> bool {
        let acceptance_masks = self.combined_acceptance_masks();

        if let Some(check_fn) = self.acceptance_fn {
            let Ok(num_masks) = u32::try_from(acceptance_masks.len()) else {
                return false;
            };
            // SAFETY: The pointer references `acceptance_masks.len()` contiguous
            // `u64` values for the duration of the call. The compiled function
            // only reads the mask slice.
            return unsafe {
                check_fn(node_state_bitmask, acceptance_masks.as_ptr(), num_masks) != 0
            };
        }

        interpreted_acceptance_check(node_state_bitmask, &acceptance_masks)
    }

    fn combined_acceptance_masks(&self) -> Vec<u64> {
        let mut masks = Vec::with_capacity(
            self.promise_tag_masks.len()
                + usize::from(self.ae_state_tag_mask != 0)
                + usize::from(self.ae_action_tag_mask != 0),
        );
        masks.extend_from_slice(&self.promise_tag_masks);
        if self.ae_state_tag_mask != 0 {
            masks.push(self.ae_state_tag_mask);
        }
        if self.ae_action_tag_mask != 0 {
            masks.push(self.ae_action_tag_mask);
        }
        masks
    }
}

/// Compile a generic acceptance checker for SCC bitmask evaluation.
///
/// The generated function checks that, for every mask in
/// `acceptance_masks_ptr[..num_masks]`, `node_state_bitmask & mask != 0`.
///
/// Returns the compiled function pointer and the JITModule that owns the
/// code pages. The caller must retain the module for the function pointer
/// to remain valid (#4082).
pub fn compile_acceptance_checker(
    acceptance_masks: &[u64],
) -> Result<(CompiledAcceptanceCheckFn, JITModule), JitError> {
    use crate::jit_native::{Linkage, Module};
    use cranelift_codegen::ir::{
        condcodes::IntCC, types, AbiParam, InstBuilder, MemFlags, UserFuncName,
    };
    use cranelift_codegen::Context;
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

    let _num_masks = u32::try_from(acceptance_masks.len()).map_err(|_| {
        JitError::CompileError(format!(
            "too many SCC acceptance masks: {}",
            acceptance_masks.len()
        ))
    })?;

    let mut module = crate::create_jit_module()?;
    let pointer_type = module.target_config().pointer_type();

    // Define function signature:
    // (node_state_bitmask: u64, acceptance_masks_ptr: *const u64, num_masks: u32) -> u32
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(pointer_type));
    sig.params.push(AbiParam::new(types::I32));
    sig.returns.push(AbiParam::new(types::I32));

    let func_id = module
        .declare_function("liveness_scc_acceptance_check", Linkage::Export, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let mut ctx = Context::new();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, 2);

    let mut fb_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);

    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    builder.seal_block(entry_block);

    let node_state_bitmask = builder.block_params(entry_block)[0];
    let acceptance_masks_ptr = builder.block_params(entry_block)[1];
    let num_masks = builder.block_params(entry_block)[2];

    let loop_header = builder.create_block();
    builder.append_block_param(loop_header, types::I32); // idx

    let loop_body = builder.create_block();
    let continue_block = builder.create_block();
    let success_block = builder.create_block();
    let fail_block = builder.create_block();

    let zero_i32 = builder.ins().iconst(types::I32, 0);
    builder.ins().jump(loop_header, &[zero_i32]);

    builder.switch_to_block(loop_header);
    let idx = builder.block_params(loop_header)[0];
    let at_end = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, idx, num_masks);
    builder
        .ins()
        .brif(at_end, success_block, &[], loop_body, &[]);

    builder.switch_to_block(loop_body);
    builder.seal_block(loop_body);

    let idx_ptr = builder.ins().uextend(pointer_type, idx);
    let byte_offset = builder.ins().imul_imm(idx_ptr, 8);
    let mask_addr = builder.ins().iadd(acceptance_masks_ptr, byte_offset);
    let mask = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), mask_addr, 0);

    let masked = builder.ins().band(node_state_bitmask, mask);
    let zero_i64 = builder.ins().iconst(types::I64, 0);
    let has_match = builder.ins().icmp(IntCC::NotEqual, masked, zero_i64);
    builder
        .ins()
        .brif(has_match, continue_block, &[], fail_block, &[]);

    builder.switch_to_block(continue_block);
    builder.seal_block(continue_block);
    let next_idx = builder.ins().iadd_imm(idx, 1);
    builder.ins().jump(loop_header, &[next_idx]);

    builder.seal_block(loop_header);

    builder.switch_to_block(fail_block);
    builder.seal_block(fail_block);
    let zero_result = builder.ins().iconst(types::I32, 0);
    builder.ins().return_(&[zero_result]);

    builder.switch_to_block(success_block);
    builder.seal_block(success_block);
    let one_result = builder.ins().iconst(types::I32, 1);
    builder.ins().return_(&[one_result]);
    builder.finalize();

    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    module.clear_context(&mut ctx);
    module
        .finalize_definitions()
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let code_ptr = module.get_finalized_function(func_id);

    // SAFETY: The generated function follows the CompiledAcceptanceCheckFn ABI.
    // The module is returned to the caller who retains it so the code pages
    // stay valid. Previously leaked via std::mem::forget (#4082).
    debug_assert!(!code_ptr.is_null(), "compiled acceptance check code pointer is null");
    let fn_ptr: CompiledAcceptanceCheckFn = unsafe { std::mem::transmute(code_ptr) };
    Ok((fn_ptr, module))
}

fn build_tag_mask(tags: &[u32], label: &str) -> Result<u64, JitError> {
    let mut mask = 0u64;
    for &tag in tags {
        if tag >= 64 {
            return Err(JitError::CompileError(format!(
                "{label} tag {tag} exceeds u64 bitmask capacity"
            )));
        }
        mask |= 1u64 << tag;
    }
    Ok(mask)
}

fn interpreted_acceptance_check(node_state_bitmask: u64, acceptance_masks: &[u64]) -> bool {
    acceptance_masks
        .iter()
        .all(|&mask| (node_state_bitmask & mask) != 0)
}

/// Result of attempting to compile a liveness predicate batch.
///
/// Contains compiled function pointers for eligible predicates and a list
/// of tags that could not be compiled (requiring interpreter fallback).
#[derive(Debug)]
pub struct CompiledLivenessBatch {
    /// Compiled state predicate batch function, if any state predicates
    /// were successfully compiled. Returns bitmask of true tags.
    pub state_pred_fn: Option<CompiledStatePredBatchFn>,

    /// Tags of state predicates that were compiled into `state_pred_fn`.
    /// Only these bits in the returned bitmask are valid.
    pub compiled_state_tags: Vec<u32>,

    /// Tags of state predicates that could NOT be compiled and require
    /// interpreter fallback.
    pub fallback_state_tags: Vec<u32>,

    /// Compiled action predicate batch function, if any action predicates
    /// were successfully compiled. Returns bitmask of true tags.
    pub action_pred_fn: Option<CompiledActionPredBatchFn>,

    /// Tags of action predicates that were compiled into `action_pred_fn`.
    pub compiled_action_tags: Vec<u32>,

    /// Tags of action predicates that could NOT be compiled.
    pub fallback_action_tags: Vec<u32>,

    /// The state layout used for compilation. Callers must serialize states
    /// using this layout before calling the compiled functions.
    pub state_layout: StateLayout,

    /// Compilation statistics.
    pub stats: LivenessCompileStats,

    /// Retains ownership of JIT modules whose code pages back the compiled
    /// function pointers. Previously leaked via std::mem::forget (#4082).
    _modules: Vec<JITModule>,
}

/// Statistics from liveness predicate compilation.
#[derive(Debug, Clone, Default)]
pub struct LivenessCompileStats {
    /// Number of state predicates eligible for compilation.
    pub state_eligible: usize,
    /// Number of state predicates successfully compiled.
    pub state_compiled: usize,
    /// Number of action predicates eligible for compilation.
    pub action_eligible: usize,
    /// Number of action predicates successfully compiled.
    pub action_compiled: usize,
    /// Number of predicates skipped (Enabled, StateChanged, compound types).
    pub skipped_ineligible: usize,
    /// Compilation time in microseconds.
    pub compile_time_us: u64,
}

impl CompiledLivenessBatch {
    /// Check if any predicates were compiled (worth using the compiled path).
    #[must_use]
    pub fn has_compiled_predicates(&self) -> bool {
        self.state_pred_fn.is_some() || self.action_pred_fn.is_some()
    }

    /// Check if ALL state predicates were compiled (no interpreter fallback needed).
    #[must_use]
    pub fn all_state_compiled(&self) -> bool {
        self.fallback_state_tags.is_empty()
    }

    /// Check if ALL action predicates were compiled (no interpreter fallback needed).
    #[must_use]
    pub fn all_action_compiled(&self) -> bool {
        self.fallback_action_tags.is_empty()
    }

    /// Evaluate compiled state predicates on a flattened state buffer.
    ///
    /// Returns a bitmask where bit `tag` is set if predicate with that tag
    /// evaluates to true. Only bits in `compiled_state_tags` are meaningful.
    ///
    /// # Safety
    ///
    /// `state_buf` must have length >= `state_layout.num_vars()`.
    #[must_use]
    pub unsafe fn eval_state_preds(&self, state_buf: &[i64]) -> u64 {
        match self.state_pred_fn {
            Some(f) => f(state_buf.as_ptr(), state_buf.len() as u32),
            None => 0,
        }
    }

    /// Evaluate compiled action predicates on a transition.
    ///
    /// Returns a bitmask where bit `tag` is set if predicate with that tag
    /// evaluates to true for the (current, next) transition. Only bits in
    /// `compiled_action_tags` are meaningful.
    ///
    /// # Safety
    ///
    /// Both buffers must have length >= `state_layout.num_vars()`.
    #[must_use]
    pub unsafe fn eval_action_preds(&self, current_buf: &[i64], next_buf: &[i64]) -> u64 {
        match self.action_pred_fn {
            Some(f) => f(
                current_buf.as_ptr(),
                next_buf.as_ptr(),
                current_buf.len() as u32,
            ),
            None => 0,
        }
    }
}

/// Information about a single liveness predicate to be compiled.
///
/// This is the interface between `tla-check` (which knows about `LiveExpr`)
/// and `tla-jit` (which compiles to Cranelift IR). The check crate extracts
/// predicate metadata and expressions, then passes them here for compilation.
#[derive(Debug, Clone)]
pub struct LivenessPredInfo {
    /// Unique tag for this predicate (bit position in the bitmask).
    pub tag: u32,
    /// Whether this is a state predicate (true) or action predicate (false).
    pub is_state_pred: bool,
    /// Index of the variable being compared, if this is a simple variable
    /// equality/comparison predicate. Used for direct register access in
    /// the compiled code.
    pub var_indices: Vec<u16>,
    /// The kind of predicate for compilation dispatch.
    pub kind: LivenessPredKind,
}

/// Kind of liveness predicate for compilation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LivenessPredKind {
    /// A scalar comparison: state[var_idx] <op> constant_value.
    /// This is the most common and most efficiently compiled case.
    ScalarComparison {
        /// Index of the state variable to read.
        var_idx: u16,
        /// The comparison operation.
        op: ScalarCompOp,
        /// The constant value to compare against.
        constant: i64,
    },
    /// A variable-to-variable comparison: state[lhs] <op> state[rhs].
    VarComparison {
        /// Index of the left-hand state variable.
        lhs_var_idx: u16,
        /// Index of the right-hand state variable.
        rhs_var_idx: u16,
        /// The comparison operation.
        op: ScalarCompOp,
    },
    /// State change check: current[var_idx] != next[var_idx].
    /// Only valid for action predicates.
    StateChangeCheck {
        /// Indices of variables to check for changes.
        var_indices: Vec<u16>,
    },
    /// A predicate that is not eligible for direct compilation.
    /// The tag is recorded so the caller knows to use interpreter fallback.
    NotEligible,
}

/// Scalar comparison operations supported in compiled predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarCompOp {
    /// Equal (=)
    Eq,
    /// Not equal (/=)
    Ne,
    /// Less than (<)
    Lt,
    /// Less than or equal (<=)
    Le,
    /// Greater than (>)
    Gt,
    /// Greater than or equal (>=)
    Ge,
}

/// Compile a batch of liveness predicates into native code.
///
/// This is the main entry point for liveness JIT compilation. It takes a list
/// of predicate descriptors and produces compiled batch functions.
///
/// Predicates marked `NotEligible` are tracked in the fallback lists so the
/// caller can use the interpreter for those specific tags.
///
/// # Errors
///
/// Returns `JitError` if Cranelift compilation fails. Predicates that cannot
/// be compiled are not errors -- they are tracked in the fallback lists.
pub fn compile_liveness_predicates(
    predicates: &[LivenessPredInfo],
    layout: &StateLayout,
) -> Result<CompiledLivenessBatch, JitError> {
    let start = std::time::Instant::now();

    let mut compiled_state_tags = Vec::new();
    let mut fallback_state_tags = Vec::new();
    let mut compiled_action_tags = Vec::new();
    let mut fallback_action_tags = Vec::new();

    let mut state_preds: Vec<&LivenessPredInfo> = Vec::new();
    let mut action_preds: Vec<&LivenessPredInfo> = Vec::new();
    let mut stats = LivenessCompileStats::default();

    for pred in predicates {
        if pred.tag >= 64 {
            stats.skipped_ineligible += 1;
            if pred.is_state_pred {
                fallback_state_tags.push(pred.tag);
            } else {
                fallback_action_tags.push(pred.tag);
            }
            continue;
        }

        match &pred.kind {
            LivenessPredKind::NotEligible => {
                stats.skipped_ineligible += 1;
                if pred.is_state_pred {
                    fallback_state_tags.push(pred.tag);
                } else {
                    fallback_action_tags.push(pred.tag);
                }
            }
            _ => {
                if pred.is_state_pred {
                    stats.state_eligible += 1;
                    state_preds.push(pred);
                } else {
                    stats.action_eligible += 1;
                    action_preds.push(pred);
                }
            }
        }
    }

    // Compile state predicate batch
    let mut modules = Vec::new();
    let state_pred_fn = if !state_preds.is_empty() {
        match compile_state_pred_batch(&state_preds, layout) {
            Ok((fn_ptr, module)) => {
                for pred in &state_preds {
                    compiled_state_tags.push(pred.tag);
                    stats.state_compiled += 1;
                }
                modules.push(module);
                Some(fn_ptr)
            }
            Err(_) => {
                // Compilation failed -- fall back to interpreter for all state preds
                for pred in &state_preds {
                    fallback_state_tags.push(pred.tag);
                }
                None
            }
        }
    } else {
        None
    };

    // Compile action predicate batch
    let action_pred_fn = if !action_preds.is_empty() {
        match compile_action_pred_batch(&action_preds, layout) {
            Ok((fn_ptr, module)) => {
                for pred in &action_preds {
                    compiled_action_tags.push(pred.tag);
                    stats.action_compiled += 1;
                }
                modules.push(module);
                Some(fn_ptr)
            }
            Err(_) => {
                for pred in &action_preds {
                    fallback_action_tags.push(pred.tag);
                }
                None
            }
        }
    } else {
        None
    };

    stats.compile_time_us = start.elapsed().as_micros() as u64;

    Ok(CompiledLivenessBatch {
        state_pred_fn,
        compiled_state_tags,
        fallback_state_tags,
        action_pred_fn,
        compiled_action_tags,
        fallback_action_tags,
        state_layout: layout.clone(),
        stats,
        _modules: modules,
    })
}

/// Compile a batch of state predicates into a single Cranelift function.
///
/// The generated function evaluates each predicate and OR's the result into
/// a u64 bitmask accumulator.
fn compile_state_pred_batch(
    preds: &[&LivenessPredInfo],
    layout: &StateLayout,
) -> Result<(CompiledStatePredBatchFn, JITModule), JitError> {
    use crate::jit_native::{Linkage, Module};
    use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName};
    use cranelift_codegen::Context;
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};

    let mut module = crate::create_jit_module()?;
    let pointer_type = module.target_config().pointer_type();

    // Define function signature: (state_ptr: i64*, state_len: u32) -> u64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(pointer_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I32)); // state_len
    sig.returns.push(AbiParam::new(types::I64)); // bitmask

    let func_id = module
        .declare_function("liveness_state_pred_batch", Linkage::Export, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let mut ctx = Context::new();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, 0);

    let mut fb_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);

    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    builder.seal_block(entry_block);

    let state_ptr = builder.block_params(entry_block)[0];
    let _state_len = builder.block_params(entry_block)[1];

    // Start with bitmask = 0
    let mut bitmask = builder.ins().iconst(types::I64, 0);

    for pred in preds {
        let pred_result = emit_state_pred_check(&mut builder, state_ptr, pred, layout)?;

        // Convert bool (i8) to i64 and shift to tag position
        let result_i64 = builder.ins().uextend(types::I64, pred_result);
        let shift = builder.ins().iconst(types::I64, pred.tag as i64);
        let shifted = builder.ins().ishl(result_i64, shift);
        bitmask = builder.ins().bor(bitmask, shifted);
    }

    builder.ins().return_(&[bitmask]);
    builder.finalize();

    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    module.clear_context(&mut ctx);
    module
        .finalize_definitions()
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let code_ptr = module.get_finalized_function(func_id);

    // SAFETY: The generated function follows the CompiledStatePredBatchFn ABI.
    // The module is returned to the caller who retains it so the code pages
    // stay valid. Previously leaked via std::mem::forget (#4082).
    debug_assert!(!code_ptr.is_null(), "compiled state pred batch code pointer is null");
    let fn_ptr: CompiledStatePredBatchFn = unsafe { std::mem::transmute(code_ptr) };
    Ok((fn_ptr, module))
}

/// Compile a batch of action predicates into a single Cranelift function.
fn compile_action_pred_batch(
    preds: &[&LivenessPredInfo],
    layout: &StateLayout,
) -> Result<(CompiledActionPredBatchFn, JITModule), JitError> {
    use crate::jit_native::{Linkage, Module};
    use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName};
    use cranelift_codegen::Context;
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};

    let mut module = crate::create_jit_module()?;
    let pointer_type = module.target_config().pointer_type();

    // Define function signature: (current_ptr, next_ptr, state_len) -> u64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(pointer_type)); // current_ptr
    sig.params.push(AbiParam::new(pointer_type)); // next_ptr
    sig.params.push(AbiParam::new(types::I32)); // state_len
    sig.returns.push(AbiParam::new(types::I64)); // bitmask

    let func_id = module
        .declare_function("liveness_action_pred_batch", Linkage::Export, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let mut ctx = Context::new();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, 1);

    let mut fb_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);

    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    builder.seal_block(entry_block);

    let current_ptr = builder.block_params(entry_block)[0];
    let next_ptr = builder.block_params(entry_block)[1];
    let _state_len = builder.block_params(entry_block)[2];

    let mut bitmask = builder.ins().iconst(types::I64, 0);

    for pred in preds {
        let pred_result =
            emit_action_pred_check(&mut builder, current_ptr, next_ptr, pred, layout)?;

        let result_i64 = builder.ins().uextend(types::I64, pred_result);
        let shift = builder.ins().iconst(types::I64, pred.tag as i64);
        let shifted = builder.ins().ishl(result_i64, shift);
        bitmask = builder.ins().bor(bitmask, shifted);
    }

    builder.ins().return_(&[bitmask]);
    builder.finalize();

    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    module.clear_context(&mut ctx);
    module
        .finalize_definitions()
        .map_err(|e| JitError::CompileError(e.to_string()))?;

    let code_ptr = module.get_finalized_function(func_id);

    // SAFETY: The generated function follows the CompiledActionPredBatchFn ABI.
    // The module is returned to the caller who retains it so the code pages
    // stay valid. Previously leaked via std::mem::forget (#4082).
    debug_assert!(!code_ptr.is_null(), "compiled action pred batch code pointer is null");
    let fn_ptr: CompiledActionPredBatchFn = unsafe { std::mem::transmute(code_ptr) };
    Ok((fn_ptr, module))
}

/// Emit Cranelift IR for a single state predicate check.
///
/// Returns a Cranelift value of type i8 (0 = false, 1 = true).
fn emit_state_pred_check(
    builder: &mut cranelift_frontend::FunctionBuilder,
    state_ptr: cranelift_codegen::ir::Value,
    pred: &LivenessPredInfo,
    _layout: &StateLayout,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::{types, InstBuilder, MemFlags};

    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // Load state[var_idx]
            let offset = (*var_idx as i32) * 8; // i64 = 8 bytes
            let var_val = builder
                .ins()
                .load(types::I64, MemFlags::trusted(), state_ptr, offset);
            let const_val = builder.ins().iconst(types::I64, *constant);
            let cmp_result = emit_scalar_cmp(builder, *op, var_val, const_val);
            Ok(cmp_result)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            let lhs_offset = (*lhs_var_idx as i32) * 8;
            let rhs_offset = (*rhs_var_idx as i32) * 8;
            let lhs_val =
                builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), state_ptr, lhs_offset);
            let rhs_val =
                builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), state_ptr, rhs_offset);
            let cmp_result = emit_scalar_cmp(builder, *op, lhs_val, rhs_val);
            Ok(cmp_result)
        }
        _ => {
            // NotEligible / StateChangeCheck on state pred -- return false
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(zero)
        }
    }
}

/// Emit Cranelift IR for a single action predicate check.
fn emit_action_pred_check(
    builder: &mut cranelift_frontend::FunctionBuilder,
    current_ptr: cranelift_codegen::ir::Value,
    next_ptr: cranelift_codegen::ir::Value,
    pred: &LivenessPredInfo,
    _layout: &StateLayout,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::{types, InstBuilder, MemFlags};

    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // For action preds comparing current state: load from current
            let offset = (*var_idx as i32) * 8;
            let var_val = builder
                .ins()
                .load(types::I64, MemFlags::trusted(), current_ptr, offset);
            let const_val = builder.ins().iconst(types::I64, *constant);
            let cmp_result = emit_scalar_cmp(builder, *op, var_val, const_val);
            Ok(cmp_result)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            // For action preds comparing variables within the same state
            let lhs_offset = (*lhs_var_idx as i32) * 8;
            let rhs_offset = (*rhs_var_idx as i32) * 8;
            let lhs_val =
                builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), current_ptr, lhs_offset);
            let rhs_val =
                builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), current_ptr, rhs_offset);
            let cmp_result = emit_scalar_cmp(builder, *op, lhs_val, rhs_val);
            Ok(cmp_result)
        }
        LivenessPredKind::StateChangeCheck { var_indices } => {
            // State change check: ANY variable changed between current and next
            if var_indices.is_empty() {
                // No variables to check -- return false
                let zero = builder.ins().iconst(types::I8, 0);
                return Ok(zero);
            }

            // Check if current[idx] != next[idx] for any idx in var_indices
            let mut any_changed = builder.ins().iconst(types::I8, 0);

            for &var_idx in var_indices {
                let offset = (var_idx as i32) * 8;
                let current_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), current_ptr, offset);
                let next_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), next_ptr, offset);
                let ne_result = builder.ins().icmp(
                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                    current_val,
                    next_val,
                );
                any_changed = builder.ins().bor(any_changed, ne_result);
            }

            Ok(any_changed)
        }
        LivenessPredKind::NotEligible => {
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(zero)
        }
    }
}

/// Emit a scalar comparison instruction.
fn emit_scalar_cmp(
    builder: &mut cranelift_frontend::FunctionBuilder,
    op: ScalarCompOp,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    use cranelift_codegen::ir::condcodes::IntCC;
    use cranelift_codegen::ir::InstBuilder;

    let cc = match op {
        ScalarCompOp::Eq => IntCC::Equal,
        ScalarCompOp::Ne => IntCC::NotEqual,
        ScalarCompOp::Lt => IntCC::SignedLessThan,
        ScalarCompOp::Le => IntCC::SignedLessThanOrEqual,
        ScalarCompOp::Gt => IntCC::SignedGreaterThan,
        ScalarCompOp::Ge => IntCC::SignedGreaterThanOrEqual,
    };

    builder.ins().icmp(cc, lhs, rhs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compound_layout::{StateLayout, VarLayout};

    fn make_test_layout(num_vars: usize) -> StateLayout {
        let vars: Vec<VarLayout> = (0..num_vars).map(|_| VarLayout::ScalarInt).collect();
        StateLayout::new(vars)
    }

    #[test]
    fn test_compile_empty_predicates() {
        let layout = make_test_layout(3);
        let batch =
            compile_liveness_predicates(&[], &layout).expect("empty predicates should compile");
        assert!(!batch.has_compiled_predicates());
        assert!(batch.all_state_compiled());
        assert!(batch.all_action_compiled());
    }

    #[test]
    fn test_compile_single_state_scalar_comparison() {
        let layout = make_test_layout(3);
        let preds = vec![LivenessPredInfo {
            tag: 1,
            is_state_pred: true,
            var_indices: vec![0],
            kind: LivenessPredKind::ScalarComparison {
                var_idx: 0,
                op: ScalarCompOp::Gt,
                constant: 5,
            },
        }];

        let batch =
            compile_liveness_predicates(&preds, &layout).expect("scalar comparison should compile");
        assert!(batch.has_compiled_predicates());
        assert!(batch.state_pred_fn.is_some());
        assert_eq!(batch.compiled_state_tags, vec![1]);
        assert!(batch.fallback_state_tags.is_empty());

        // Test evaluation: state = [10, 0, 0] -> var0 (10) > 5 -> true -> bit 1 set
        let state = [10i64, 0, 0];
        let result = unsafe { batch.eval_state_preds(&state) };
        assert_eq!(
            result & (1 << 1),
            1 << 1,
            "tag 1 should be true for var0=10 > 5"
        );

        // Test evaluation: state = [3, 0, 0] -> var0 (3) > 5 -> false -> bit 1 not set
        let state2 = [3i64, 0, 0];
        let result2 = unsafe { batch.eval_state_preds(&state2) };
        assert_eq!(
            result2 & (1 << 1),
            0,
            "tag 1 should be false for var0=3 > 5"
        );
    }

    #[test]
    fn test_compile_multiple_state_predicates() {
        let layout = make_test_layout(3);
        let preds = vec![
            LivenessPredInfo {
                tag: 0,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Eq,
                    constant: 42,
                },
            },
            LivenessPredInfo {
                tag: 2,
                is_state_pred: true,
                var_indices: vec![1],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 1,
                    op: ScalarCompOp::Lt,
                    constant: 100,
                },
            },
        ];

        let batch = compile_liveness_predicates(&preds, &layout)
            .expect("multiple predicates should compile");
        assert_eq!(batch.compiled_state_tags, vec![0, 2]);

        // state = [42, 50, 0] -> tag 0 true (42 == 42), tag 2 true (50 < 100)
        let state = [42i64, 50, 0];
        let result = unsafe { batch.eval_state_preds(&state) };
        assert_ne!(result & (1 << 0), 0, "tag 0 should be true");
        assert_ne!(result & (1 << 2), 0, "tag 2 should be true");

        // state = [43, 200, 0] -> tag 0 false (43 != 42), tag 2 false (200 >= 100)
        let state2 = [43i64, 200, 0];
        let result2 = unsafe { batch.eval_state_preds(&state2) };
        assert_eq!(result2 & (1 << 0), 0, "tag 0 should be false");
        assert_eq!(result2 & (1 << 2), 0, "tag 2 should be false");
    }

    #[test]
    fn test_compile_var_comparison() {
        let layout = make_test_layout(3);
        let preds = vec![LivenessPredInfo {
            tag: 3,
            is_state_pred: true,
            var_indices: vec![0, 1],
            kind: LivenessPredKind::VarComparison {
                lhs_var_idx: 0,
                rhs_var_idx: 1,
                op: ScalarCompOp::Eq,
            },
        }];

        let batch =
            compile_liveness_predicates(&preds, &layout).expect("var comparison should compile");

        // state = [7, 7, 0] -> var0 == var1 -> true
        let state = [7i64, 7, 0];
        let result = unsafe { batch.eval_state_preds(&state) };
        assert_ne!(result & (1 << 3), 0, "tag 3 should be true when vars equal");

        // state = [7, 8, 0] -> var0 != var1 -> false
        let state2 = [7i64, 8, 0];
        let result2 = unsafe { batch.eval_state_preds(&state2) };
        assert_eq!(
            result2 & (1 << 3),
            0,
            "tag 3 should be false when vars differ"
        );
    }

    #[test]
    fn test_compile_action_state_change_check() {
        let layout = make_test_layout(3);
        let preds = vec![LivenessPredInfo {
            tag: 5,
            is_state_pred: false,
            var_indices: vec![0, 1],
            kind: LivenessPredKind::StateChangeCheck {
                var_indices: vec![0, 1],
            },
        }];

        let batch = compile_liveness_predicates(&preds, &layout)
            .expect("state change check should compile");
        assert!(batch.action_pred_fn.is_some());
        assert_eq!(batch.compiled_action_tags, vec![5]);

        // current = [1, 2, 3], next = [1, 2, 3] -> no change -> false
        let current = [1i64, 2, 3];
        let next = [1i64, 2, 3];
        let result = unsafe { batch.eval_action_preds(&current, &next) };
        assert_eq!(result & (1 << 5), 0, "no change should be false");

        // current = [1, 2, 3], next = [1, 99, 3] -> var1 changed -> true
        let next2 = [1i64, 99, 3];
        let result2 = unsafe { batch.eval_action_preds(&current, &next2) };
        assert_ne!(result2 & (1 << 5), 0, "state change should be true");
    }

    #[test]
    fn test_mixed_eligible_and_ineligible() {
        let layout = make_test_layout(3);
        let preds = vec![
            LivenessPredInfo {
                tag: 1,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Gt,
                    constant: 0,
                },
            },
            LivenessPredInfo {
                tag: 2,
                is_state_pred: true,
                var_indices: vec![],
                kind: LivenessPredKind::NotEligible,
            },
        ];

        let batch =
            compile_liveness_predicates(&preds, &layout).expect("mixed predicates should compile");
        assert!(batch.has_compiled_predicates());
        assert_eq!(batch.compiled_state_tags, vec![1]);
        assert_eq!(batch.fallback_state_tags, vec![2]);
        assert!(!batch.all_state_compiled());
    }

    #[test]
    fn test_tag_over_63_rejected() {
        let layout = make_test_layout(3);
        let preds = vec![LivenessPredInfo {
            tag: 64,
            is_state_pred: true,
            var_indices: vec![0],
            kind: LivenessPredKind::ScalarComparison {
                var_idx: 0,
                op: ScalarCompOp::Eq,
                constant: 1,
            },
        }];

        let batch = compile_liveness_predicates(&preds, &layout)
            .expect("tag >= 64 should be skipped, not error");
        assert!(!batch.has_compiled_predicates());
        assert_eq!(batch.fallback_state_tags, vec![64]);
    }

    #[test]
    fn test_compile_stats() {
        let layout = make_test_layout(3);
        let preds = vec![
            LivenessPredInfo {
                tag: 0,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Eq,
                    constant: 1,
                },
            },
            LivenessPredInfo {
                tag: 1,
                is_state_pred: false,
                var_indices: vec![0],
                kind: LivenessPredKind::StateChangeCheck {
                    var_indices: vec![0],
                },
            },
            LivenessPredInfo {
                tag: 2,
                is_state_pred: true,
                var_indices: vec![],
                kind: LivenessPredKind::NotEligible,
            },
        ];

        let batch = compile_liveness_predicates(&preds, &layout).expect("should compile");
        assert_eq!(batch.stats.state_eligible, 1);
        assert_eq!(batch.stats.state_compiled, 1);
        assert_eq!(batch.stats.action_eligible, 1);
        assert_eq!(batch.stats.action_compiled, 1);
        assert_eq!(batch.stats.skipped_ineligible, 1);
        assert!(batch.stats.compile_time_us > 0 || batch.stats.compile_time_us == 0);
        // may be 0 on fast machines
    }

    #[test]
    fn test_empty_acceptance() {
        let helpers =
            CompiledSccHelpers::new(vec![], &[], &[]).expect("empty acceptance should build");
        assert!(helpers.acceptance_fn.is_none());
        assert!(helpers.check_node_acceptance(0));
        assert!(helpers.check_node_acceptance(u64::MAX));
    }

    #[test]
    fn test_single_promise_mask() {
        let helpers = CompiledSccHelpers::new(vec![0b0110], &[], &[])
            .expect("single promise mask should compile");
        assert!(helpers.acceptance_fn.is_some());
        assert!(helpers.check_node_acceptance(0b0010));
        assert!(helpers.check_node_acceptance(0b0100));
        assert!(!helpers.check_node_acceptance(0b1000));
    }

    #[test]
    fn test_multiple_promise_masks() {
        let helpers = CompiledSccHelpers::new(vec![0b0011, 0b1100], &[], &[])
            .expect("multiple promise masks should compile");
        assert!(helpers.check_node_acceptance(0b0101));
        assert!(!helpers.check_node_acceptance(0b0001));
        assert!(!helpers.check_node_acceptance(0b1000));
    }

    #[test]
    fn test_ae_state_mask_check() {
        let helpers =
            CompiledSccHelpers::new(vec![], &[1, 4], &[]).expect("AE state mask should compile");
        assert_eq!(helpers.ae_state_tag_mask, (1u64 << 1) | (1u64 << 4));
        assert!(helpers.check_node_acceptance(1u64 << 1));
        assert!(helpers.check_node_acceptance(1u64 << 4));
        assert!(!helpers.check_node_acceptance(0));
    }

    #[test]
    fn test_combined_acceptance_and_ae() {
        let helpers = CompiledSccHelpers::new(vec![1u64 << 0, 0b0110], &[4], &[6])
            .expect("combined acceptance masks should compile");
        let satisfying = (1u64 << 0) | (1u64 << 2) | (1u64 << 4) | (1u64 << 6);
        let missing_ae_action = (1u64 << 0) | (1u64 << 2) | (1u64 << 4);
        let missing_promise = (1u64 << 0) | (1u64 << 4) | (1u64 << 6);

        assert!(helpers.check_node_acceptance(satisfying));
        assert!(!helpers.check_node_acceptance(missing_ae_action));
        assert!(!helpers.check_node_acceptance(missing_promise));
    }
}
