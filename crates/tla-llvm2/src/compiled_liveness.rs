// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM2-compiled liveness predicate evaluation.
//!
//! This module takes [`LivenessPredInfo`] descriptors (defined in
//! `tla-jit-abi`) and compiles them through the tMIR/LLVM2 pipeline. The
//! resulting native code
//! implements the same ABI:
//!
//! - **State predicate batch:**
//!   `fn(state: *const i64, state_len: u32) -> u64`
//!
//! - **Action predicate batch:**
//!   `fn(current: *const i64, next: *const i64, state_len: u32) -> u64`
//!
//! Each bit in the returned u64 corresponds to one predicate tag being true.
//!
//! # Architecture
//!
//! ```text
//! LivenessPredInfo[] ──► build tMIR Module ──► compile_module_native()
//!                                                       │
//!     CompiledStatePredBatchFn ◄────────────────────────┘
//!     CompiledActionPredBatchFn ◄───────────────────────┘
//! ```
//!
//! The generated tMIR module contains one or two functions:
//! - `liveness_state_pred_batch` — evaluates all eligible state predicates
//! - `liveness_action_pred_batch` — evaluates all eligible action predicates
//!
//! Each function loads values from the state buffer via GEP, performs scalar
//! comparisons, assembles the bitmask via shifts and ORs, and returns.
//!
//! Part of #4198: Compiled liveness predicates via tMIR/LLVM2.

use crate::runtime_abi::compound_layout::StateLayout;
use crate::runtime_abi::liveness_types::{
    CompiledActionPredBatchFn, CompiledStatePredBatchFn, LivenessCompileStats, LivenessPredInfo,
    LivenessPredKind, ScalarCompOp,
};
use crate::Llvm2Error;
use std::fmt::Write;

/// Result of LLVM2-compiled liveness predicate batch.
///
/// Wraps LLVM2-compiled predicate batch function pointers with the same
/// bitmask ABI as the interpreter fallback path.
#[derive(Debug)]
pub struct Llvm2CompiledLivenessBatch {
    /// Compiled state predicate batch function pointer.
    pub state_pred_fn: Option<CompiledStatePredBatchFn>,

    /// Tags of state predicates successfully compiled.
    pub compiled_state_tags: Vec<u32>,

    /// Tags of state predicates that require interpreter fallback.
    pub fallback_state_tags: Vec<u32>,

    /// Compiled action predicate batch function pointer.
    pub action_pred_fn: Option<CompiledActionPredBatchFn>,

    /// Tags of action predicates successfully compiled.
    pub compiled_action_tags: Vec<u32>,

    /// Tags of action predicates that require interpreter fallback.
    pub fallback_action_tags: Vec<u32>,

    /// The state layout used for compilation.
    pub state_layout: StateLayout,

    /// Compilation statistics.
    pub stats: LivenessCompileStats,

    /// Retains ownership of the native library backing the function pointers.
    #[cfg(feature = "native")]
    _native_lib: Option<crate::compile::NativeLibrary>,
    #[cfg(not(feature = "native"))]
    _native_lib: Option<()>,
}

impl Llvm2CompiledLivenessBatch {
    /// Check if any predicates were compiled.
    #[must_use]
    pub fn has_compiled_predicates(&self) -> bool {
        self.state_pred_fn.is_some() || self.action_pred_fn.is_some()
    }

    /// Check if ALL state predicates were compiled.
    #[must_use]
    pub fn all_state_compiled(&self) -> bool {
        self.fallback_state_tags.is_empty()
    }

    /// Check if ALL action predicates were compiled.
    #[must_use]
    pub fn all_action_compiled(&self) -> bool {
        self.fallback_action_tags.is_empty()
    }

    /// Evaluate compiled state predicates on a flattened state buffer.
    ///
    /// # Safety
    ///
    /// `state_buf` must have length >= `state_layout.num_vars()`.
    #[must_use]
    pub unsafe fn eval_state_preds(&self, state_buf: &[i64]) -> u64 {
        match self.state_pred_fn {
            Some(f) => {
                crate::ensure_jit_execute_mode();
                f(state_buf.as_ptr(), state_buf.len() as u32)
            }
            None => 0,
        }
    }

    /// Evaluate compiled action predicates on a transition.
    ///
    /// # Safety
    ///
    /// Both buffers must have length >= `state_layout.num_vars()`.
    #[must_use]
    pub unsafe fn eval_action_preds(&self, current_buf: &[i64], next_buf: &[i64]) -> u64 {
        match self.action_pred_fn {
            Some(f) => {
                crate::ensure_jit_execute_mode();
                f(
                    current_buf.as_ptr(),
                    next_buf.as_ptr(),
                    current_buf.len() as u32,
                )
            }
            None => 0,
        }
    }
}

/// Compile liveness predicates via the LLVM2 pipeline.
///
/// Generates LLVM IR for the predicate batch functions and compiles them
/// to native code through the LLVM2 backend.
///
/// # Errors
///
/// Returns [`Llvm2Error`] if IR generation or native compilation fails.
/// Predicates that cannot be compiled are tracked in fallback lists (not errors).
pub fn compile_liveness_predicates_llvm2(
    predicates: &[LivenessPredInfo],
    layout: &StateLayout,
) -> Result<Llvm2CompiledLivenessBatch, Llvm2Error> {
    let start = std::time::Instant::now();

    let mut compiled_state_tags = Vec::new();
    let mut fallback_state_tags = Vec::new();
    let mut compiled_action_tags = Vec::new();
    let mut fallback_action_tags = Vec::new();

    let mut state_preds: Vec<&LivenessPredInfo> = Vec::new();
    let mut action_preds: Vec<&LivenessPredInfo> = Vec::new();
    let mut stats = LivenessCompileStats::default();

    // Classify predicates into compilable and fallback.
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

    // Generate LLVM IR text for both batch functions.
    let ir_text = generate_liveness_ir(&state_preds, &action_preds)?;

    // Attempt native compilation.
    let (state_pred_fn, action_pred_fn, native_lib) =
        compile_liveness_native(&ir_text, &state_preds, &action_preds)?;

    if state_pred_fn.is_some() {
        for pred in &state_preds {
            compiled_state_tags.push(pred.tag);
            stats.state_compiled += 1;
        }
    } else {
        for pred in &state_preds {
            fallback_state_tags.push(pred.tag);
        }
    }

    if action_pred_fn.is_some() {
        for pred in &action_preds {
            compiled_action_tags.push(pred.tag);
            stats.action_compiled += 1;
        }
    } else {
        for pred in &action_preds {
            fallback_action_tags.push(pred.tag);
        }
    }

    stats.compile_time_us = start.elapsed().as_micros() as u64;

    Ok(Llvm2CompiledLivenessBatch {
        state_pred_fn,
        compiled_state_tags,
        fallback_state_tags,
        action_pred_fn,
        compiled_action_tags,
        fallback_action_tags,
        state_layout: layout.clone(),
        stats,
        _native_lib: native_lib,
    })
}

/// Generate LLVM IR text for the liveness predicate batch functions.
///
/// Produces a complete LLVM module with up to two functions:
/// - `liveness_state_pred_batch(state: ptr, state_len: i32) -> i64`
/// - `liveness_action_pred_batch(current: ptr, next: ptr, state_len: i32) -> i64`
fn generate_liveness_ir(
    state_preds: &[&LivenessPredInfo],
    action_preds: &[&LivenessPredInfo],
) -> Result<String, Llvm2Error> {
    let mut ir = String::with_capacity(4096);

    // Module header.
    writeln!(ir, "; ModuleID = 'liveness_predicates'")
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir, "source_filename = \"liveness_predicates\"")
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(
        ir,
        "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
    )
    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir).map_err(|e| Llvm2Error::Emission(e.to_string()))?;

    // Emit state predicate batch function.
    if !state_preds.is_empty() {
        emit_state_pred_batch_fn(&mut ir, state_preds)?;
        writeln!(ir).map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    }

    // Emit action predicate batch function.
    if !action_preds.is_empty() {
        emit_action_pred_batch_fn(&mut ir, action_preds)?;
        writeln!(ir).map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    }

    Ok(ir)
}

/// Emit LLVM IR for the state predicate batch function.
///
/// Signature: `define i64 @liveness_state_pred_batch(ptr %state, i32 %state_len)`
///
/// The function loads state variables via GEP, performs scalar comparisons,
/// and assembles the bitmask by shifting and OR-ing the results.
fn emit_state_pred_batch_fn(
    ir: &mut String,
    preds: &[&LivenessPredInfo],
) -> Result<(), Llvm2Error> {
    writeln!(
        ir,
        "define i64 @liveness_state_pred_batch(ptr %state, i32 %state_len) {{"
    )
    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir, "entry:").map_err(|e| Llvm2Error::Emission(e.to_string()))?;

    let mut reg_counter = 0u32;
    let mut bitmask_reg = alloc_reg(&mut reg_counter);

    // Start with bitmask = 0.
    writeln!(ir, "  {bitmask_reg} = add i64 0, 0")
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

    for pred in preds {
        let pred_result_reg = emit_state_pred_check(ir, &mut reg_counter, pred, "%state")?;

        // Convert i1 result to i64, shift to tag position, OR into bitmask.
        let ext_reg = alloc_reg(&mut reg_counter);
        writeln!(ir, "  {ext_reg} = zext i1 {pred_result_reg} to i64")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        let shifted_reg = alloc_reg(&mut reg_counter);
        writeln!(ir, "  {shifted_reg} = shl i64 {ext_reg}, {}", pred.tag)
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        let new_bitmask_reg = alloc_reg(&mut reg_counter);
        writeln!(
            ir,
            "  {new_bitmask_reg} = or i64 {bitmask_reg}, {shifted_reg}"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        bitmask_reg = new_bitmask_reg;
    }

    writeln!(ir, "  ret i64 {bitmask_reg}").map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir, "}}").map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    Ok(())
}

/// Emit LLVM IR for the action predicate batch function.
///
/// Signature: `define i64 @liveness_action_pred_batch(ptr %current, ptr %next, i32 %state_len)`
fn emit_action_pred_batch_fn(
    ir: &mut String,
    preds: &[&LivenessPredInfo],
) -> Result<(), Llvm2Error> {
    writeln!(
        ir,
        "define i64 @liveness_action_pred_batch(ptr %current, ptr %next, i32 %state_len) {{"
    )
    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir, "entry:").map_err(|e| Llvm2Error::Emission(e.to_string()))?;

    let mut reg_counter = 0u32;
    let mut bitmask_reg = alloc_reg(&mut reg_counter);

    // Start with bitmask = 0.
    writeln!(ir, "  {bitmask_reg} = add i64 0, 0")
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

    for pred in preds {
        let pred_result_reg =
            emit_action_pred_check(ir, &mut reg_counter, pred, "%current", "%next")?;

        let ext_reg = alloc_reg(&mut reg_counter);
        writeln!(ir, "  {ext_reg} = zext i1 {pred_result_reg} to i64")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        let shifted_reg = alloc_reg(&mut reg_counter);
        writeln!(ir, "  {shifted_reg} = shl i64 {ext_reg}, {}", pred.tag)
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        let new_bitmask_reg = alloc_reg(&mut reg_counter);
        writeln!(
            ir,
            "  {new_bitmask_reg} = or i64 {bitmask_reg}, {shifted_reg}"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        bitmask_reg = new_bitmask_reg;
    }

    writeln!(ir, "  ret i64 {bitmask_reg}").map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    writeln!(ir, "}}").map_err(|e| Llvm2Error::Emission(e.to_string()))?;
    Ok(())
}

/// Emit LLVM IR for a single state predicate check.
///
/// Returns the register name holding the i1 result (true/false).
fn emit_state_pred_check(
    ir: &mut String,
    reg_counter: &mut u32,
    pred: &LivenessPredInfo,
    state_ptr: &str,
) -> Result<String, Llvm2Error> {
    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // Load state[var_idx].
            let gep_reg = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {gep_reg} = getelementptr i64, ptr {state_ptr}, i64 {var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let val_reg = alloc_reg(reg_counter);
            writeln!(ir, "  {val_reg} = load i64, ptr {gep_reg}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            // Compare against constant.
            let cmp_reg = alloc_reg(reg_counter);
            let cond = scalar_comp_to_llvm(*op);
            writeln!(ir, "  {cmp_reg} = icmp {cond} i64 {val_reg}, {constant}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            Ok(cmp_reg)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            // Load state[lhs_var_idx].
            let lhs_gep = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {lhs_gep} = getelementptr i64, ptr {state_ptr}, i64 {lhs_var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let lhs_val = alloc_reg(reg_counter);
            writeln!(ir, "  {lhs_val} = load i64, ptr {lhs_gep}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            // Load state[rhs_var_idx].
            let rhs_gep = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {rhs_gep} = getelementptr i64, ptr {state_ptr}, i64 {rhs_var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let rhs_val = alloc_reg(reg_counter);
            writeln!(ir, "  {rhs_val} = load i64, ptr {rhs_gep}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            // Compare.
            let cmp_reg = alloc_reg(reg_counter);
            let cond = scalar_comp_to_llvm(*op);
            writeln!(ir, "  {cmp_reg} = icmp {cond} i64 {lhs_val}, {rhs_val}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            Ok(cmp_reg)
        }
        _ => {
            // NotEligible or StateChangeCheck on state pred -- return false (i1 0).
            let reg = alloc_reg(reg_counter);
            writeln!(ir, "  {reg} = icmp eq i64 0, 1")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
            Ok(reg)
        }
    }
}

/// Emit LLVM IR for a single action predicate check.
///
/// Returns the register name holding the i1 result.
fn emit_action_pred_check(
    ir: &mut String,
    reg_counter: &mut u32,
    pred: &LivenessPredInfo,
    current_ptr: &str,
    next_ptr: &str,
) -> Result<String, Llvm2Error> {
    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // Load current[var_idx].
            let gep_reg = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {gep_reg} = getelementptr i64, ptr {current_ptr}, i64 {var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let val_reg = alloc_reg(reg_counter);
            writeln!(ir, "  {val_reg} = load i64, ptr {gep_reg}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let cmp_reg = alloc_reg(reg_counter);
            let cond = scalar_comp_to_llvm(*op);
            writeln!(ir, "  {cmp_reg} = icmp {cond} i64 {val_reg}, {constant}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            Ok(cmp_reg)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            // Load current[lhs].
            let lhs_gep = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {lhs_gep} = getelementptr i64, ptr {current_ptr}, i64 {lhs_var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let lhs_val = alloc_reg(reg_counter);
            writeln!(ir, "  {lhs_val} = load i64, ptr {lhs_gep}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            // Load current[rhs].
            let rhs_gep = alloc_reg(reg_counter);
            writeln!(
                ir,
                "  {rhs_gep} = getelementptr i64, ptr {current_ptr}, i64 {rhs_var_idx}"
            )
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let rhs_val = alloc_reg(reg_counter);
            writeln!(ir, "  {rhs_val} = load i64, ptr {rhs_gep}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            let cmp_reg = alloc_reg(reg_counter);
            let cond = scalar_comp_to_llvm(*op);
            writeln!(ir, "  {cmp_reg} = icmp {cond} i64 {lhs_val}, {rhs_val}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

            Ok(cmp_reg)
        }
        LivenessPredKind::StateChangeCheck { var_indices } => {
            if var_indices.is_empty() {
                // No variables to check -- return false.
                let reg = alloc_reg(reg_counter);
                writeln!(ir, "  {reg} = icmp eq i64 0, 1")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                return Ok(reg);
            }

            // Check if ANY variable changed: current[idx] != next[idx].
            let mut any_changed_reg: Option<String> = None;

            for &var_idx in var_indices {
                // Load current[var_idx].
                let cur_gep = alloc_reg(reg_counter);
                writeln!(
                    ir,
                    "  {cur_gep} = getelementptr i64, ptr {current_ptr}, i64 {var_idx}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                let cur_val = alloc_reg(reg_counter);
                writeln!(ir, "  {cur_val} = load i64, ptr {cur_gep}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                // Load next[var_idx].
                let nxt_gep = alloc_reg(reg_counter);
                writeln!(
                    ir,
                    "  {nxt_gep} = getelementptr i64, ptr {next_ptr}, i64 {var_idx}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                let nxt_val = alloc_reg(reg_counter);
                writeln!(ir, "  {nxt_val} = load i64, ptr {nxt_gep}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                // Compare: current != next.
                let ne_reg = alloc_reg(reg_counter);
                writeln!(ir, "  {ne_reg} = icmp ne i64 {cur_val}, {nxt_val}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                // OR with accumulated result.
                match &any_changed_reg {
                    None => {
                        any_changed_reg = Some(ne_reg);
                    }
                    Some(prev) => {
                        let or_reg = alloc_reg(reg_counter);
                        writeln!(ir, "  {or_reg} = or i1 {prev}, {ne_reg}")
                            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                        any_changed_reg = Some(or_reg);
                    }
                }
            }

            Ok(any_changed_reg.expect("invariant: var_indices is non-empty"))
        }
        LivenessPredKind::NotEligible => {
            let reg = alloc_reg(reg_counter);
            writeln!(ir, "  {reg} = icmp eq i64 0, 1")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
            Ok(reg)
        }
    }
}

/// Allocate a new SSA register name (%N).
fn alloc_reg(counter: &mut u32) -> String {
    let reg = format!("%{counter}");
    *counter += 1;
    reg
}

/// Map a `ScalarCompOp` to its LLVM IR `icmp` condition code.
fn scalar_comp_to_llvm(op: ScalarCompOp) -> &'static str {
    match op {
        ScalarCompOp::Eq => "eq",
        ScalarCompOp::Ne => "ne",
        ScalarCompOp::Lt => "slt",
        ScalarCompOp::Le => "sle",
        ScalarCompOp::Gt => "sgt",
        ScalarCompOp::Ge => "sge",
    }
}

/// Attempt native compilation of the liveness IR through LLVM2.
///
/// When the `native` feature is enabled, compiles the IR and looks up the
/// function symbols. When disabled, returns (None, None, None) gracefully.
#[cfg(feature = "native")]
fn compile_liveness_native(
    _ir_text: &str,
    state_preds: &[&LivenessPredInfo],
    action_preds: &[&LivenessPredInfo],
) -> Result<
    (
        Option<CompiledStatePredBatchFn>,
        Option<CompiledActionPredBatchFn>,
        Option<crate::compile::NativeLibrary>,
    ),
    Llvm2Error,
> {
    if state_preds.is_empty() && action_preds.is_empty() {
        return Ok((None, None, None));
    }

    // Compile through LLVM2 native pipeline.
    // Since compile_and_link is deprecated, we build a tMIR module and use
    // the direct pipeline. However, our liveness IR is hand-generated LLVM IR
    // text which does not go through tMIR. We use the text path for now.
    //
    // The LLVM2 compile_and_link API redirects to compile_module_native which
    // expects a tMIR module. For liveness, we generate the tMIR module
    // programmatically instead.
    let module = build_liveness_tmir_module(state_preds, action_preds)?;
    let native_lib = crate::compile::compile_module_native(&module, crate::compile::OptLevel::O1)?;

    let state_pred_fn = if !state_preds.is_empty() {
        // SAFETY: The generated function matches CompiledStatePredBatchFn ABI.
        let ptr = unsafe { native_lib.get_symbol("liveness_state_pred_batch")? };
        Some(unsafe { std::mem::transmute::<*mut std::ffi::c_void, CompiledStatePredBatchFn>(ptr) })
    } else {
        None
    };

    let action_pred_fn = if !action_preds.is_empty() {
        // SAFETY: The generated function matches CompiledActionPredBatchFn ABI.
        let ptr = unsafe { native_lib.get_symbol("liveness_action_pred_batch")? };
        Some(unsafe {
            std::mem::transmute::<*mut std::ffi::c_void, CompiledActionPredBatchFn>(ptr)
        })
    } else {
        None
    };

    Ok((state_pred_fn, action_pred_fn, Some(native_lib)))
}

#[cfg(not(feature = "native"))]
fn compile_liveness_native(
    _ir_text: &str,
    _state_preds: &[&LivenessPredInfo],
    _action_preds: &[&LivenessPredInfo],
) -> Result<
    (
        Option<CompiledStatePredBatchFn>,
        Option<CompiledActionPredBatchFn>,
        Option<()>,
    ),
    Llvm2Error,
> {
    Ok((None, None, None))
}

/// Build a tMIR module representing the liveness predicate batch functions.
///
/// This generates tMIR instructions programmatically to implement the same
/// logic as the LLVM IR text generation above, but going through the proper
/// tMIR -> LLVM2 pipeline for native compilation.
#[cfg(feature = "native")]
fn build_liveness_tmir_module(
    state_preds: &[&LivenessPredInfo],
    action_preds: &[&LivenessPredInfo],
) -> Result<tmir::Module, Llvm2Error> {
    use tmir::constant::Constant;
    use tmir::inst::{BinOp, CastOp, Inst};
    use tmir::ty::{FuncTy, Ty};
    use tmir::value::{BlockId, FuncId, ValueId};
    use tmir::{Block, Function, InstrNode, Module};

    let mut module = Module::new("liveness_predicates");
    let mut func_id_counter = 0u32;

    // State predicate batch function.
    if !state_preds.is_empty() {
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let entry_block_id = BlockId::new(0);
        let mut func = Function::new(
            FuncId::new(func_id_counter),
            "liveness_state_pred_batch",
            ft,
            entry_block_id,
        );
        func_id_counter += 1;

        let mut block = Block::new(entry_block_id);
        let mut val_counter = 0u32;

        // Parameters: %0 = state_ptr, %1 = state_len.
        let state_ptr_val = ValueId::new(val_counter);
        val_counter += 1;
        let _state_len_val = ValueId::new(val_counter);
        val_counter += 1;

        // Initialize bitmask to 0.
        let bitmask_init = ValueId::new(val_counter);
        val_counter += 1;
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0i128),
            })
            .with_result(bitmask_init),
        );

        let mut current_bitmask = bitmask_init;

        for pred in state_preds {
            let (pred_result, new_val_counter) =
                emit_tmir_state_pred_check(&mut block, val_counter, pred, state_ptr_val);
            val_counter = new_val_counter;

            // Zero-extend i1 to i64.
            let ext_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: pred_result,
                })
                .with_result(ext_val),
            );

            // Shift left by tag.
            let shift_amount = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(pred.tag as i128),
                })
                .with_result(shift_amount),
            );

            let shifted = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Shl,
                    lhs: ext_val,
                    rhs: shift_amount,
                    ty: Ty::I64,
                })
                .with_result(shifted),
            );

            // OR into bitmask.
            let new_bitmask = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    lhs: current_bitmask,
                    rhs: shifted,
                    ty: Ty::I64,
                })
                .with_result(new_bitmask),
            );

            current_bitmask = new_bitmask;
        }

        // Return the bitmask.
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![current_bitmask],
        }));

        func.blocks.push(block);
        module.add_function(func);
    }

    // Action predicate batch function.
    if !action_preds.is_empty() {
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let entry_block_id = BlockId::new(0);
        let mut func = Function::new(
            FuncId::new(func_id_counter),
            "liveness_action_pred_batch",
            ft,
            entry_block_id,
        );
        #[allow(unused_assignments)]
        {
            func_id_counter += 1;
        }

        let mut block = Block::new(entry_block_id);
        let mut val_counter = 0u32;

        // Parameters: %0 = current_ptr, %1 = next_ptr, %2 = state_len.
        let current_ptr_val = ValueId::new(val_counter);
        val_counter += 1;
        let next_ptr_val = ValueId::new(val_counter);
        val_counter += 1;
        let _state_len_val = ValueId::new(val_counter);
        val_counter += 1;

        // Initialize bitmask to 0.
        let bitmask_init = ValueId::new(val_counter);
        val_counter += 1;
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0i128),
            })
            .with_result(bitmask_init),
        );

        let mut current_bitmask = bitmask_init;

        for pred in action_preds {
            let (pred_result, new_val_counter) = emit_tmir_action_pred_check(
                &mut block,
                val_counter,
                pred,
                current_ptr_val,
                next_ptr_val,
            );
            val_counter = new_val_counter;

            // Zero-extend i1 to i64.
            let ext_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: pred_result,
                })
                .with_result(ext_val),
            );

            // Shift left by tag.
            let shift_amount = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(pred.tag as i128),
                })
                .with_result(shift_amount),
            );

            let shifted = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Shl,
                    lhs: ext_val,
                    rhs: shift_amount,
                    ty: Ty::I64,
                })
                .with_result(shifted),
            );

            // OR into bitmask.
            let new_bitmask = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    lhs: current_bitmask,
                    rhs: shifted,
                    ty: Ty::I64,
                })
                .with_result(new_bitmask),
            );

            current_bitmask = new_bitmask;
        }

        block.body.push(InstrNode::new(Inst::Return {
            values: vec![current_bitmask],
        }));

        func.blocks.push(block);
        module.add_function(func);
    }

    Ok(module)
}

/// Emit tMIR instructions for a single state predicate check.
///
/// Returns (result_value_id, updated_val_counter).
#[cfg(feature = "native")]
fn emit_tmir_state_pred_check(
    block: &mut tmir::Block,
    mut val_counter: u32,
    pred: &LivenessPredInfo,
    state_ptr: tmir::value::ValueId,
) -> (tmir::value::ValueId, u32) {
    use tmir::constant::Constant;
    use tmir::inst::Inst;
    use tmir::ty::Ty;
    use tmir::value::ValueId;
    use tmir::InstrNode;

    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // GEP: ptr to state[var_idx].
            let idx_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*var_idx as i128),
                })
                .with_result(idx_val),
            );

            let gep_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: state_ptr,
                    indices: vec![idx_val],
                })
                .with_result(gep_val),
            );

            // Load i64.
            let load_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: gep_val,
                    align: None,
                    volatile: false,
                })
                .with_result(load_val),
            );

            // Constant value.
            let const_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*constant as i128),
                })
                .with_result(const_val),
            );

            // Compare.
            let cmp_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: scalar_comp_to_tmir(*op),
                    lhs: load_val,
                    rhs: const_val,
                    ty: Ty::I64,
                })
                .with_result(cmp_val),
            );

            (cmp_val, val_counter)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            // Load lhs.
            let lhs_idx = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*lhs_var_idx as i128),
                })
                .with_result(lhs_idx),
            );

            let lhs_gep = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: state_ptr,
                    indices: vec![lhs_idx],
                })
                .with_result(lhs_gep),
            );

            let lhs_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: lhs_gep,
                    align: None,
                    volatile: false,
                })
                .with_result(lhs_val),
            );

            // Load rhs.
            let rhs_idx = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*rhs_var_idx as i128),
                })
                .with_result(rhs_idx),
            );

            let rhs_gep = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: state_ptr,
                    indices: vec![rhs_idx],
                })
                .with_result(rhs_gep),
            );

            let rhs_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: rhs_gep,
                    align: None,
                    volatile: false,
                })
                .with_result(rhs_val),
            );

            // Compare.
            let cmp_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: scalar_comp_to_tmir(*op),
                    lhs: lhs_val,
                    rhs: rhs_val,
                    ty: Ty::I64,
                })
                .with_result(cmp_val),
            );

            (cmp_val, val_counter)
        }
        _ => {
            // Return constant false (i1 0).
            let zero = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(zero),
            );
            (zero, val_counter)
        }
    }
}

/// Emit tMIR instructions for a single action predicate check.
#[cfg(feature = "native")]
fn emit_tmir_action_pred_check(
    block: &mut tmir::Block,
    mut val_counter: u32,
    pred: &LivenessPredInfo,
    current_ptr: tmir::value::ValueId,
    next_ptr: tmir::value::ValueId,
) -> (tmir::value::ValueId, u32) {
    use tmir::constant::Constant;
    use tmir::inst::{BinOp, ICmpOp, Inst};
    use tmir::ty::Ty;
    use tmir::value::ValueId;
    use tmir::InstrNode;

    match &pred.kind {
        LivenessPredKind::ScalarComparison {
            var_idx,
            op,
            constant,
        } => {
            // Load current[var_idx].
            let idx_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*var_idx as i128),
                })
                .with_result(idx_val),
            );

            let gep_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: current_ptr,
                    indices: vec![idx_val],
                })
                .with_result(gep_val),
            );

            let load_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: gep_val,
                    align: None,
                    volatile: false,
                })
                .with_result(load_val),
            );

            let const_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*constant as i128),
                })
                .with_result(const_val),
            );

            let cmp_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: scalar_comp_to_tmir(*op),
                    lhs: load_val,
                    rhs: const_val,
                    ty: Ty::I64,
                })
                .with_result(cmp_val),
            );

            (cmp_val, val_counter)
        }
        LivenessPredKind::VarComparison {
            lhs_var_idx,
            rhs_var_idx,
            op,
        } => {
            // Load current[lhs], current[rhs].
            let lhs_idx = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*lhs_var_idx as i128),
                })
                .with_result(lhs_idx),
            );

            let lhs_gep = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: current_ptr,
                    indices: vec![lhs_idx],
                })
                .with_result(lhs_gep),
            );

            let lhs_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: lhs_gep,
                    align: None,
                    volatile: false,
                })
                .with_result(lhs_val),
            );

            let rhs_idx = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(*rhs_var_idx as i128),
                })
                .with_result(rhs_idx),
            );

            let rhs_gep = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: current_ptr,
                    indices: vec![rhs_idx],
                })
                .with_result(rhs_gep),
            );

            let rhs_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: rhs_gep,
                    align: None,
                    volatile: false,
                })
                .with_result(rhs_val),
            );

            let cmp_val = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: scalar_comp_to_tmir(*op),
                    lhs: lhs_val,
                    rhs: rhs_val,
                    ty: Ty::I64,
                })
                .with_result(cmp_val),
            );

            (cmp_val, val_counter)
        }
        LivenessPredKind::StateChangeCheck { var_indices } => {
            if var_indices.is_empty() {
                let zero = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    })
                    .with_result(zero),
                );
                return (zero, val_counter);
            }

            let mut any_changed: Option<ValueId> = None;

            for &var_idx in var_indices {
                // Load current[var_idx].
                let idx_val = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(var_idx as i128),
                    })
                    .with_result(idx_val),
                );

                let cur_gep = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I64,
                        base: current_ptr,
                        indices: vec![idx_val],
                    })
                    .with_result(cur_gep),
                );

                let cur_val = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::Load {
                        ty: Ty::I64,
                        ptr: cur_gep,
                        align: None,
                        volatile: false,
                    })
                    .with_result(cur_val),
                );

                // Load next[var_idx] - reuse same idx_val for next GEP.
                let nxt_gep = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I64,
                        base: next_ptr,
                        indices: vec![idx_val],
                    })
                    .with_result(nxt_gep),
                );

                let nxt_val = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::Load {
                        ty: Ty::I64,
                        ptr: nxt_gep,
                        align: None,
                        volatile: false,
                    })
                    .with_result(nxt_val),
                );

                // Compare ne.
                let ne_val = ValueId::new(val_counter);
                val_counter += 1;
                block.body.push(
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Ne,
                        lhs: cur_val,
                        rhs: nxt_val,
                        ty: Ty::I64,
                    })
                    .with_result(ne_val),
                );

                match any_changed {
                    None => {
                        any_changed = Some(ne_val);
                    }
                    Some(prev) => {
                        let or_val = ValueId::new(val_counter);
                        val_counter += 1;
                        block.body.push(
                            InstrNode::new(Inst::BinOp {
                                op: BinOp::Or,
                                lhs: prev,
                                rhs: ne_val,
                                ty: Ty::Bool,
                            })
                            .with_result(or_val),
                        );
                        any_changed = Some(or_val);
                    }
                }
            }

            (
                any_changed.expect("invariant: var_indices is non-empty"),
                val_counter,
            )
        }
        LivenessPredKind::NotEligible => {
            let zero = ValueId::new(val_counter);
            val_counter += 1;
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(zero),
            );
            (zero, val_counter)
        }
    }
}

/// Map `ScalarCompOp` to tMIR `ICmpOp`.
#[cfg(feature = "native")]
fn scalar_comp_to_tmir(op: ScalarCompOp) -> tmir::inst::ICmpOp {
    use tmir::inst::ICmpOp;
    match op {
        ScalarCompOp::Eq => ICmpOp::Eq,
        ScalarCompOp::Ne => ICmpOp::Ne,
        ScalarCompOp::Lt => ICmpOp::Slt,
        ScalarCompOp::Le => ICmpOp::Sle,
        ScalarCompOp::Gt => ICmpOp::Sgt,
        ScalarCompOp::Ge => ICmpOp::Sge,
    }
}

/// Generate the LLVM IR text for a liveness batch (exposed for testing/debugging).
///
/// This is the IR text generation path, useful when the native feature is not
/// available or for debugging the generated IR.
pub fn generate_liveness_ir_text(predicates: &[LivenessPredInfo]) -> Result<String, Llvm2Error> {
    let mut state_preds: Vec<&LivenessPredInfo> = Vec::new();
    let mut action_preds: Vec<&LivenessPredInfo> = Vec::new();

    for pred in predicates {
        if pred.tag >= 64 {
            continue;
        }
        match &pred.kind {
            LivenessPredKind::NotEligible => continue,
            _ => {
                if pred.is_state_pred {
                    state_preds.push(pred);
                } else {
                    action_preds.push(pred);
                }
            }
        }
    }

    generate_liveness_ir(&state_preds, &action_preds)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime_abi::compound_layout::{StateLayout, VarLayout};
    use crate::runtime_abi::liveness_types::{LivenessPredInfo, LivenessPredKind, ScalarCompOp};

    fn make_test_layout(num_vars: usize) -> StateLayout {
        let vars: Vec<VarLayout> = (0..num_vars).map(|_| VarLayout::ScalarInt).collect();
        StateLayout::new(vars)
    }

    #[test]
    fn test_generate_ir_empty_predicates() {
        let ir = generate_liveness_ir_text(&[]).expect("empty should succeed");
        assert!(ir.contains("ModuleID"));
        // No function definitions for empty predicates.
        assert!(!ir.contains("define"));
    }

    #[test]
    fn test_generate_ir_single_state_pred() {
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

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        assert!(ir.contains("define i64 @liveness_state_pred_batch"));
        assert!(ir.contains("getelementptr i64"));
        assert!(ir.contains("icmp sgt"));
        assert!(ir.contains("shl i64"));
        assert!(ir.contains("ret i64"));
    }

    #[test]
    fn test_generate_ir_action_pred_state_change() {
        let preds = vec![LivenessPredInfo {
            tag: 3,
            is_state_pred: false,
            var_indices: vec![0, 1],
            kind: LivenessPredKind::StateChangeCheck {
                var_indices: vec![0, 1],
            },
        }];

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        assert!(ir.contains("define i64 @liveness_action_pred_batch"));
        assert!(ir.contains("icmp ne"));
        assert!(ir.contains("or i1"));
    }

    #[test]
    fn test_generate_ir_var_comparison() {
        let preds = vec![LivenessPredInfo {
            tag: 2,
            is_state_pred: true,
            var_indices: vec![0, 1],
            kind: LivenessPredKind::VarComparison {
                lhs_var_idx: 0,
                rhs_var_idx: 1,
                op: ScalarCompOp::Eq,
            },
        }];

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        assert!(ir.contains("icmp eq i64"));
        // Should load two different variables.
        let gep_count = ir.matches("getelementptr i64").count();
        assert_eq!(gep_count, 2, "VarComparison needs 2 GEPs");
    }

    #[test]
    fn test_generate_ir_mixed_state_and_action() {
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
                tag: 1,
                is_state_pred: false,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Lt,
                    constant: 100,
                },
            },
        ];

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        assert!(ir.contains("@liveness_state_pred_batch"));
        assert!(ir.contains("@liveness_action_pred_batch"));
    }

    #[test]
    fn test_generate_ir_not_eligible_skipped() {
        let preds = vec![
            LivenessPredInfo {
                tag: 0,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Gt,
                    constant: 0,
                },
            },
            LivenessPredInfo {
                tag: 1,
                is_state_pred: true,
                var_indices: vec![],
                kind: LivenessPredKind::NotEligible,
            },
        ];

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        // Only one predicate should be in the IR (tag 0).
        assert!(ir.contains("shl i64"));
        // The shift should be for tag 0 only.
        assert!(ir.contains("shl i64 %"), "should have shift for tag 0");
    }

    #[test]
    fn test_generate_ir_tag_over_63_skipped() {
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

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        assert!(
            !ir.contains("define"),
            "tag >= 64 should be skipped entirely"
        );
    }

    #[test]
    fn test_compile_batch_empty() {
        let layout = make_test_layout(3);
        let batch = compile_liveness_predicates_llvm2(&[], &layout).expect("empty should succeed");
        assert!(!batch.has_compiled_predicates());
        assert!(batch.all_state_compiled());
        assert!(batch.all_action_compiled());
    }

    #[test]
    fn test_compile_batch_classifies_ineligible() {
        let layout = make_test_layout(3);
        let preds = vec![
            LivenessPredInfo {
                tag: 0,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Gt,
                    constant: 0,
                },
            },
            LivenessPredInfo {
                tag: 1,
                is_state_pred: true,
                var_indices: vec![],
                kind: LivenessPredKind::NotEligible,
            },
            LivenessPredInfo {
                tag: 64,
                is_state_pred: false,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Eq,
                    constant: 1,
                },
            },
        ];

        let batch = compile_liveness_predicates_llvm2(&preds, &layout).expect("should classify");

        // Tag 1 is NotEligible, tag 64 exceeds bitmask.
        assert!(batch.fallback_state_tags.contains(&1));
        assert!(batch.fallback_action_tags.contains(&64));
        assert_eq!(batch.stats.skipped_ineligible, 2);
        assert_eq!(batch.stats.state_eligible, 1);
    }

    #[test]
    fn test_scalar_comp_to_llvm_mapping() {
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Eq), "eq");
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Ne), "ne");
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Lt), "slt");
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Le), "sle");
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Gt), "sgt");
        assert_eq!(scalar_comp_to_llvm(ScalarCompOp::Ge), "sge");
    }

    #[test]
    fn test_generate_ir_multiple_state_preds_bitmask_assembly() {
        let preds = vec![
            LivenessPredInfo {
                tag: 0,
                is_state_pred: true,
                var_indices: vec![0],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 0,
                    op: ScalarCompOp::Eq,
                    constant: 10,
                },
            },
            LivenessPredInfo {
                tag: 3,
                is_state_pred: true,
                var_indices: vec![1],
                kind: LivenessPredKind::ScalarComparison {
                    var_idx: 1,
                    op: ScalarCompOp::Ne,
                    constant: 0,
                },
            },
        ];

        let ir = generate_liveness_ir_text(&preds).expect("should generate");
        // Both tags should appear in shift operations.
        assert!(ir.contains("shl i64"), "should have shift operations");
        // Two OR operations to build up the bitmask.
        let or_count = ir.matches("or i64").count();
        assert_eq!(or_count, 2, "should have 2 OR operations for 2 predicates");
    }
}
