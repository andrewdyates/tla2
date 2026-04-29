// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JIT next-state cache: holds compiled native next-state action functions.
//!
//! `JitNextStateCache` is constructed at model checker startup time by
//! attempting to JIT-compile each bytecode next-state action. At check time,
//! the cache provides O(1) lookup from action name to native function pointer.
//!
//! # Key difference from `JitInvariantCache`
//!
//! Invariant functions consume a state and produce a boolean (pass/fail).
//! Next-state functions consume a current state and **produce** a successor
//! state: they write primed variable values to an output buffer. The JIT ABI
//! uses a 4-argument signature `(out, state_in, state_out, state_len)` where
//! `state_out` is caller-allocated and the compiled code writes primed values
//! via `StoreVar` opcodes.
//!
//! The `out.value` field indicates whether the action is **enabled** (1) or
//! **disabled** (0) for the current state.

use std::time::Instant;

use crate::abi::{JitCallOut, JitNextStateFn, JitStatus};
use crate::error::JitError;
use crate::tiered::{CacheBuildStats, CompileStats};
use rustc_hash::{FxHashMap, FxHashSet};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

use super::compile_common::{collect_loadvar_indices, collect_storevar_indices};
use super::eligibility::check_next_state_eligibility_with_constants;
use super::state_access::UnchangedVarMap;
use super::BytecodeLowerer;

// `NextStateDispatchCounters` moved to `tla-jit-abi` in Wave 16 Gate 1
// Batch C (Part of #4267 / #4291) so `tla-check` can own counter fields
// without depending on the Cranelift JIT crate. Re-exported for backward
// compatibility with existing `tla_jit::NextStateDispatchCounters` callers.
pub use tla_jit_abi::NextStateDispatchCounters;

// `JitActionResult` moved to `tla-jit-abi` in Wave 16 Gate 1 Batch D
// (Part of #4267 / #4291) so `tla-check` can match on JIT dispatch
// outcomes without pulling in the Cranelift JIT crate. Re-exported for
// backward compatibility with existing `tla_jit::JitActionResult` callers.
pub use tla_jit_abi::JitActionResult;

// `BindingSpec` and `specialized_key` now live in `tla-jit-abi` (leaf crate)
// so they survive Stage 2d deletion of `tla-jit`. Re-exported here for
// backward compatibility with existing `tla_jit::BindingSpec` / `tla_jit::specialized_key`
// callers. Part of #4270 and epic #4251.
pub use tla_jit_abi::{specialized_key, BindingSpec};

// `value_to_jit_i64` and `bindings_to_jit_i64` now live in
// `tla-jit-runtime::helpers` (Wave 11e of epic #4251 Stage 2d) so that
// `tla-check` can specialize bindings without depending on the Cranelift
// pipeline. Re-exported here for backward compatibility with
// `tla_jit::value_to_jit_i64` / `tla_jit::bindings_to_jit_i64` callers.
pub use tla_jit_runtime::{bindings_to_jit_i64, value_to_jit_i64};

/// Create a specialized bytecode function by prepending `LoadImm` instructions
/// for each binding parameter.
///
/// Given a function compiled from `SendMsg(i)` where parameter `i` is in
/// register 0, this prepends `LoadImm { rd: 0, value: binding_value }` so
/// the function can execute without the caller providing the binding.
///
/// The function's `arity` is set to 0 since the specialized version has no
/// unbound parameters. `max_register` is preserved from the base so the
/// register file remains large enough for all parameter registers the body
/// references.
///
/// `pub` since #4270: the tMIR → LLVM2 adapter reuses this transform to
/// lower EXISTS-bound actions through the binding-free next-state ABI.
pub fn specialize_bytecode_function(
    base: &BytecodeFunction,
    binding_values: &[i64],
    specialized_name: &str,
) -> BytecodeFunction {
    // Start from arity 0 so downstream gates (tMIR, LLVM2) treat the
    // specialized function as binding-free. The binding parameter registers
    // are still populated by the prepended `LoadImm` instructions.
    let mut func = BytecodeFunction::new(specialized_name.to_string(), 0);
    // Preserve the base's register-file size so all parameter registers
    // referenced by the body remain addressable. `emit` also updates
    // `max_register` on each instruction, but binding-only references never
    // raise the max, so we seed it here.
    func.max_register = base.max_register;
    // Prepend LoadImm for each binding parameter (registers 0..binding_values.len()).
    for (i, &value) in binding_values.iter().enumerate() {
        func.emit(Opcode::LoadImm { rd: i as u8, value });
    }
    // Append all original instructions (with jump offsets adjusted for the prepended instructions).
    let prefix_len = binding_values.len();
    for &op in &base.instructions {
        func.emit(adjust_jump_offsets(op, prefix_len as i16));
    }
    func
}

/// Adjust jump offsets in an opcode to account for prepended instructions.
///
/// When we prepend N `LoadImm` instructions, all jump targets that reference
/// positions relative to the current PC remain correct because the relative
/// offsets don't change — the body instructions are shifted uniformly.
/// However, backward jumps to the very start (offset = -(current_pc)) would
/// land in the prepended region, which is fine (they'll re-execute the LoadImm
/// instructions, which is a no-op since registers are overwritten by the body).
///
/// In practice, the bytecode compiler generates jumps relative to the current
/// instruction, so prepending instructions does NOT change relative offsets.
/// This function is a no-op but exists for documentation clarity.
fn adjust_jump_offsets(op: Opcode, _prefix_len: i16) -> Opcode {
    // Jump offsets in our bytecode are relative to the instruction that contains
    // them, not absolute. Since we shift ALL instructions by the same amount,
    // relative offsets remain correct. No adjustment needed.
    op
}

/// Per-action metadata stored alongside the compiled function pointer.
///
/// Part of #4034: Needed to construct `ActionDescriptor` for `CompiledBfsStep`.
#[derive(Debug, Clone)]
pub struct ActionMeta {
    /// Sorted, deduplicated indices of state variables read by this action.
    pub read_vars: Vec<u16>,
    /// Sorted, deduplicated indices of state variables written by this action.
    pub write_vars: Vec<u16>,
}

/// Cache of JIT-compiled next-state action functions.
///
/// Built once at startup, queried per-state during model checking.
/// Each compiled action takes a current state and produces a successor state
/// (or indicates the action is disabled).
pub struct JitNextStateCache {
    /// Owns the JIT module backing `functions`; dropping it invalidates pointers.
    _lowerer: BytecodeLowerer,
    /// Map from action name to native function pointer.
    functions: FxHashMap<String, JitNextStateFn>,
    /// Per-action metadata (read/write var indices).
    ///
    /// Part of #4034: Used to construct `ActionDescriptor` for `CompiledBfsStep`.
    action_meta: FxHashMap<String, ActionMeta>,
    /// Number of state variables (used to allocate output buffers).
    state_var_count: usize,
    /// Union of all `VarIdx` values read by any JIT-compiled action.
    /// Sorted, deduplicated.
    required_read_vars: Vec<u16>,
    /// Union of all `VarIdx` values written by any JIT-compiled action.
    /// Sorted, deduplicated.
    required_write_vars: Vec<u16>,
    /// Cached TLA2_JIT_DIAG env var check (avoid per-call syscall).
    jit_diag: bool,
}

// SAFETY: After construction, the cache is immutable. The stored function
// pointers target finalized machine code owned by `_lowerer`, and `_lowerer`
// is retained for the cache lifetime so the backing memory stays valid.
unsafe impl Send for JitNextStateCache {}
// SAFETY: Concurrent callers only read immutable maps and invoke finalized code
// with caller-owned input/output buffers; the cache itself has no mutation.
unsafe impl Sync for JitNextStateCache {}

impl JitNextStateCache {
    /// Build a JIT next-state cache from a bytecode chunk and action index.
    ///
    /// `action_indices` maps action name to bytecode function index.
    /// `state_var_count` is the total number of state variables in the model.
    ///
    /// For each action in `action_indices`, attempts JIT compilation. Actions
    /// that are not eligible or fail compilation are silently skipped (the
    /// bytecode VM or tree-walker handles them instead).
    pub fn build(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
    ) -> Result<Self, JitError> {
        let empty_unchanged = UnchangedVarMap::new();
        Self::build_with_unchanged(chunk, action_indices, state_var_count, &empty_unchanged)
    }

    /// Build a JIT next-state cache with pre-materialized Unchanged variable maps.
    pub fn build_with_unchanged(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
        unchanged_vars: &UnchangedVarMap,
    ) -> Result<Self, JitError> {
        Self::build_with_unchanged_and_layout(
            chunk,
            action_indices,
            state_var_count,
            unchanged_vars,
            None,
        )
    }

    /// Build a JIT next-state cache with compound state layout information.
    ///
    /// When `state_layout` is provided, compound variables (records, functions,
    /// sequences) in the state can be accessed natively by JIT-compiled actions
    /// via `FuncApply`, `RecordGet`, and `TupleGet` instead of falling back
    /// to the interpreter.
    ///
    /// Part of #3958: Enable native compound access in JIT next-state dispatch.
    pub fn build_with_unchanged_and_layout(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
        unchanged_vars: &UnchangedVarMap,
        state_layout: Option<&crate::compound_layout::StateLayout>,
    ) -> Result<Self, JitError> {
        use super::inliner::{has_call_opcodes, BytecodeInliner};
        use std::collections::HashMap;

        let mut lowerer = BytecodeLowerer::new()?;
        let mut functions = FxHashMap::default();
        let mut action_meta_map = FxHashMap::default();
        let mut all_read_indices: Vec<u16> = Vec::new();
        let mut all_write_indices: Vec<u16> = Vec::new();
        let mut read_set = FxHashSet::default();
        let mut write_set = FxHashSet::default();

        // Build callee map for inlining
        let callee_map: HashMap<u16, BytecodeFunction> = chunk
            .functions
            .iter()
            .enumerate()
            .map(|(idx, f)| (idx as u16, f.clone()))
            .collect();

        for (name, &func_idx) in action_indices {
            let func = chunk.functions.get(func_idx as usize).ok_or_else(|| {
                JitError::CompileError(format!(
                    "operator index {func_idx} for action {name} is out of range \
                     ({} functions)",
                    chunk.functions.len()
                ))
            })?;

            if let Err(_reason) =
                check_next_state_eligibility_with_constants(func, Some(&chunk.constants))
            {
                continue;
            }

            // Part of #4304: reject JIT when action would hit compound-type
            // fallback on a Seq-typed state var (flat state cannot represent Seq).
            if let Err(_reason) = super::eligibility::check_seq_compatible(func, state_layout) {
                continue;
            }

            // Inline callee calls to eliminate Call opcodes
            let func_to_compile = if has_call_opcodes(func) {
                BytecodeInliner::inline(func, &callee_map, 4).unwrap_or_else(|_| func.clone())
            } else {
                func.clone()
            };

            // Part of #4304: Post-inlining seq-compatibility check.
            if super::eligibility::check_seq_compatible(&func_to_compile, state_layout).is_err() {
                continue;
            }

            match lowerer.compile_next_state_with_layout(
                &func_to_compile,
                unchanged_vars,
                Some(&chunk.constants),
                state_layout,
            ) {
                Ok(Some(jit_fn)) => {
                    // Collect read/write variable indices for selective flattening.
                    let mut action_read: Vec<u16> = collect_loadvar_indices(&func_to_compile);
                    action_read.sort_unstable();
                    action_read.dedup();
                    let mut action_write: Vec<u16> = collect_storevar_indices(&func_to_compile);
                    action_write.sort_unstable();
                    action_write.dedup();
                    for &idx in &action_read {
                        if read_set.insert(idx) {
                            all_read_indices.push(idx);
                        }
                    }
                    for &idx in &action_write {
                        if write_set.insert(idx) {
                            all_write_indices.push(idx);
                        }
                    }
                    action_meta_map.insert(
                        name.clone(),
                        ActionMeta {
                            read_vars: action_read,
                            write_vars: action_write,
                        },
                    );
                    functions.insert(name.clone(), jit_fn);
                }
                Ok(None) => {
                    // Not eligible -- fall back to interpreter
                }
                Err(_) => {
                    // Compilation error -- fall back to interpreter
                }
            }
        }

        all_read_indices.sort_unstable();
        all_write_indices.sort_unstable();

        Ok(JitNextStateCache {
            _lowerer: lowerer,
            functions,
            action_meta: action_meta_map,
            state_var_count,
            required_read_vars: all_read_indices,
            required_write_vars: all_write_indices,
            jit_diag: std::env::var("TLA2_JIT_DIAG").is_ok(),
        })
    }

    /// Build a JIT next-state cache with compilation statistics.
    ///
    /// Identical to [`build`] but additionally returns per-action and aggregate
    /// timing data for compilation latency reporting.
    ///
    /// Part of #3910: JIT compilation latency instrumentation.
    pub fn build_with_stats(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
    ) -> Result<(Self, CacheBuildStats), JitError> {
        Self::build_with_stats_and_layout(chunk, action_indices, state_var_count, None)
    }

    /// Build with stats and state layout for native compound access.
    ///
    /// Part of #3958: Enable native compound access in JIT next-state dispatch.
    pub fn build_with_stats_and_layout(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
        state_layout: Option<&crate::compound_layout::StateLayout>,
    ) -> Result<(Self, CacheBuildStats), JitError> {
        // Auto-build UnchangedVarMap from the constant pool by scanning
        // action bytecode for Unchanged opcodes and reading var indices
        // from consecutive SmallInt constants at the `start` index.
        let unchanged = build_unchanged_map_from_chunk(chunk, action_indices);
        Self::build_with_unchanged_and_stats_and_layout(
            chunk,
            action_indices,
            state_var_count,
            &unchanged,
            state_layout,
        )
    }

    /// Build with Unchanged maps, stats, and state layout.
    ///
    /// Part of #3910: JIT compilation latency instrumentation.
    /// Part of #3958: Enable native compound access in JIT next-state dispatch.
    pub fn build_with_unchanged_and_stats_and_layout(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
        unchanged_vars: &UnchangedVarMap,
        state_layout: Option<&crate::compound_layout::StateLayout>,
    ) -> Result<(Self, CacheBuildStats), JitError> {
        use super::inliner::{has_call_opcodes, BytecodeInliner};
        use std::collections::HashMap;

        let build_start = Instant::now();
        let mut lowerer = BytecodeLowerer::new()?;
        let mut functions = FxHashMap::default();
        let mut action_meta_map = FxHashMap::default();
        let mut all_read_indices: Vec<u16> = Vec::new();
        let mut all_write_indices: Vec<u16> = Vec::new();
        let mut read_set = FxHashSet::default();
        let mut write_set = FxHashSet::default();
        let mut stats = CacheBuildStats::default();

        // Build callee map for inlining: all functions in the chunk keyed by index.
        // This allows the inliner to replace Call opcodes with inline callee code.
        let callee_map: HashMap<u16, BytecodeFunction> = chunk
            .functions
            .iter()
            .enumerate()
            .map(|(idx, f)| (idx as u16, f.clone()))
            .collect();

        let stats_enabled = std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1");

        for (name, &func_idx) in action_indices {
            let func = chunk.functions.get(func_idx as usize).ok_or_else(|| {
                JitError::CompileError(format!(
                    "operator index {func_idx} for action {name} is out of range \
                     ({} functions)",
                    chunk.functions.len()
                ))
            })?;

            if let Err(reason) =
                check_next_state_eligibility_with_constants(func, Some(&chunk.constants))
            {
                if stats_enabled {
                    eprintln!("[jit]   action '{name}': INELIGIBLE: {reason}");
                }
                stats.skipped_count += 1;
                continue;
            }

            // Part of #4304: reject JIT when action would hit compound-type
            // fallback on a Seq-typed state var (flat state cannot represent Seq).
            if let Err(reason) = super::eligibility::check_seq_compatible(func, state_layout) {
                if stats_enabled {
                    eprintln!("[jit]   action '{name}': INELIGIBLE (#4304 seq-heavy): {reason}");
                }
                stats.skipped_count += 1;
                continue;
            }

            // Inline callee calls to eliminate Call opcodes that always fallback.
            // The inliner replaces Call(op_idx) with the callee's bytecode inline,
            // allowing the JIT to compile the whole action natively.
            let func_to_compile = if has_call_opcodes(func) {
                match BytecodeInliner::inline(func, &callee_map, 4) {
                    Ok(inlined) => {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   action '{name}': inlined calls ({} -> {} opcodes)",
                                func.instructions.len(),
                                inlined.instructions.len()
                            );
                        }
                        inlined
                    }
                    Err(e) => {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   action '{name}': inlining failed: {e:?}, using original"
                            );
                        }
                        func.clone()
                    }
                }
            } else {
                func.clone()
            };

            // Part of #3958: Post-inlining check for ExistsBegin. Inlining may
            // introduce inner EXISTS quantifiers from callees. These produce
            // multiple successors that the single-successor JIT ABI cannot handle.
            if func_to_compile
                .instructions
                .iter()
                .any(|op| matches!(op, Opcode::ExistsBegin { .. }))
            {
                if stats_enabled {
                    eprintln!(
                        "[jit]   action '{name}': INELIGIBLE (post-inline): ExistsBegin in \
                         next-state action produces multiple successors"
                    );
                }
                stats.skipped_count += 1;
                continue;
            }

            // Part of #4304: Post-inlining seq-compatibility check. Inlining may
            // introduce Seq-incompatible ops (TupleNew/SeqNew/Concat/Append/etc.)
            // from callees that the direct check didn't see.
            if let Err(reason) =
                super::eligibility::check_seq_compatible(&func_to_compile, state_layout)
            {
                if stats_enabled {
                    eprintln!(
                        "[jit]   action '{name}': INELIGIBLE (#4304 seq-heavy post-inline): \
                         {reason}"
                    );
                }
                stats.skipped_count += 1;
                continue;
            }

            // Dump opcodes that will cause fallback (compound/set/call ops)
            if stats_enabled {
                for (pc, instr) in func_to_compile.instructions.iter().enumerate() {
                    let is_problematic = matches!(
                        instr,
                        Opcode::SetDiff { .. }
                            | Opcode::SetUnion { .. }
                            | Opcode::SetIntersect { .. }
                            | Opcode::Powerset { .. }
                            | Opcode::SetBuilderBegin { .. }
                            | Opcode::SetFilterBegin { .. }
                            | Opcode::FuncDefBegin { .. }
                            | Opcode::RecordNew { .. }
                            | Opcode::RecordSet { .. }
                            | Opcode::FuncDef { .. }
                            | Opcode::FuncSet { .. }
                            | Opcode::TupleNew { .. }
                            | Opcode::SeqNew { .. }
                            | Opcode::Concat { .. }
                            | Opcode::Call { .. }
                            | Opcode::Domain { .. }
                            | Opcode::CallBuiltin { .. }
                    );
                    if is_problematic {
                        eprintln!("[jit]   action '{name}' PC {pc}: fallback opcode: {instr:?}");
                    }
                }
            }

            let opcode_count = func_to_compile.instructions.len();
            let compile_start = Instant::now();
            let result = lowerer.compile_next_state_with_layout(
                &func_to_compile,
                unchanged_vars,
                Some(&chunk.constants),
                state_layout,
            );
            let compile_time = compile_start.elapsed();

            match result {
                Ok(Some(jit_fn)) => {
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: true,
                    });
                    stats.compiled_count += 1;

                    let mut action_read: Vec<u16> = collect_loadvar_indices(&func_to_compile);
                    action_read.sort_unstable();
                    action_read.dedup();
                    let mut action_write: Vec<u16> = collect_storevar_indices(&func_to_compile);
                    action_write.sort_unstable();
                    action_write.dedup();
                    for &idx in &action_read {
                        if read_set.insert(idx) {
                            all_read_indices.push(idx);
                        }
                    }
                    for &idx in &action_write {
                        if write_set.insert(idx) {
                            all_write_indices.push(idx);
                        }
                    }
                    action_meta_map.insert(
                        name.clone(),
                        ActionMeta {
                            read_vars: action_read,
                            write_vars: action_write,
                        },
                    );
                    functions.insert(name.clone(), jit_fn);
                }
                Ok(None) => {
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: false,
                    });
                    stats.skipped_count += 1;
                }
                Err(e) => {
                    if std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1") {
                        eprintln!("[jit]   action '{name}': compile error: {e}");
                    }
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: false,
                    });
                    stats.skipped_count += 1;
                }
            }
        }

        all_read_indices.sort_unstable();
        all_write_indices.sort_unstable();
        stats.total_build_time = build_start.elapsed();

        let cache = JitNextStateCache {
            _lowerer: lowerer,
            functions,
            action_meta: action_meta_map,
            state_var_count,
            required_read_vars: all_read_indices,
            required_write_vars: all_write_indices,
            jit_diag: std::env::var("TLA2_JIT_DIAG").is_ok(),
        };

        Ok((cache, stats))
    }

    /// Build with stats, layout, AND binding specializations.
    ///
    /// This is the Phase 1 entry point. For each `BindingSpec`, creates a
    /// specialized bytecode function with binding values baked in as constants,
    /// then JIT-compiles it under a specialized key.
    ///
    /// Falls back to the generic (unspecialized) compilation for actions that
    /// have no binding specs.
    ///
    /// Part of: JIT Phase 1 — pre-specialized binding functions.
    pub fn build_with_stats_and_specializations(
        chunk: &BytecodeChunk,
        action_indices: &FxHashMap<String, u16>,
        state_var_count: usize,
        state_layout: Option<&crate::compound_layout::StateLayout>,
        specializations: &[BindingSpec],
    ) -> Result<(Self, CacheBuildStats), JitError> {
        use super::inliner::{has_call_opcodes, BytecodeInliner};
        use std::collections::HashMap;

        let build_start = Instant::now();
        let mut lowerer = BytecodeLowerer::new()?;
        let mut functions = FxHashMap::default();
        let mut action_meta_map = FxHashMap::default();
        let mut all_read_indices: Vec<u16> = Vec::new();
        let mut all_write_indices: Vec<u16> = Vec::new();
        let mut read_set = FxHashSet::default();
        let mut write_set = FxHashSet::default();
        let mut stats = CacheBuildStats::default();

        // Auto-build UnchangedVarMap from the constant pool.
        let unchanged = build_unchanged_map_from_chunk(chunk, action_indices);

        // Build callee map for inlining.
        let callee_map: HashMap<u16, BytecodeFunction> = chunk
            .functions
            .iter()
            .enumerate()
            .map(|(idx, f)| (idx as u16, f.clone()))
            .collect();

        let stats_enabled = std::env::var("TLA2_BYTECODE_VM_STATS").as_deref() == Ok("1");

        // Phase A: Compile generic (unspecialized) actions.
        // These are used for binding-free actions.
        // Also serves as the base for specialization.
        let mut base_functions: HashMap<String, BytecodeFunction> = HashMap::new();

        for (name, &func_idx) in action_indices {
            let func = chunk.functions.get(func_idx as usize).ok_or_else(|| {
                JitError::CompileError(format!(
                    "operator index {func_idx} for action {name} is out of range \
                     ({} functions)",
                    chunk.functions.len()
                ))
            })?;

            // Part of #4176: Use permissive eligibility check that allows ExistsBegin.
            // Inner EXISTS will be handled by expansion below (Phase A).
            if let Err(reason) = super::eligibility::check_next_state_eligibility_allowing_exists(
                func,
                Some(&chunk.constants),
            ) {
                if stats_enabled {
                    eprintln!("[jit]   action '{name}': INELIGIBLE: {reason}");
                }
                stats.skipped_count += 1;
                continue;
            }

            // Part of #4304: reject JIT when action would hit compound-type
            // fallback on a Seq-typed state var (flat state cannot represent Seq).
            if let Err(reason) = super::eligibility::check_seq_compatible(func, state_layout) {
                if stats_enabled {
                    eprintln!("[jit]   action '{name}': INELIGIBLE (#4304 seq-heavy): {reason}");
                }
                stats.skipped_count += 1;
                continue;
            }

            // Inline callee calls.
            let func_to_compile = if has_call_opcodes(func) {
                match BytecodeInliner::inline(func, &callee_map, 4) {
                    Ok(inlined) => {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   action '{name}': inlined calls ({} -> {} opcodes)",
                                func.instructions.len(),
                                inlined.instructions.len()
                            );
                        }
                        inlined
                    }
                    Err(e) => {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   action '{name}': inlining failed: {e:?}, using original"
                            );
                        }
                        func.clone()
                    }
                }
            } else {
                func.clone()
            };

            // Part of #4304: Post-inlining seq-compatibility check. Inlining may
            // introduce Seq-incompatible ops from callees.
            if let Err(reason) =
                super::eligibility::check_seq_compatible(&func_to_compile, state_layout)
            {
                if stats_enabled {
                    eprintln!(
                        "[jit]   action '{name}': INELIGIBLE (#4304 seq-heavy post-inline): \
                         {reason}"
                    );
                }
                stats.skipped_count += 1;
                continue;
            }

            // Part of #3958/#4176: Post-inlining check for ExistsBegin (Phase A).
            // Instead of rejecting, try inner EXISTS expansion (Phase 1 of #4176).
            let has_inner_exists = func_to_compile
                .instructions
                .iter()
                .any(|op| matches!(op, Opcode::ExistsBegin { .. }));

            if has_inner_exists {
                // Phase 1: Try to expand inner EXISTS with static domains.
                use tla_tir::bytecode::{
                    can_expand_inner_exists, expand_inner_exists_preserving_offsets,
                };

                if can_expand_inner_exists(&func_to_compile, Some(&chunk.constants)) {
                    if let Some(expanded) = expand_inner_exists_preserving_offsets(
                        &func_to_compile,
                        Some(&chunk.constants),
                    ) {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   action '{name}': inner EXISTS expanded into {} \
                                 specialized functions",
                                expanded.len(),
                            );
                        }

                        // Compile each expanded function as a specialized action.
                        // The key format is "ActionName__inner_v0_v1..." to distinguish
                        // from outer binding specializations.
                        for expansion in &expanded {
                            let inner_key = specialized_key(name, &expansion.inner_binding_values);

                            if functions.contains_key(&inner_key) {
                                continue;
                            }

                            let opcode_count = expansion.func.instructions.len();
                            let compile_start = Instant::now();
                            let result = lowerer.compile_next_state_with_layout(
                                &expansion.func,
                                &unchanged,
                                Some(&chunk.constants),
                                state_layout,
                            );
                            let compile_time = compile_start.elapsed();

                            match result {
                                Ok(Some(jit_fn)) => {
                                    stats.per_action.push(CompileStats {
                                        action_name: inner_key.clone(),
                                        opcode_count,
                                        compile_time,
                                        success: true,
                                    });
                                    stats.compiled_count += 1;

                                    let mut action_read: Vec<u16> =
                                        collect_loadvar_indices(&expansion.func);
                                    action_read.sort_unstable();
                                    action_read.dedup();
                                    let mut action_write: Vec<u16> =
                                        collect_storevar_indices(&expansion.func);
                                    action_write.sort_unstable();
                                    action_write.dedup();
                                    for &idx in &action_read {
                                        if read_set.insert(idx) {
                                            all_read_indices.push(idx);
                                        }
                                    }
                                    for &idx in &action_write {
                                        if write_set.insert(idx) {
                                            all_write_indices.push(idx);
                                        }
                                    }
                                    action_meta_map.insert(
                                        inner_key.clone(),
                                        ActionMeta {
                                            read_vars: action_read,
                                            write_vars: action_write,
                                        },
                                    );
                                    functions.insert(inner_key, jit_fn);
                                }
                                Ok(None) => {
                                    if stats_enabled {
                                        eprintln!("[jit]   expanded '{inner_key}': not eligible");
                                    }
                                    stats.skipped_count += 1;
                                }
                                Err(e) => {
                                    if stats_enabled {
                                        eprintln!(
                                            "[jit]   expanded '{inner_key}': compile error: {e}"
                                        );
                                    }
                                    stats.skipped_count += 1;
                                }
                            }
                        }

                        // Store base for outer binding specialization (Phase B).
                        // The base has EXISTS, but we also store the expanded names
                        // so Phase B can combine outer + inner bindings.
                        base_functions.insert(name.clone(), func_to_compile.clone());
                        continue;
                    }
                }

                // Could not expand at generic level — store the base function anyway
                // so Phase B can try inner EXISTS expansion after outer binding
                // specialization. For example, `\E j \in Node \ {i} : ...` cannot
                // be expanded when `i` is unbound, but after specializing `i=0`,
                // the domain `Node \ {0}` may resolve to a known set `{1, 2}`.
                // Part of #4176: deferred inner EXISTS expansion.
                if stats_enabled {
                    eprintln!(
                        "[jit]   action '{name}': inner EXISTS not expandable at generic level; \
                         deferring to Phase B (outer binding specialization)"
                    );
                }
                base_functions.insert(name.clone(), func_to_compile.clone());
                continue;
            }

            // Store the prepared function for specialization.
            base_functions.insert(name.clone(), func_to_compile.clone());

            // Also compile the generic version (for binding-free actions).
            let opcode_count = func_to_compile.instructions.len();
            let compile_start = Instant::now();
            let result = lowerer.compile_next_state_with_layout(
                &func_to_compile,
                &unchanged,
                Some(&chunk.constants),
                state_layout,
            );
            let compile_time = compile_start.elapsed();

            match result {
                Ok(Some(jit_fn)) => {
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: true,
                    });
                    stats.compiled_count += 1;

                    let mut action_read: Vec<u16> = collect_loadvar_indices(&func_to_compile);
                    action_read.sort_unstable();
                    action_read.dedup();
                    let mut action_write: Vec<u16> = collect_storevar_indices(&func_to_compile);
                    action_write.sort_unstable();
                    action_write.dedup();
                    for &idx in &action_read {
                        if read_set.insert(idx) {
                            all_read_indices.push(idx);
                        }
                    }
                    for &idx in &action_write {
                        if write_set.insert(idx) {
                            all_write_indices.push(idx);
                        }
                    }
                    action_meta_map.insert(
                        name.clone(),
                        ActionMeta {
                            read_vars: action_read,
                            write_vars: action_write,
                        },
                    );
                    functions.insert(name.clone(), jit_fn);
                }
                Ok(None) => {
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: false,
                    });
                    stats.skipped_count += 1;
                }
                Err(e) => {
                    if stats_enabled {
                        eprintln!("[jit]   action '{name}': compile error: {e}");
                    }
                    stats.per_action.push(CompileStats {
                        action_name: name.clone(),
                        opcode_count,
                        compile_time,
                        success: false,
                    });
                    stats.skipped_count += 1;
                }
            }
        }

        // Phase B: Compile specialized (binding-specialized) actions.
        let mut specialized_count = 0usize;
        for spec in specializations {
            let base = match base_functions.get(&spec.action_name) {
                Some(f) => f,
                None => {
                    if stats_enabled {
                        let key = specialized_key(&spec.action_name, &spec.binding_values);
                        eprintln!(
                            "[jit]   specialized '{key}': base '{}' not compiled, skipping",
                            spec.action_name
                        );
                    }
                    continue;
                }
            };

            let key = specialized_key(&spec.action_name, &spec.binding_values);

            // Skip if we already compiled this exact specialization.
            if functions.contains_key(&key) {
                continue;
            }

            let formal_arity = usize::from(base.arity);
            if spec.formal_values.len() != formal_arity {
                if stats_enabled {
                    eprintln!(
                        "[jit]   specialized '{key}': formal binding arity mismatch for base '{}' ({} values for arity {}), skipping",
                        spec.action_name,
                        spec.formal_values.len(),
                        base.arity,
                    );
                }
                stats.skipped_count += 1;
                continue;
            }

            let specialized = specialize_bytecode_function(base, &spec.formal_values, &key);

            // Part of #4176: After outer binding specialization, check if the
            // specialized function has inner EXISTS that can now be expanded.
            // Example: `SendMsg(i)` with `\E j \in Node \ {i} : ...` cannot be
            // expanded when `i` is unbound. But `SendMsg__0_0` with `i=0` may
            // have `Node \ {0}` resolve to `{1, 2}` in the constant pool.
            let has_inner_exists_specialized = specialized
                .instructions
                .iter()
                .any(|op| matches!(op, Opcode::ExistsBegin { .. }));

            if has_inner_exists_specialized {
                use tla_tir::bytecode::{
                    can_expand_inner_exists, expand_inner_exists_preserving_offsets,
                };

                if can_expand_inner_exists(&specialized, Some(&chunk.constants)) {
                    if let Some(expanded) =
                        expand_inner_exists_preserving_offsets(&specialized, Some(&chunk.constants))
                    {
                        if stats_enabled {
                            eprintln!(
                                "[jit]   specialized '{key}': inner EXISTS expanded into {} functions",
                                expanded.len(),
                            );
                        }

                        for expansion in &expanded {
                            // Build combined key: outer binding + inner binding.
                            // e.g., "SendMsg__0_0" + inner [1] => "SendMsg__0_0__1"
                            let inner_key = specialized_key(&key, &expansion.inner_binding_values);

                            if functions.contains_key(&inner_key) {
                                continue;
                            }

                            let opcode_count = expansion.func.instructions.len();
                            let compile_start = Instant::now();
                            let result = lowerer.compile_next_state_with_layout(
                                &expansion.func,
                                &unchanged,
                                Some(&chunk.constants),
                                state_layout,
                            );
                            let compile_time = compile_start.elapsed();

                            match result {
                                Ok(Some(jit_fn)) => {
                                    stats.per_action.push(CompileStats {
                                        action_name: inner_key.clone(),
                                        opcode_count,
                                        compile_time,
                                        success: true,
                                    });
                                    stats.compiled_count += 1;
                                    specialized_count += 1;

                                    let mut action_read: Vec<u16> =
                                        collect_loadvar_indices(&expansion.func);
                                    action_read.sort_unstable();
                                    action_read.dedup();
                                    let mut action_write: Vec<u16> =
                                        collect_storevar_indices(&expansion.func);
                                    action_write.sort_unstable();
                                    action_write.dedup();
                                    for &idx in &action_read {
                                        if read_set.insert(idx) {
                                            all_read_indices.push(idx);
                                        }
                                    }
                                    for &idx in &action_write {
                                        if write_set.insert(idx) {
                                            all_write_indices.push(idx);
                                        }
                                    }
                                    action_meta_map.insert(
                                        inner_key.clone(),
                                        ActionMeta {
                                            read_vars: action_read,
                                            write_vars: action_write,
                                        },
                                    );
                                    functions.insert(inner_key, jit_fn);
                                }
                                Ok(None) => {
                                    if stats_enabled {
                                        eprintln!("[jit]   expanded '{inner_key}': not eligible");
                                    }
                                    stats.skipped_count += 1;
                                }
                                Err(e) => {
                                    if stats_enabled {
                                        eprintln!(
                                            "[jit]   expanded '{inner_key}': compile error: {e}"
                                        );
                                    }
                                    stats.skipped_count += 1;
                                }
                            }
                        }
                        // Don't compile the un-expanded specialized version
                        // (it has ExistsBegin and would produce wrong results).
                        continue;
                    }
                }

                // Inner EXISTS still not expandable even after outer specialization.
                if stats_enabled {
                    eprintln!("[jit]   specialized '{key}': inner EXISTS not expandable, skipping");
                }
                stats.skipped_count += 1;
                continue;
            }

            let opcode_count = specialized.instructions.len();
            let compile_start = Instant::now();
            let result = lowerer.compile_next_state_with_layout(
                &specialized,
                &unchanged,
                Some(&chunk.constants),
                state_layout,
            );
            let compile_time = compile_start.elapsed();

            match result {
                Ok(Some(jit_fn)) => {
                    if stats_enabled {
                        eprintln!(
                            "[jit]   specialized '{key}': compiled ({opcode_count} ops, {compile_time:?})"
                        );
                    }
                    stats.per_action.push(CompileStats {
                        action_name: key.clone(),
                        opcode_count,
                        compile_time,
                        success: true,
                    });
                    stats.compiled_count += 1;
                    specialized_count += 1;

                    let mut action_read: Vec<u16> = collect_loadvar_indices(&specialized);
                    action_read.sort_unstable();
                    action_read.dedup();
                    let mut action_write: Vec<u16> = collect_storevar_indices(&specialized);
                    action_write.sort_unstable();
                    action_write.dedup();
                    for &idx in &action_read {
                        if read_set.insert(idx) {
                            all_read_indices.push(idx);
                        }
                    }
                    for &idx in &action_write {
                        if write_set.insert(idx) {
                            all_write_indices.push(idx);
                        }
                    }
                    action_meta_map.insert(
                        key.clone(),
                        ActionMeta {
                            read_vars: action_read,
                            write_vars: action_write,
                        },
                    );
                    functions.insert(key, jit_fn);
                }
                Ok(None) => {
                    if stats_enabled {
                        eprintln!("[jit]   specialized '{key}': not eligible after specialization");
                    }
                    stats.skipped_count += 1;
                }
                Err(e) => {
                    if stats_enabled {
                        eprintln!("[jit]   specialized '{key}': compile error: {e}");
                    }
                    stats.skipped_count += 1;
                }
            }
        }

        if stats_enabled || specialized_count > 0 {
            eprintln!(
                "[jit] Specialized {specialized_count}/{} binding instances compiled",
                specializations.len(),
            );
        }

        all_read_indices.sort_unstable();
        all_write_indices.sort_unstable();
        stats.total_build_time = build_start.elapsed();

        let cache = JitNextStateCache {
            _lowerer: lowerer,
            functions,
            action_meta: action_meta_map,
            state_var_count,
            required_read_vars: all_read_indices,
            required_write_vars: all_write_indices,
            jit_diag: std::env::var("TLA2_JIT_DIAG").is_ok(),
        };

        Ok((cache, stats))
    }

    /// Check if any actions were JIT-compiled.
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Number of JIT-compiled actions.
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// List all compiled action keys, including inner EXISTS expansions.
    ///
    /// Inner EXISTS expansions have keys like "ActionName__v0_v1" where the
    /// suffix encodes the concrete binding values. This is useful for BFS
    /// dispatch to know which expanded actions to iterate.
    ///
    /// Part of #4176: JIT EXISTS binding dispatch.
    pub fn compiled_action_keys(&self) -> Vec<String> {
        self.functions.keys().cloned().collect()
    }

    /// Find all inner EXISTS expansion keys for a given base action name.
    ///
    /// Returns all compiled keys that start with `"base_name__"`, representing
    /// expanded inner EXISTS bindings. Returns an empty vec if the action has
    /// no inner EXISTS expansions.
    ///
    /// Part of #4176: JIT EXISTS binding dispatch.
    pub fn inner_exists_expansion_keys(&self, base_name: &str) -> Vec<String> {
        let prefix = format!("{base_name}__");
        let mut keys: Vec<String> = self
            .functions
            .keys()
            .filter(|k| k.starts_with(&prefix))
            .cloned()
            .collect();
        keys.sort();
        keys
    }

    /// Number of state variables in the model.
    pub fn state_var_count(&self) -> usize {
        self.state_var_count
    }

    /// Sorted, deduplicated list of `VarIdx` values read by any JIT-compiled
    /// action's `LoadVar` opcodes.
    pub fn required_read_vars(&self) -> &[u16] {
        &self.required_read_vars
    }

    /// Sorted, deduplicated list of `VarIdx` values written by any JIT-compiled
    /// action's `StoreVar` opcodes.
    pub fn required_write_vars(&self) -> &[u16] {
        &self.required_write_vars
    }

    /// Check whether a specific action has been JIT-compiled.
    pub fn contains_action(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Resolve action names to native function pointers in the given order.
    ///
    /// Returns `Some(vec)` if all actions are JIT-compiled, `None` if any
    /// is missing. The returned Vec has the same length and order as
    /// `action_names`, enabling callers to build `CompiledActionFn` wrappers
    /// without HashMap lookups in the hot path.
    ///
    /// Part of #4034: Extract raw JitNextStateFn pointers for CompiledBfsStep.
    pub fn resolve_ordered(
        &self,
        action_names: &[String],
    ) -> Option<Vec<crate::abi::JitNextStateFn>> {
        let mut resolved = Vec::with_capacity(action_names.len());
        for name in action_names {
            match self.functions.get(name) {
                Some(&f) => resolved.push(f),
                None => return None,
            }
        }
        Some(resolved)
    }

    /// Look up per-action metadata (read/write vars) by name.
    ///
    /// Part of #4034: Used to construct `ActionDescriptor` for `CompiledBfsStep`.
    pub fn action_metadata(&self, name: &str) -> Option<&ActionMeta> {
        self.action_meta.get(name)
    }

    /// Evaluate a single action against a flattened i64 state array.
    ///
    /// Returns:
    /// - `Some(Ok(JitActionResult::Enabled { successor }))` if the action
    ///   is enabled and produced a successor state.
    /// - `Some(Ok(JitActionResult::Disabled))` if the action's guard is false.
    /// - `Some(Err(_))` if a runtime error occurred (e.g., division by zero).
    /// - `None` if the action is not JIT-compiled or needs interpreter fallback.
    ///
    /// # Safety
    ///
    /// `state` must point to a valid array of at least `state_var_count` i64 values.
    pub fn eval_action(
        &self,
        name: &str,
        state: &[i64],
    ) -> Option<Result<JitActionResult, JitError>> {
        let jit_fn = self.functions.get(name)?;

        let mut out = JitCallOut::default();
        let mut state_out = vec![0i64; self.state_var_count];

        // SAFETY: state points to a valid i64 slice, out is a valid JitCallOut,
        // state_out is a valid mutable i64 slice of length state_var_count.
        unsafe {
            jit_fn(
                &mut out,
                state.as_ptr(),
                state_out.as_mut_ptr(),
                self.state_var_count as u32,
            );
        }

        match out.status {
            JitStatus::Ok => {
                if out.value != 0 {
                    Some(Ok(JitActionResult::Enabled {
                        successor: state_out,
                    }))
                } else {
                    Some(Ok(JitActionResult::Disabled))
                }
            }
            JitStatus::RuntimeError => Some(Err(JitError::RuntimeError { kind: out.err_kind })),
            JitStatus::FallbackNeeded | JitStatus::PartialPass => {
                use std::sync::atomic::{AtomicBool, Ordering};
                static LOGGED: AtomicBool = AtomicBool::new(false);
                if self.jit_diag && !LOGGED.swap(true, Ordering::Relaxed) {
                    eprintln!(
                        "[jit-diag] eval_action '{name}': runtime status={:?}, err_kind={:?}, value={}",
                        out.status, out.err_kind, out.value,
                    );
                }
                None
            }
        }
    }

    /// Evaluate a single action, writing the successor into a caller-provided
    /// buffer to avoid allocation on the hot path.
    ///
    /// Returns:
    /// - `Some(Ok(true))` if the action is enabled (successor written to `state_out`).
    /// - `Some(Ok(false))` if the action is disabled (`state_out` is unmodified).
    /// - `Some(Err(_))` on runtime error.
    /// - `None` if fallback to interpreter is needed or action not compiled.
    ///
    /// # Safety
    ///
    /// `state` and `state_out` must each have at least `state_var_count` elements.
    pub fn eval_action_into(
        &self,
        name: &str,
        state: &[i64],
        state_out: &mut [i64],
    ) -> Option<Result<bool, JitError>> {
        let jit_fn = self.functions.get(name)?;

        let mut out = JitCallOut::default();

        // SAFETY: state and state_out are valid i64 slices of sufficient length.
        unsafe {
            jit_fn(
                &mut out,
                state.as_ptr(),
                state_out.as_mut_ptr(),
                self.state_var_count as u32,
            );
        }

        match out.status {
            JitStatus::Ok => Some(Ok(out.value != 0)),
            JitStatus::RuntimeError => Some(Err(JitError::RuntimeError { kind: out.err_kind })),
            JitStatus::FallbackNeeded | JitStatus::PartialPass => None,
        }
    }

    /// Evaluate all JIT-compiled actions against a state, collecting successors.
    ///
    /// `actions` is the ordered list of action names to evaluate.
    /// `unchecked` collects names of actions that need interpreter fallback
    /// (either not compiled or returned FallbackNeeded at runtime).
    ///
    /// Returns a list of (action_name, successor_state) for enabled actions.
    pub fn eval_all_actions<'a>(
        &self,
        actions: &'a [String],
        state: &[i64],
        unchecked: &mut Vec<&'a str>,
    ) -> Result<Vec<(&'a str, Vec<i64>)>, JitError> {
        let mut successors = Vec::new();

        for action_name in actions {
            match self.eval_action(action_name, state) {
                Some(Ok(JitActionResult::Enabled { successor })) => {
                    successors.push((action_name.as_str(), successor));
                }
                Some(Ok(JitActionResult::Disabled)) => {
                    // Action guard is false -- no successor
                }
                Some(Err(e)) => return Err(e),
                None => {
                    // Not compiled or fallback needed
                    unchecked.push(action_name.as_str());
                }
            }
        }

        Ok(successors)
    }

    /// Evaluate all JIT-compiled actions with dispatch counters.
    ///
    /// Behaves identically to [`eval_all_actions`] but additionally populates
    /// `counters` with hit/fallback/not_compiled/error tallies.
    pub fn eval_all_actions_with_counters<'a>(
        &self,
        actions: &'a [String],
        state: &[i64],
        unchecked: &mut Vec<&'a str>,
        counters: &mut NextStateDispatchCounters,
    ) -> Result<Vec<(&'a str, Vec<i64>)>, JitError> {
        let mut successors = Vec::new();

        for action_name in actions {
            counters.total += 1;
            match self.eval_action(action_name, state) {
                Some(Ok(JitActionResult::Enabled { successor })) => {
                    counters.jit_hit += 1;
                    successors.push((action_name.as_str(), successor));
                }
                Some(Ok(JitActionResult::Disabled)) => {
                    counters.jit_hit += 1;
                    // Action guard is false -- no successor
                }
                Some(Err(e)) => {
                    counters.jit_error += 1;
                    return Err(e);
                }
                None => {
                    if self.functions.contains_key(action_name.as_str()) {
                        counters.jit_fallback += 1;
                    } else {
                        counters.jit_not_compiled += 1;
                    }
                    unchecked.push(action_name.as_str());
                }
            }
        }

        Ok(successors)
    }
}

/// Build an `UnchangedVarMap` by scanning bytecode for `Unchanged` opcodes
/// and reading consecutive `SmallInt` constants from the constant pool.
///
/// The bytecode compiler stores unchanged variable indices as consecutive
/// `SmallInt(var_idx)` entries starting at the `start` constant index.
fn build_unchanged_map_from_chunk(
    chunk: &BytecodeChunk,
    action_indices: &FxHashMap<String, u16>,
) -> UnchangedVarMap {
    let mut map = UnchangedVarMap::new();
    for &func_idx in action_indices.values() {
        if let Some(func) = chunk.functions.get(func_idx as usize) {
            for op in &func.instructions {
                if let Opcode::Unchanged { start, count, .. } = *op {
                    if map.contains_key(&start) {
                        continue;
                    }
                    let mut var_indices = Vec::with_capacity(count as usize);
                    for i in 0..count as u16 {
                        let val = chunk.constants.get_value(start + i);
                        if let tla_value::Value::SmallInt(n) = val {
                            var_indices.push(*n as u16);
                        }
                    }
                    if var_indices.len() == count as usize {
                        map.insert(start, var_indices);
                    }
                }
            }
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::{BytecodeFunction, Opcode};

    /// Build a simple next-state chunk: x' = x + 1, always enabled.
    fn make_increment_chunk() -> (BytecodeChunk, FxHashMap<String, u16>) {
        let mut func = BytecodeFunction::new("Increment".to_string(), 2);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("Increment".to_string(), 0);

        (chunk, action_indices)
    }

    /// Build a two-action chunk: Increment (x' = x + 1) and Decrement (x' = x - 1, guard: x > 0).
    fn make_two_action_chunk() -> (BytecodeChunk, FxHashMap<String, u16>) {
        // Action 0: Increment -- x' = x + 1, always enabled
        let mut inc_func = BytecodeFunction::new("Increment".to_string(), 2);
        inc_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inc_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        inc_func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inc_func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        inc_func.emit(Opcode::LoadBool { rd: 0, value: true });
        inc_func.emit(Opcode::Ret { rs: 0 });

        // Action 1: Decrement -- guard: x > 0, x' = x - 1
        let mut dec_func = BytecodeFunction::new("Decrement".to_string(), 3);
        dec_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        dec_func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        dec_func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        // If x <= 0, jump to disabled return
        dec_func.emit(Opcode::JumpFalse { rs: 2, offset: 4 });
        // Enabled: x' = x - 1
        dec_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        dec_func.emit(Opcode::SubInt {
            rd: 3,
            r1: 0,
            r2: 1,
        });
        dec_func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        dec_func.emit(Opcode::Ret { rs: 2 }); // return TRUE (r2=1)
                                              // Disabled: return FALSE
        dec_func.emit(Opcode::LoadBool {
            rd: 0,
            value: false,
        });
        dec_func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(inc_func);
        chunk.functions.push(dec_func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("Increment".to_string(), 0);
        action_indices.insert("Decrement".to_string(), 1);

        (chunk, action_indices)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_build_and_eval_increment() {
        let (chunk, action_indices) = make_increment_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");
        assert_eq!(cache.len(), 1);
        assert!(!cache.is_empty());
        assert!(cache.contains_action("Increment"));

        // x=10, x'=11
        let state = vec![10i64];
        let result = cache.eval_action("Increment", &state);
        match result {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![11i64]);
            }
            other => panic!("expected Enabled, got: {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_missing_action_returns_none() {
        let (chunk, action_indices) = make_increment_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        let state = vec![10i64];
        assert!(cache.eval_action("NonExistent", &state).is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_disabled_action() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");
        assert_eq!(cache.len(), 2);

        // x=0, Decrement guard: x > 0 is false => disabled
        let state = vec![0i64];
        let result = cache.eval_action("Decrement", &state);
        match result {
            Some(Ok(JitActionResult::Disabled)) => {}
            other => panic!("expected Disabled, got: {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_enabled_decrement() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        // x=5, Decrement guard: x > 0 is true => x' = 4
        let state = vec![5i64];
        let result = cache.eval_action("Decrement", &state);
        match result {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![4i64]);
            }
            other => panic!("expected Enabled with x'=4, got: {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_action_into() {
        let (chunk, action_indices) = make_increment_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        let state = vec![42i64];
        let mut state_out = vec![0i64; 1];
        let result = cache.eval_action_into("Increment", &state, &mut state_out);
        assert_eq!(result, Some(Ok(true)));
        assert_eq!(state_out, vec![43i64]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_action_into_disabled() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        let state = vec![0i64]; // x=0, Decrement disabled
        let mut state_out = vec![0i64; 1];
        let result = cache.eval_action_into("Decrement", &state, &mut state_out);
        assert_eq!(result, Some(Ok(false)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_all_actions() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        // x=5: both Increment and Decrement are enabled
        let actions = vec!["Increment".to_string(), "Decrement".to_string()];
        let state = vec![5i64];
        let mut unchecked = Vec::new();

        let successors = cache
            .eval_all_actions(&actions, &state, &mut unchecked)
            .expect("eval_all should succeed");

        assert!(unchecked.is_empty(), "all actions should be JIT-compiled");
        assert_eq!(successors.len(), 2);

        // Find Increment: x' = 6
        let inc_succ = successors.iter().find(|(n, _)| *n == "Increment");
        assert_eq!(inc_succ.expect("Increment should be present").1, vec![6i64]);

        // Find Decrement: x' = 4
        let dec_succ = successors.iter().find(|(n, _)| *n == "Decrement");
        assert_eq!(dec_succ.expect("Decrement should be present").1, vec![4i64]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_all_with_disabled() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        // x=0: Increment enabled (x'=1), Decrement disabled
        let actions = vec!["Increment".to_string(), "Decrement".to_string()];
        let state = vec![0i64];
        let mut unchecked = Vec::new();

        let successors = cache
            .eval_all_actions(&actions, &state, &mut unchecked)
            .expect("eval_all should succeed");

        assert!(unchecked.is_empty());
        assert_eq!(successors.len(), 1);
        assert_eq!(successors[0].0, "Increment");
        assert_eq!(successors[0].1, vec![1i64]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_all_with_unchecked() {
        let (chunk, action_indices) = make_increment_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        // Ask for actions including one that is not compiled
        let actions = vec!["Increment".to_string(), "NonExistent".to_string()];
        let state = vec![10i64];
        let mut unchecked = Vec::new();

        let successors = cache
            .eval_all_actions(&actions, &state, &mut unchecked)
            .expect("eval_all should succeed");

        assert_eq!(successors.len(), 1);
        assert_eq!(unchecked, vec!["NonExistent"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_eval_all_with_counters() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        let actions = vec![
            "Increment".to_string(),
            "Decrement".to_string(),
            "Missing".to_string(),
        ];
        let state = vec![5i64];
        let mut unchecked = Vec::new();
        let mut counters = NextStateDispatchCounters::default();

        let successors = cache
            .eval_all_actions_with_counters(&actions, &state, &mut unchecked, &mut counters)
            .expect("eval_all should succeed");

        assert_eq!(successors.len(), 2); // Increment + Decrement
        assert_eq!(unchecked, vec!["Missing"]);
        assert_eq!(counters.total, 3);
        assert_eq!(counters.jit_hit, 2); // Increment + Decrement
        assert_eq!(counters.jit_not_compiled, 1); // Missing
        assert_eq!(counters.jit_fallback, 0);
        assert_eq!(counters.jit_error, 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_required_vars() {
        let (chunk, action_indices) = make_two_action_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");

        // Both actions read and write var 0
        assert_eq!(cache.required_read_vars(), &[0]);
        assert_eq!(cache.required_write_vars(), &[0]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_ineligible_function_skipped() {
        // Empty function (ineligible for next-state JIT)
        let func = BytecodeFunction::new("BadAction".to_string(), 0);

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("BadAction".to_string(), 0);

        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 1).expect("build should succeed");
        assert!(cache.is_empty()); // Ineligible (empty function), not cached
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_build_rejects_out_of_range_index() {
        let chunk = BytecodeChunk::new();
        let mut action_indices = FxHashMap::default();
        action_indices.insert("MissingAction".to_string(), 1);

        match JitNextStateCache::build(&chunk, &action_indices, 1) {
            Err(JitError::CompileError(message)) => {
                assert!(message.contains("out of range"));
            }
            Err(other) => panic!("expected out-of-range compile error, got {other:?}"),
            Ok(_) => panic!("expected out-of-range operator index to fail"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_two_variable_swap() {
        // x' = y, y' = x
        let mut func = BytecodeFunction::new("Swap".to_string(), 3);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("Swap".to_string(), 0);

        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 2).expect("build should succeed");
        assert_eq!(cache.len(), 1);

        let state = vec![3i64, 7];
        let result = cache.eval_action("Swap", &state);
        match result {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![7i64, 3]);
            }
            other => panic!("expected Swap to produce [7, 3], got: {other:?}"),
        }

        // Check read/write vars
        assert_eq!(cache.required_read_vars(), &[0, 1]);
        assert_eq!(cache.required_write_vars(), &[0, 1]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cache_state_var_count() {
        let (chunk, action_indices) = make_increment_chunk();
        let cache =
            JitNextStateCache::build(&chunk, &action_indices, 5).expect("build should succeed");
        assert_eq!(cache.state_var_count(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_stats_reports_compile_times() {
        let (chunk, action_indices) = make_two_action_chunk();
        let (cache, stats) = JitNextStateCache::build_with_stats(&chunk, &action_indices, 1)
            .expect("build_with_stats should succeed");

        // Both actions should be compiled
        assert_eq!(cache.len(), 2);
        assert_eq!(stats.compiled_count, 2);
        assert_eq!(stats.skipped_count, 0);

        // Per-action stats should have entries for each action
        assert_eq!(stats.per_action.len(), 2);
        for stat in &stats.per_action {
            assert!(
                stat.success,
                "action {:?} should compile successfully",
                stat.action_name
            );
            assert!(stat.opcode_count > 0, "opcode count should be > 0");
            // Compile time should be non-zero (Cranelift does real work)
            // but less than 1 second for a trivial function
            assert!(
                stat.compile_time.as_secs() < 1,
                "compile time {:?} seems too long",
                stat.compile_time
            );
        }

        // Total build time should be >= sum of compile times
        let total_compile = stats.total_compile_time();
        assert!(
            stats.total_build_time >= total_compile,
            "total_build_time ({:?}) should be >= total_compile_time ({:?})",
            stats.total_build_time,
            total_compile,
        );

        // Display implementations should not panic
        let _display = format!("{stats}");
        for stat in &stats.per_action {
            let _display = format!("{stat}");
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_stats_ineligible_counted_as_skipped() {
        // Empty function is ineligible for next-state JIT
        let func = BytecodeFunction::new("BadAction".to_string(), 0);

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("BadAction".to_string(), 0);

        let (cache, stats) = JitNextStateCache::build_with_stats(&chunk, &action_indices, 1)
            .expect("build_with_stats should succeed");

        assert!(cache.is_empty());
        assert_eq!(stats.compiled_count, 0);
        assert_eq!(stats.skipped_count, 1);
        // No per-action stats for ineligible functions (they're filtered before compilation)
        assert_eq!(stats.per_action.len(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialized_key_binding_free() {
        assert_eq!(specialized_key("Inc", &[]), "Inc");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialized_key_single_binding() {
        assert_eq!(specialized_key("SendMsg", &[42]), "SendMsg__42");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialized_key_multi_binding() {
        assert_eq!(specialized_key("Action", &[1, 2, 3]), "Action__1_2_3");
    }

    /// Test that binding specialization produces correct results.
    ///
    /// Simulates the EXISTS binding pattern:
    ///   `\E i \in {10, 20} : SetX(i)`
    /// where SetX(i) sets x' = i.
    ///
    /// The base function SetX takes one parameter in register 0 and stores
    /// it as the new value of variable 0. Specializing with i=10 should
    /// produce a function that always sets x' = 10.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_specializations_exists_binding() {
        // Base function: x' = r0 (parameter), always enabled
        // This models SetX(i) where i is passed as register 0.
        let mut func = BytecodeFunction::new("SetX".to_string(), 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 }); // x' = r0
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("SetX".to_string(), 0);

        // Specializations: SetX with i=10 and i=20
        let specializations = vec![
            BindingSpec {
                action_name: "SetX".to_string(),
                binding_values: vec![10],
                formal_values: vec![10],
            },
            BindingSpec {
                action_name: "SetX".to_string(),
                binding_values: vec![20],
                formal_values: vec![20],
            },
        ];

        let (cache, stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1,
            None,
            &specializations,
        )
        .expect("build with specializations should succeed");

        // Should have: base "SetX" + specialized "SetX__10" + "SetX__20"
        assert!(
            cache.len() >= 3,
            "expected at least 3 compiled actions (base + 2 specializations), got {}",
            cache.len(),
        );
        assert!(
            cache.contains_action("SetX"),
            "base SetX should be compiled"
        );
        assert!(
            cache.contains_action("SetX__10"),
            "SetX__10 should be compiled"
        );
        assert!(
            cache.contains_action("SetX__20"),
            "SetX__20 should be compiled"
        );

        // Verify specialization produces correct results.
        let state = vec![0i64]; // initial x=0

        // SetX__10 should set x' = 10
        match cache.eval_action("SetX__10", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![10i64], "SetX__10 should set x' = 10");
            }
            other => panic!("expected Enabled for SetX__10, got: {other:?}"),
        }

        // SetX__20 should set x' = 20
        match cache.eval_action("SetX__20", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![20i64], "SetX__20 should set x' = 20");
            }
            other => panic!("expected Enabled for SetX__20, got: {other:?}"),
        }

        // Stats should reflect the specializations
        assert!(
            stats.compiled_count >= 3,
            "expected >= 3 compiled, got {}",
            stats.compiled_count
        );
    }

    /// Test binding specialization with a guarded action.
    ///
    /// Simulates: `\E i \in {1, 2} : GuardedSet(i)`
    /// where GuardedSet(i) guards on x < i, then sets x' = i.
    ///
    /// With x=0: both GuardedSet__1 and GuardedSet__2 should be enabled.
    /// With x=1: GuardedSet__1 should be disabled (0 < 1 is false for x=1),
    /// GuardedSet__2 should be enabled.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialization_with_guard() {
        // GuardedSet(i): guard x < r0, then x' = r0
        let mut func = BytecodeFunction::new("GuardedSet".to_string(), 2);
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 }); // r1 = x
        func.emit(Opcode::LtInt {
            rd: 2,
            r1: 1,
            r2: 0,
        }); // r2 = (x < i)
        func.emit(Opcode::JumpFalse { rs: 2, offset: 3 }); // if false, skip to disabled
                                                           // Enabled path: x' = r0
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::Ret { rs: 2 }); // return true
                                          // Disabled path
        func.emit(Opcode::LoadBool {
            rd: 0,
            value: false,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("GuardedSet".to_string(), 0);

        let specializations = vec![
            BindingSpec {
                action_name: "GuardedSet".to_string(),
                binding_values: vec![1],
                formal_values: vec![1],
            },
            BindingSpec {
                action_name: "GuardedSet".to_string(),
                binding_values: vec![2],
                formal_values: vec![2],
            },
        ];

        let (cache, _stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1,
            None,
            &specializations,
        )
        .expect("build should succeed");

        assert!(cache.contains_action("GuardedSet__1"));
        assert!(cache.contains_action("GuardedSet__2"));

        // x=0: both should be enabled
        let state_0 = vec![0i64];
        match cache.eval_action("GuardedSet__1", &state_0) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![1], "GuardedSet__1(x=0) -> x'=1");
            }
            other => panic!("expected Enabled for GuardedSet__1(x=0), got: {other:?}"),
        }
        match cache.eval_action("GuardedSet__2", &state_0) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![2], "GuardedSet__2(x=0) -> x'=2");
            }
            other => panic!("expected Enabled for GuardedSet__2(x=0), got: {other:?}"),
        }

        // x=1: GuardedSet__1 disabled (1 < 1 is false), GuardedSet__2 enabled
        let state_1 = vec![1i64];
        match cache.eval_action("GuardedSet__1", &state_1) {
            Some(Ok(JitActionResult::Disabled)) => {}
            other => panic!("expected Disabled for GuardedSet__1(x=1), got: {other:?}"),
        }
        match cache.eval_action("GuardedSet__2", &state_1) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![2], "GuardedSet__2(x=1) -> x'=2");
            }
            other => panic!("expected Enabled for GuardedSet__2(x=1), got: {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_value_to_jit_i64_smallint() {
        assert_eq!(value_to_jit_i64(&tla_value::Value::SmallInt(42)), Some(42));
        assert_eq!(value_to_jit_i64(&tla_value::Value::SmallInt(-1)), Some(-1));
        assert_eq!(value_to_jit_i64(&tla_value::Value::SmallInt(0)), Some(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_value_to_jit_i64_bool() {
        assert_eq!(value_to_jit_i64(&tla_value::Value::Bool(true)), Some(1));
        assert_eq!(value_to_jit_i64(&tla_value::Value::Bool(false)), Some(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_value_to_jit_i64_string() {
        let value = tla_value::Value::String(std::sync::Arc::<str>::from("hello"));
        let expected = tla_core::intern_name("hello").0 as i64;

        assert_eq!(value_to_jit_i64(&value), Some(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_value_to_jit_i64_model_value() {
        let value = tla_value::Value::ModelValue(std::sync::Arc::<str>::from("p1"));
        let expected = tla_core::intern_name("p1").0 as i64;

        assert_eq!(value_to_jit_i64(&value), Some(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_value_to_jit_i64_compound_types_rejected() {
        let set_value = tla_value::Value::Set(std::sync::Arc::new(tla_value::SortedSet::new()));
        let seq_value = tla_value::Value::Seq(std::sync::Arc::new(tla_value::SeqValue::default()));
        let record_value =
            tla_value::Value::Record(tla_value::RecordValue::from_sorted_str_entries(vec![(
                std::sync::Arc::<str>::from("field"),
                tla_value::Value::SmallInt(1),
            )]));
        let func_value = tla_value::Value::Func(std::sync::Arc::new(
            tla_value::FuncValue::from_sorted_entries(vec![(
                tla_value::Value::SmallInt(1),
                tla_value::Value::Bool(true),
            )]),
        ));

        assert_eq!(value_to_jit_i64(&set_value), None);
        assert_eq!(value_to_jit_i64(&seq_value), None);
        assert_eq!(value_to_jit_i64(&record_value), None);
        assert_eq!(value_to_jit_i64(&func_value), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bindings_to_jit_i64_empty() {
        let bindings: [(std::sync::Arc<str>, tla_value::Value); 0] = [];

        assert_eq!(bindings_to_jit_i64(&bindings), Some(vec![]));
    }

    /// Part of #4270: the tMIR → LLVM2 adapter calls `specialize_bytecode_function`
    /// and requires the returned function to be arity-0 so the gate in
    /// `crates/tla-tmir/src/lower/mod.rs:297` accepts it. Regression guard
    /// against the prior behavior of passing `max_register` as arity.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialize_bytecode_function_returns_arity_zero() {
        let mut base = BytecodeFunction::new("SendMsg".to_string(), 2);
        base.emit(Opcode::StoreVar { var_idx: 0, rs: 0 }); // use param r0
        base.emit(Opcode::Ret { rs: 1 });

        assert_eq!(base.arity, 2, "base function should report arity 2");
        let max_reg_before = base.max_register;

        let specialized = specialize_bytecode_function(&base, &[42, 7], "SendMsg__42_7");

        assert_eq!(
            specialized.arity, 0,
            "specialized function must be arity 0 for tMIR/LLVM2 compatibility"
        );
        assert_eq!(specialized.name, "SendMsg__42_7");
        assert!(
            specialized.max_register >= max_reg_before,
            "max_register must cover all registers the original body referenced",
        );
        // First two instructions should be the prepended LoadImm entries.
        assert!(matches!(
            specialized.instructions[0],
            Opcode::LoadImm { rd: 0, value: 42 }
        ));
        assert!(matches!(
            specialized.instructions[1],
            Opcode::LoadImm { rd: 1, value: 7 }
        ));
    }

    /// Part of #4270: specialization with empty bindings should still produce
    /// an arity-0 function (defensive — LLVM2 call sites may invoke this
    /// helper when the base already has arity 0).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_specialize_bytecode_function_no_bindings_is_arity_zero() {
        let mut base = BytecodeFunction::new("Init".to_string(), 0);
        base.emit(Opcode::LoadBool { rd: 0, value: true });
        base.emit(Opcode::Ret { rs: 0 });

        let specialized = specialize_bytecode_function(&base, &[], "Init");

        assert_eq!(specialized.arity, 0);
        assert_eq!(specialized.instructions.len(), base.instructions.len());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bindings_to_jit_i64_all_scalar() {
        let bindings = vec![
            (
                std::sync::Arc::<str>::from("i"),
                tla_value::Value::SmallInt(42),
            ),
            (
                std::sync::Arc::<str>::from("flag"),
                tla_value::Value::Bool(true),
            ),
        ];

        assert_eq!(bindings_to_jit_i64(&bindings), Some(vec![42, 1]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bindings_to_jit_i64_any_compound_rejects_all() {
        let bindings = vec![
            (
                std::sync::Arc::<str>::from("i"),
                tla_value::Value::SmallInt(42),
            ),
            (
                std::sync::Arc::<str>::from("set_binding"),
                tla_value::Value::Set(std::sync::Arc::new(tla_value::SortedSet::new())),
            ),
        ];

        assert_eq!(bindings_to_jit_i64(&bindings), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dispatch_key_round_trip() {
        let mut func = BytecodeFunction::new("DispatchAction".to_string(), 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("DispatchAction".to_string(), 0);

        let vals = vec![99, 1];
        let specializations = vec![BindingSpec {
            action_name: "DispatchAction".to_string(),
            binding_values: vals.clone(),
            formal_values: vec![1],
        }];

        let (cache, _stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1,
            None,
            &specializations,
        )
        .expect("build with specializations should succeed");

        let key = specialized_key("DispatchAction", &vals);
        assert!(cache.contains_action(&key), "{key} should be compiled");

        match cache.eval_action(&key, &[0]) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![1],
                    "executable key witnesses must not be mistaken for base operator formals",
                );
            }
            other => panic!("expected Enabled for {key}, got: {other:?}"),
        }
    }

    /// Test multi-variable action with EXISTS binding.
    ///
    /// Simulates a realistic EWD998-like pattern:
    ///   `\E i \in {0, 1, 2} : SendMsg(i)`
    /// where SendMsg(i) modifies two state variables:
    ///   active[i]' = TRUE (var 0 = r0 parameter)
    ///   counter' = counter + 1 (var 1 = var 1 + 1)
    ///
    /// Validates that:
    /// 1. Three specializations (i=0, i=1, i=2) each produce correct results
    /// 2. Each specialized function writes the correct binding value to var 0
    /// 3. The shared computation (counter+1) works identically across specializations
    /// 4. eval_all_actions_with_counters reports correct hit counts
    ///
    /// Part of #3984: Wire binding specialization into BFS dispatch.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_multi_var_exists_pattern() {
        // SendMsg(i): active[i]' = r0 (binding param), counter' = counter + 1
        // Two state vars: var0 = active, var1 = counter
        let mut func = BytecodeFunction::new("SendMsg".to_string(), 3);
        // r0 is the EXISTS binding parameter (will be specialized via LoadImm)
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 }); // active' = r0
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 }); // r1 = counter
        func.emit(Opcode::LoadImm { rd: 2, value: 1 }); // r2 = 1
        func.emit(Opcode::AddInt {
            rd: 3,
            r1: 1,
            r2: 2,
        }); // r3 = counter + 1
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 3 }); // counter' = counter + 1
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("SendMsg".to_string(), 0);

        // Three EXISTS binding instances: i=0, i=1, i=2
        let specializations = vec![
            BindingSpec {
                action_name: "SendMsg".to_string(),
                binding_values: vec![0],
                formal_values: vec![0],
            },
            BindingSpec {
                action_name: "SendMsg".to_string(),
                binding_values: vec![1],
                formal_values: vec![1],
            },
            BindingSpec {
                action_name: "SendMsg".to_string(),
                binding_values: vec![2],
                formal_values: vec![2],
            },
        ];

        let (cache, stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            2, // 2 state variables
            None,
            &specializations,
        )
        .expect("build should succeed");

        // Should have base + 3 specializations
        assert!(cache.contains_action("SendMsg"), "base should be compiled");
        assert!(
            cache.contains_action("SendMsg__0"),
            "SendMsg__0 should be compiled"
        );
        assert!(
            cache.contains_action("SendMsg__1"),
            "SendMsg__1 should be compiled"
        );
        assert!(
            cache.contains_action("SendMsg__2"),
            "SendMsg__2 should be compiled"
        );
        assert!(
            stats.compiled_count >= 4,
            "expected >= 4 compiled, got {}",
            stats.compiled_count
        );

        // Initial state: active=99, counter=5
        let state = vec![99i64, 5];

        // SendMsg__0: active' = 0, counter' = 6
        match cache.eval_action("SendMsg__0", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![0, 6],
                    "SendMsg__0 should set active=0, counter=6"
                );
            }
            other => panic!("expected Enabled for SendMsg__0, got: {other:?}"),
        }

        // SendMsg__1: active' = 1, counter' = 6
        match cache.eval_action("SendMsg__1", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![1, 6],
                    "SendMsg__1 should set active=1, counter=6"
                );
            }
            other => panic!("expected Enabled for SendMsg__1, got: {other:?}"),
        }

        // SendMsg__2: active' = 2, counter' = 6
        match cache.eval_action("SendMsg__2", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![2, 6],
                    "SendMsg__2 should set active=2, counter=6"
                );
            }
            other => panic!("expected Enabled for SendMsg__2, got: {other:?}"),
        }

        // Test eval_all_actions_with_counters using specialized keys
        let actions = vec![
            "SendMsg__0".to_string(),
            "SendMsg__1".to_string(),
            "SendMsg__2".to_string(),
        ];
        let mut unchecked = Vec::new();
        let mut counters = NextStateDispatchCounters::default();

        let successors = cache
            .eval_all_actions_with_counters(&actions, &state, &mut unchecked, &mut counters)
            .expect("eval_all should succeed");

        assert_eq!(
            successors.len(),
            3,
            "all 3 specializations should be enabled"
        );
        assert!(
            unchecked.is_empty(),
            "no actions should need interpreter fallback"
        );
        assert_eq!(counters.total, 3);
        assert_eq!(counters.jit_hit, 3);
        assert_eq!(counters.jit_not_compiled, 0);
        assert_eq!(counters.jit_fallback, 0);
    }

    /// Test model value binding round-trip through the full specialization path.
    ///
    /// Simulates `\E p \in {p1, p2} : SetProc(p)` where p1 and p2 are model
    /// values. The full path: ModelValue -> value_to_jit_i64 (intern) ->
    /// BindingSpec -> specialized bytecode function -> JIT compile -> eval.
    ///
    /// This validates the consistency between the binding conversion in
    /// compile_jit_next_state_on_promotion (which creates BindingSpec from
    /// ActionInstanceMeta) and the lookup in try_jit_monolithic_successors
    /// (which converts bindings to i64 and constructs the specialized key).
    ///
    /// Part of #3984: Wire binding specialization into BFS dispatch.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_value_binding_round_trip() {
        // Action: x' = r0 (the model value's interned NameId)
        let mut func = BytecodeFunction::new("SetProc".to_string(), 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("SetProc".to_string(), 0);

        // Simulate split_action_meta bindings with ModelValue
        let bindings_p1: Vec<(std::sync::Arc<str>, tla_value::Value)> = vec![(
            std::sync::Arc::from("p"),
            tla_value::Value::ModelValue(std::sync::Arc::from("proc1")),
        )];
        let bindings_p2: Vec<(std::sync::Arc<str>, tla_value::Value)> = vec![(
            std::sync::Arc::from("p"),
            tla_value::Value::ModelValue(std::sync::Arc::from("proc2")),
        )];

        // Step 1: Build BindingSpec (same as compile_jit_next_state_on_promotion)
        let p1_vals = bindings_to_jit_i64(&bindings_p1).expect("ModelValue should convert");
        let p2_vals = bindings_to_jit_i64(&bindings_p2).expect("ModelValue should convert");
        assert_ne!(
            p1_vals, p2_vals,
            "distinct model values must have distinct i64"
        );

        let specializations = vec![
            BindingSpec {
                action_name: "SetProc".to_string(),
                binding_values: p1_vals.clone(),
                formal_values: p1_vals.clone(),
            },
            BindingSpec {
                action_name: "SetProc".to_string(),
                binding_values: p2_vals.clone(),
                formal_values: p2_vals.clone(),
            },
        ];

        // Step 2: Build cache with specializations
        let (cache, _stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1,
            None,
            &specializations,
        )
        .expect("build should succeed");

        // Step 3: Look up using same key format as try_jit_monolithic_successors
        let key_p1 = bindings_to_jit_i64(&bindings_p1)
            .map(|vals| specialized_key("SetProc", &vals))
            .expect("key should be constructible");
        let key_p2 = bindings_to_jit_i64(&bindings_p2)
            .map(|vals| specialized_key("SetProc", &vals))
            .expect("key should be constructible");

        assert!(cache.contains_action(&key_p1), "cache should have {key_p1}");
        assert!(cache.contains_action(&key_p2), "cache should have {key_p2}");

        // Step 4: Verify evaluation produces correct interned values
        let state = vec![0i64];
        match cache.eval_action(&key_p1, &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![p1_vals[0]],
                    "SetProc(proc1) should set x' to proc1's interned id"
                );
            }
            other => panic!("expected Enabled for {key_p1}, got: {other:?}"),
        }
        match cache.eval_action(&key_p2, &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(
                    successor,
                    vec![p2_vals[0]],
                    "SetProc(proc2) should set x' to proc2's interned id"
                );
            }
            other => panic!("expected Enabled for {key_p2}, got: {other:?}"),
        }
    }

    // ================================================================
    // Inner EXISTS expansion integration tests (Part of #4176)
    // ================================================================

    /// Build a chunk with an inner EXISTS action:
    /// SetVal == \E val \in {10, 20, 30} : x' = val
    ///
    /// This action has an inner EXISTS that produces multiple successors.
    /// The build_with_stats_and_specializations should expand it into 3
    /// specialized functions: SetVal__10, SetVal__20, SetVal__30.
    fn make_inner_exists_chunk() -> (BytecodeChunk, FxHashMap<String, u16>) {
        let mut func = BytecodeFunction::new("SetVal".to_string(), 6);

        // Load domain elements into registers for SetEnum
        func.emit(Opcode::LoadImm { rd: 3, value: 10 }); // PC 0
        func.emit(Opcode::LoadImm { rd: 4, value: 20 }); // PC 1
        func.emit(Opcode::LoadImm { rd: 5, value: 30 }); // PC 2
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 3,
            count: 3,
        }); // PC 3

        // ExistsBegin: \E val(r1) \in r2
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 4, // -> PC 8
        }); // PC 4

        // Body: x' = val
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // PC 5
        func.emit(Opcode::LoadBool { rd: 4, value: true }); // PC 6

        // ExistsNext
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 4,
            loop_begin: -2, // -> PC 5
        }); // PC 7

        func.emit(Opcode::Ret { rs: 0 }); // PC 8

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("SetVal".to_string(), 0);

        (chunk, action_indices)
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inner_exists_expansion_via_build() {
        let (chunk, action_indices) = make_inner_exists_chunk();

        let (cache, stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1, // 1 state variable
            None,
            &[], // No outer binding specializations
        )
        .expect("build should succeed");

        // The inner EXISTS should be expanded into 3 specialized functions
        let expansion_keys = cache.inner_exists_expansion_keys("SetVal");
        assert_eq!(
            expansion_keys.len(),
            3,
            "should have 3 inner EXISTS expansions; compiled keys: {:?}",
            cache.compiled_action_keys(),
        );

        // Verify the expanded function keys
        assert!(
            cache.contains_action("SetVal__10"),
            "should have SetVal__10"
        );
        assert!(
            cache.contains_action("SetVal__20"),
            "should have SetVal__20"
        );
        assert!(
            cache.contains_action("SetVal__30"),
            "should have SetVal__30"
        );

        // Stats should show compiled functions
        assert!(
            stats.compiled_count >= 3,
            "at least 3 expanded functions should be compiled, got {}",
            stats.compiled_count
        );

        // Evaluate each expanded action
        let state = vec![0i64]; // initial state x=0

        for (key, expected_val) in [("SetVal__10", 10), ("SetVal__20", 20), ("SetVal__30", 30)] {
            match cache.eval_action(key, &state) {
                Some(Ok(JitActionResult::Enabled { successor })) => {
                    assert_eq!(
                        successor,
                        vec![expected_val],
                        "{key} should set x' = {expected_val}"
                    );
                }
                Some(Ok(JitActionResult::Disabled)) => {
                    panic!("{key} should be enabled, got Disabled");
                }
                Some(Err(e)) => {
                    panic!("{key} returned error: {e}");
                }
                None => {
                    // Fallback needed is acceptable if the expanded function
                    // still has compound opcodes
                    eprintln!("{key} returned None (FallbackNeeded)");
                }
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inner_exists_expansion_with_binding_free_action() {
        // Test that a chunk with both a binding-free action and an inner EXISTS
        // action correctly compiles both. The binding-free action should be
        // compiled normally, and the EXISTS action should be expanded.
        let mut inc_func = BytecodeFunction::new("Increment".to_string(), 2);
        inc_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inc_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        inc_func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inc_func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        inc_func.emit(Opcode::LoadBool { rd: 0, value: true });
        inc_func.emit(Opcode::Ret { rs: 0 });

        // Inner EXISTS action: SetVal == \E val \in {10, 20} : x' = val
        let mut setval_func = BytecodeFunction::new("SetVal".to_string(), 6);
        setval_func.emit(Opcode::LoadImm { rd: 3, value: 10 }); // PC 0
        setval_func.emit(Opcode::LoadImm { rd: 4, value: 20 }); // PC 1
        setval_func.emit(Opcode::SetEnum {
            rd: 2,
            start: 3,
            count: 2,
        }); // PC 2
        setval_func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 4, // -> PC 7
        }); // PC 3
        setval_func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // PC 4
        setval_func.emit(Opcode::LoadBool { rd: 4, value: true }); // PC 5
        setval_func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 4,
            loop_begin: -2, // -> PC 4
        }); // PC 6
        setval_func.emit(Opcode::Ret { rs: 0 }); // PC 7

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(inc_func);
        chunk.functions.push(setval_func);

        let mut action_indices = FxHashMap::default();
        action_indices.insert("Increment".to_string(), 0);
        action_indices.insert("SetVal".to_string(), 1);

        let (cache, _stats) = JitNextStateCache::build_with_stats_and_specializations(
            &chunk,
            &action_indices,
            1,
            None,
            &[],
        )
        .expect("build should succeed");

        // Increment should be compiled normally
        assert!(
            cache.contains_action("Increment"),
            "Increment should be compiled"
        );

        // SetVal expansions should exist
        assert!(
            cache.contains_action("SetVal__10"),
            "SetVal__10 should be compiled"
        );
        assert!(
            cache.contains_action("SetVal__20"),
            "SetVal__20 should be compiled"
        );

        // Verify Increment works
        let state = vec![5i64];
        match cache.eval_action("Increment", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![6], "Increment should set x' = 6");
            }
            other => panic!("Increment expected Enabled, got: {other:?}"),
        }

        // Verify SetVal expansions work
        match cache.eval_action("SetVal__10", &state) {
            Some(Ok(JitActionResult::Enabled { successor })) => {
                assert_eq!(successor, vec![10], "SetVal__10 should set x' = 10");
            }
            other => panic!("SetVal__10 expected Enabled, got: {other:?}"),
        }
    }
}
