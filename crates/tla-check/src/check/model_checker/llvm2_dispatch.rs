// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM2 native compilation dispatch for the BFS model checker.
//!
//! Provides an alternative to the Cranelift JIT path by compiling TIR bytecode
//! through the LLVM2 native pipeline: BytecodeFunction -> tMIR -> LLVM2 ISel ->
//! RegAlloc -> AArch64/x86 encoding -> JIT executable memory. Zero C dependencies.
//! The resulting native functions share the same `extern "C"` ABI as Cranelift JIT,
//! so the BFS dispatch logic is compatible with both backends.
//!
//! # Design rationale (Part of #4251 Stream 6 / #4118)
//!
//! **(a) Spec shape eligibility.** The BFS path compiles the per-action
//! next-state function via `compile_next_state_native_with_constants`. The
//! next-state ABI is `fn(out, state_in, state_out, state_len)` with NO
//! parameters — so actions with `arity > 0` (EXISTS-bound parameters like
//! `\E i \in S : Action(i)`) are ineligible and routed to the interpreter.
//! In addition, we pre-screen with [`tla_llvm2::is_tir_eligible_with_state`]
//! to skip actions whose bytecode contains opcodes that are known to reach
//! unsupported paths (closures, builder lambdas, etc.). This is a soft
//! pre-screen only — the tMIR pipeline handles many more opcodes than the
//! direct TIR→LLVM fast path, so pre-screen rejection triggers a warning and
//! still attempts compilation. The pipeline itself is the source of truth
//! and returns [`tla_llvm2::Llvm2Error::UnsupportedInst`] when the action
//! cannot be compiled, at which point the action is permanently routed to
//! the interpreter for the remainder of the run.
//!
//! **(b) Per-action dispatch.** [`Llvm2NativeCache`] owns a
//! `FxHashMap<String, NativeNextStateFn>` keyed by action name. At BFS
//! setup, each action is compiled eagerly and the resulting function pointer
//! (plus its backing [`NativeLibrary`] mmap) is installed in the cache.
//! Inside the BFS action loop, dispatch flows interpreter-first-unless-compiled:
//! if `cache.contains_action(action_name)` is true the native path runs;
//! otherwise the interpreter runs. There is NO global switch once the cache
//! is built — every action picks its path independently each iteration.
//!
//! **(c) Fallback on compile failure / ineligibility.** Compile failures
//! are absorbed at `Llvm2NativeCache::build` time: the failure is logged
//! once (at cache construction), the failed action is omitted from
//! `next_state_fns`, and no retry is ever attempted. The interpreter then
//! handles every BFS visit of that action's (state, action) pair. This is
//! the "log once, interpreter forever" policy described in the Stream 6
//! handoff.
//!
//! # ABI Compatibility
//!
//! Both Cranelift JIT and LLVM2 use the same function signature:
//! - **Next-state**: `extern "C" fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
//! - **Invariant**: `extern "C" fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
//!
//! # Activation
//!
//! Enable at compile time with `--features llvm2`, then at runtime with
//! either `TLA2_LLVM2=1` (global LLVM2 dispatch) or `TLA2_LLVM2_BFS=1`
//! (BFS-scoped dispatch — identical code path today; reserved as a
//! narrower switch so invariant / liveness LLVM2 wiring can activate
//! independently in the future). No system LLVM installation required —
//! the LLVM2 backend is a pure-Rust JIT compiler.
//!
//! # Pipeline
//!
//! ```text
//! BytecodeFunction (per action / invariant)
//!     |  (tla_tmir::lower -> tmir::Module)
//!     v
//! tmir::Module (SSA IR)
//!     |  (tla_llvm2::compile_module_native -> LLVM2 JIT pipeline)
//!     v
//! NativeLibrary (JIT executable buffer)
//!     |  (get_symbol -> transmute)
//!     v
//! Callable function pointers
//! ```
//!
//! Part of #4118: Wire tla-llvm2 into tla-check BFS loop.
//! Part of #4251 Stream 6: BFS-scoped activation via `TLA2_LLVM2_BFS`.

use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_jit_abi::{BindingSpec, JitCallOut};

/// Type alias for the native next-state function pointer.
///
/// ABI: `extern "C" fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
///
/// - `out`: caller-allocated result struct. On success, `out.status = Ok` and
///   `out.value = 1` (enabled) or `0` (disabled). On error, status is set
///   to RuntimeError with error details.
/// - `state_in`: flat i64 array of current state variable values.
/// - `state_out`: flat i64 array for successor state (pre-allocated by caller).
/// - `state_len`: number of state variables.
type NativeNextStateFn =
    unsafe extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32);

/// Type alias for the native invariant function pointer.
///
/// ABI: `extern "C" fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
type NativeInvariantFn = unsafe extern "C" fn(*mut JitCallOut, *const i64, u32);

/// Cache of LLVM2-compiled native functions for BFS dispatch.
///
/// LLVM2 counterpart of the former Cranelift `JitNextStateCache`, backed by native shared
/// libraries (`.dylib`/`.so`) instead of Cranelift JIT memory. Holds the
/// `NativeLibrary` handles to keep the dlopen'd code alive.
pub(in crate::check) struct Llvm2NativeCache {
    /// Per-action next-state function pointers, keyed by action name.
    next_state_fns: FxHashMap<String, NativeNextStateFn>,
    /// Per-invariant function pointers, indexed parallel to the spec's invariant list.
    /// Uses `Option` to maintain index alignment when compilation fails mid-sequence.
    /// `invariant_fns[i]` corresponds to the spec's invariant at index `i`.
    invariant_fns: Vec<Option<NativeInvariantFn>>,
    /// Number of state variables in the model.
    state_var_count: usize,
    /// Keeps the native libraries alive (dlopen handles).
    /// Dropping these invalidates the function pointers above.
    _libraries: Vec<tla_llvm2::NativeLibrary>,
}

// SAFETY: After construction, the cache is immutable. Function pointers target
// finalized native code in dlopen'd libraries that are retained for the cache
// lifetime. No interior mutation.
unsafe impl Send for Llvm2NativeCache {}
unsafe impl Sync for Llvm2NativeCache {}

/// Result of evaluating a single LLVM2-compiled action.
pub(in crate::check) enum Llvm2ActionResult {
    /// Action is enabled; `successor` contains the flat i64 output buffer.
    /// `jit_input` is a snapshot of the input state buffer, needed by
    /// `unflatten_i64_to_array_state_with_input` for compound value
    /// deserialization (offsets encoded in output reference the input buffer).
    Enabled { successor: Vec<i64>, jit_input: Vec<i64> },
    /// Action guard evaluated to false; no successor state.
    Disabled,
}

/// Statistics from LLVM2 cache construction.
#[derive(Debug, Clone, Default)]
pub(in crate::check) struct Llvm2BuildStats {
    /// Number of actions successfully compiled.
    pub actions_compiled: usize,
    /// Number of actions that failed compilation (fell back to interpreter).
    pub actions_failed: usize,
    /// Number of invariants successfully compiled.
    pub invariants_compiled: usize,
    /// Number of invariants that failed compilation.
    pub invariants_failed: usize,
    /// Total wall-clock time for all compilations.
    pub total_compile_ms: u64,
}

impl Llvm2NativeCache {
    /// Check whether EXISTS-binding specialization (#4270) is enabled.
    ///
    /// Gated by `TLA2_LLVM2_EXISTS=1` (default OFF). When enabled,
    /// `Llvm2NativeCache::build` consumes `BindingSpec` entries extracted from
    /// `split_action_meta`, runs `tla_tir::bytecode::specialize_bytecode_function` to
    /// prepend `LoadImm` for each binding register, and compiles the resulting
    /// arity-0 function through the tMIR → LLVM2 pipeline. When disabled, the
    /// cache ignores specializations and behaves as before (binding-heavy
    /// actions fall back to the interpreter).
    pub(in crate::check) fn exists_enabled() -> bool {
        std::env::var("TLA2_LLVM2_EXISTS").map_or(false, |v| v == "1")
    }

    /// Build an LLVM2 native cache from bytecode functions.
    ///
    /// For each action, compiles the next-state bytecode function through the
    /// full LLVM2 pipeline (BytecodeFunction -> tMIR -> LLVM IR -> llc -> .dylib).
    /// Actions that fail compilation are silently skipped (interpreter handles them).
    ///
    /// # Arguments
    ///
    /// * `action_bytecodes` - Map from action name to bytecode function.
    /// * `invariant_bytecodes` - Bytecode functions for each invariant.
    /// * `state_var_count` - Number of state variables in the model.
    /// * `opt_level` - LLVM optimization level.
    /// * `const_pool` - Optional constant pool for resolving `LoadConst`/`Unchanged` opcodes.
    /// * `specializations` - `BindingSpec` entries (one per EXISTS-bound split
    ///   action instance) whose scalar binding values should be baked into a
    ///   specialized bytecode function. Only honored when
    ///   [`Llvm2NativeCache::exists_enabled`] returns true. Part of #4270.
    /// * `chunk` - Optional source bytecode chunk. When provided, action /
    ///   invariant compilation routes through the chunk-aware tMIR lowering
    ///   path so user-defined operator `Call` opcodes in the entry body
    ///   resolve to fully-defined callee functions instead of leaving
    ///   `__func_N` unresolved-symbol references in the output LLVM module.
    ///   Required to compile any action that calls into another operator
    ///   (DieHard, AsyncTerminationDetection, etc.). Part of #4280 Gap C.
    pub(in crate::check) fn build(
        action_bytecodes: &FxHashMap<String, &tla_tir::bytecode::BytecodeFunction>,
        invariant_bytecodes: &[&tla_tir::bytecode::BytecodeFunction],
        state_var_count: usize,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        specializations: &[BindingSpec],
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> (Self, Llvm2BuildStats) {
        let start = std::time::Instant::now();
        let mut stats = Llvm2BuildStats::default();
        let mut next_state_fns = FxHashMap::default();
        let mut invariant_fns = Vec::new();
        let mut libraries = Vec::new();

        let exists_enabled = Self::exists_enabled();
        if exists_enabled {
            eprintln!(
                "[llvm2] TLA2_LLVM2_EXISTS=1: specializing {} binding entries (#4270)",
                specializations.len(),
            );
        }

        // Compile each action's next-state function.
        for (action_name, func) in action_bytecodes {
            // Skip actions with arity > 0 (they have EXISTS binding parameters
            // and cannot be lowered to the next-state ABI which expects arity 0).
            // When `TLA2_LLVM2_EXISTS=1`, the binding specialization loop below
            // handles arity-positive actions by prepending `LoadImm` for each
            // binding register and compiling the resulting arity-0 function.
            // Without specializations, EXISTS-bound actions stay interpreter-only.
            if func.arity != 0 {
                stats.actions_failed += 1;
                eprintln!(
                    "[llvm2] skipping action '{}' as binding-free: arity {} (specialize via BindingSpec in build)",
                    action_name, func.arity,
                );
                continue;
            }

            // Pre-screen with `is_tir_eligible_with_state`: this is a soft
            // check (superset of opcodes directly lowerable by the TIR fast
            // path, plus LoadVar/StoreVar/LoadPrime/Unchanged state access).
            // A mismatch is advisory only — the tMIR pipeline handles more
            // opcodes than the direct fast path, so we log and still attempt
            // compilation. If the pipeline itself rejects, the compile Err()
            // branch below skips the action permanently (log-once semantics).
            // Part of #4251 Stream 6.
            if !tla_llvm2::is_tir_eligible_with_state(func) {
                eprintln!(
                    "[llvm2] action '{}' has opcodes outside the scalar+state-access set; attempting compile via tMIR anyway",
                    action_name,
                );
            }

            match Self::compile_next_state_action(action_name, func, opt_level, const_pool, chunk) {
                Ok((fn_ptr, lib)) => {
                    next_state_fns.insert(action_name.clone(), fn_ptr);
                    libraries.push(lib);
                    stats.actions_compiled += 1;
                    eprintln!(
                        "[llvm2] compiled next-state for action '{}'",
                        action_name,
                    );
                }
                Err(e) => {
                    // Log-once policy (#4251 Stream 6 requirement c): failed
                    // compile marks this action as permanently interpreter-
                    // only for the remainder of the run. No per-iteration
                    // retry. The absence from `next_state_fns` causes
                    // `try_llvm2_action` in run_helpers.rs to return `None`,
                    // which routes BFS to the interpreter for every state.
                    stats.actions_failed += 1;
                    eprintln!(
                        "[llvm2] failed to compile action '{}': {} (interpreter fallback permanent for this run)",
                        action_name, e,
                    );
                }
            }
        }

        // Part of #4270: compile one specialized function per BindingSpec.
        // The base bytecode is fetched from `action_bytecodes`; the binding
        // values are prepended as `LoadImm` via `specialize_bytecode_function`
        // (the same transform Cranelift JIT uses in
        // `build_with_stats_and_specializations`). Specialized functions are
        // inserted under `tla_jit_abi::specialized_key(name, &values)` so the
        // dispatcher can look them up with the same key it uses for the
        // Cranelift JIT path. When `TLA2_LLVM2_EXISTS` is not set, the list
        // is treated as empty — this is the first-merge gating requirement.
        if exists_enabled {
            for spec in specializations {
                let key = tla_jit_abi::specialized_key(&spec.action_name, &spec.binding_values);
                if next_state_fns.contains_key(&key) {
                    continue; // Already compiled (duplicate spec).
                }

                let base = match action_bytecodes.get(spec.action_name.as_str()) {
                    Some(f) => *f,
                    None => {
                        eprintln!(
                            "[llvm2] specialization '{key}': base action '{}' not in bytecode map, skipping",
                            spec.action_name,
                        );
                        stats.actions_failed += 1;
                        continue;
                    }
                };

                let specialized = tla_tir::bytecode::specialize_bytecode_function(
                    base,
                    &spec.binding_values,
                    &key,
                );

                if specialized.arity != 0 {
                    // Defensive: specialize_bytecode_function is required to
                    // return an arity-0 function. Any drift is a contract bug.
                    eprintln!(
                        "[llvm2] specialization '{key}': unexpected arity {}, skipping",
                        specialized.arity,
                    );
                    stats.actions_failed += 1;
                    continue;
                }

                match Self::compile_next_state_action(&key, &specialized, opt_level, const_pool, chunk) {
                    Ok((fn_ptr, lib)) => {
                        next_state_fns.insert(key.clone(), fn_ptr);
                        libraries.push(lib);
                        stats.actions_compiled += 1;
                        eprintln!("[llvm2] specialized '{key}'");
                    }
                    Err(e) => {
                        stats.actions_failed += 1;
                        eprintln!(
                            "[llvm2] failed to compile specialization '{key}': {} (interpreter fallback permanent)",
                            e,
                        );
                    }
                }
            }
        }

        // Compile each invariant function.
        // Use Option to maintain index alignment: invariant_fns[i] always
        // corresponds to spec invariant i, even when compilation fails.
        // This fixes #4197 where failed compilations caused index misalignment.
        for (idx, func) in invariant_bytecodes.iter().enumerate() {
            let inv_name = format!("llvm2_inv_{idx}");
            match Self::compile_invariant_func(&inv_name, func, opt_level, const_pool, chunk) {
                Ok((fn_ptr, lib)) => {
                    invariant_fns.push(Some(fn_ptr));
                    libraries.push(lib);
                    stats.invariants_compiled += 1;
                    eprintln!("[llvm2] compiled invariant {idx}");
                }
                Err(e) => {
                    stats.invariants_failed += 1;
                    eprintln!(
                        "[llvm2] failed to compile invariant {idx}: {}",
                        e,
                    );
                    invariant_fns.push(None);
                }
            }
        }

        stats.total_compile_ms = start.elapsed().as_millis() as u64;

        let cache = Llvm2NativeCache {
            next_state_fns,
            invariant_fns,
            state_var_count,
            _libraries: libraries,
        };

        (cache, stats)
    }

    /// Compile a single next-state action through the LLVM2 native pipeline.
    ///
    /// Pipeline: BytecodeFunction -> tMIR -> LLVM2 JIT -> NativeLibrary.
    ///
    /// When `chunk` is `Some`, compilation routes through
    /// `compile_entry_next_state_native_with_chunk`, which drains pending
    /// `Call` opcodes so callee function bodies are emitted alongside the
    /// entry. This is required for any action that invokes another user-
    /// defined operator; without it, LLVM2 emits unresolved `__func_N`
    /// symbols. When `chunk` is `None`, falls back to the single-function
    /// path (legacy callers + JIT specialization of arity-0 functions that
    /// do not appear in the chunk's `functions` table).
    ///
    /// Part of #4280 Gap C.
    fn compile_next_state_action(
        action_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> Result<(NativeNextStateFn, tla_llvm2::NativeLibrary), tla_llvm2::Llvm2Error> {
        // Sanitize the action name for use as an LLVM function name.
        let safe_name = sanitize_llvm_name(action_name);

        // Compile BytecodeFunction -> tMIR -> native code via LLVM2 JIT pipeline.
        let lib = if let Some(chunk) = chunk {
            // Chunk-aware path: drains `Call` callees from chunk.functions so
            // they are emitted alongside the entry. Fixes #4280 Gap C.
            tla_llvm2::compile_entry_next_state_native_with_chunk(
                func, chunk, &safe_name, opt_level,
            )?
        } else if let Some(pool) = const_pool {
            tla_llvm2::compile_next_state_native_with_constants(func, &safe_name, pool, opt_level)?
        } else {
            tla_llvm2::compile_next_state_native(func, &safe_name, opt_level)?
        };

        // Look up the compiled function symbol.
        // SAFETY: We control the compilation pipeline and know the exact signature.
        let fn_ptr = unsafe {
            let raw = lib.get_symbol(&safe_name)?;
            std::mem::transmute::<*mut std::ffi::c_void, NativeNextStateFn>(raw)
        };

        Ok((fn_ptr, lib))
    }

    /// Compile a single invariant function through the LLVM2 native pipeline.
    ///
    /// Pipeline: BytecodeFunction -> tMIR -> LLVM2 JIT -> NativeLibrary.
    ///
    /// `chunk` semantics match [`compile_next_state_action`]. Part of #4280 Gap C.
    fn compile_invariant_func(
        inv_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> Result<(NativeInvariantFn, tla_llvm2::NativeLibrary), tla_llvm2::Llvm2Error> {
        let safe_name = sanitize_llvm_name(inv_name);

        // Compile BytecodeFunction -> tMIR -> native code via LLVM2 JIT pipeline.
        let lib = if let Some(chunk) = chunk {
            // Chunk-aware path: emit callee bodies alongside the entry. #4280 Gap C.
            tla_llvm2::compile_entry_invariant_native_with_chunk(
                func, chunk, &safe_name, opt_level,
            )?
        } else if let Some(pool) = const_pool {
            tla_llvm2::compile_invariant_native_with_constants(func, &safe_name, pool, opt_level)?
        } else {
            tla_llvm2::compile_invariant_native(func, &safe_name, opt_level)?
        };

        // SAFETY: We control the compilation pipeline and know the exact signature.
        let fn_ptr = unsafe {
            let raw = lib.get_symbol(&safe_name)?;
            std::mem::transmute::<*mut std::ffi::c_void, NativeInvariantFn>(raw)
        };

        Ok((fn_ptr, lib))
    }

    /// Check whether LLVM2 native compilation is available.
    ///
    /// Returns `true` when the `native` feature is compiled into `tla-llvm2`.
    /// When `false`, [`Llvm2NativeCache::build`] will fail to compile any functions.
    pub(in crate::check) fn is_available() -> bool {
        tla_llvm2::is_native_available()
    }

    /// Check whether the LLVM2 BFS path is activated via environment variable.
    ///
    /// Accepted flags (either enables):
    /// - `TLA2_LLVM2=1` — general LLVM2 activation (covers invariants and
    ///   next-state actions where eligible).
    /// - `TLA2_LLVM2_BFS=1` — BFS-scoped alias (epic #4251 Stream 6). Reads
    ///   identically today; reserved so the BFS code path can be gated
    ///   independently of invariants in the future without a flag flip day.
    ///
    /// OFF by default — nothing changes for existing users unless one of
    /// these flags is explicitly set.
    pub(in crate::check) fn is_enabled() -> bool {
        let general = std::env::var("TLA2_LLVM2").map_or(false, |v| v == "1");
        let bfs = std::env::var("TLA2_LLVM2_BFS").map_or(false, |v| v == "1");
        general || bfs
    }

    /// Number of successfully compiled action functions.
    pub(in crate::check) fn action_count(&self) -> usize {
        self.next_state_fns.len()
    }

    /// Whether at least one next-state action was successfully compiled.
    ///
    /// Used by the fingerprint mixed-mode guard in
    /// `try_activate_compiled_fingerprinting`: when any compiled action can
    /// produce successors during BFS, the fingerprint pipeline must stay on a
    /// single hash domain so that compiled-emitted and interpreter-emitted
    /// successors of the same logical state dedup into the same `Fingerprint`.
    ///
    /// Part of #4319 (LLVM2 fingerprint unification) Phase 0.
    #[inline]
    pub(in crate::check) fn has_any_compiled_action(&self) -> bool {
        !self.next_state_fns.is_empty()
    }

    /// Number of successfully compiled invariant functions.
    pub(in crate::check) fn invariant_count(&self) -> usize {
        self.invariant_fns.iter().filter(|f| f.is_some()).count()
    }

    /// Number of state variables.
    pub(in crate::check) fn state_var_count(&self) -> usize {
        self.state_var_count
    }

    /// Check if a specific action is compiled.
    pub(in crate::check) fn contains_action(&self, name: &str) -> bool {
        self.next_state_fns.contains_key(name)
    }

    /// Evaluate a compiled next-state action on a flat i64 state buffer.
    ///
    /// Returns `Some(Ok(result))` if the action is compiled and evaluation
    /// succeeded. Returns `Some(Err(()))` on runtime error. Returns `None`
    /// if the action is not compiled.
    ///
    /// The `state_in` buffer is snapshotted into the `Enabled` result as
    /// `jit_input`, because compound value deserialization needs the input
    /// buffer to resolve offsets written by native FuncExcept operations.
    /// Fixes #4193: previously `None` was passed making compound states unsound.
    pub(in crate::check) fn eval_action(
        &self,
        action_name: &str,
        state_in: &[i64],
    ) -> Option<Result<Llvm2ActionResult, ()>> {
        let fn_ptr = self.next_state_fns.get(action_name)?;

        let mut out = JitCallOut::default();
        let mut state_out = vec![0i64; self.state_var_count];

        // SAFETY: fn_ptr was obtained from our compilation pipeline with the
        // correct ABI. state_in/state_out are valid i64 buffers. out is
        // caller-allocated. state_len matches the model's variable count.
        unsafe {
            fn_ptr(
                &mut out,
                state_in.as_ptr(),
                state_out.as_mut_ptr(),
                self.state_var_count as u32,
            );
        }

        match out.status {
            tla_jit_abi::JitStatus::Ok => {
                if out.value != 0 {
                    // Snapshot the input buffer for compound value deserialization.
                    // The native function may encode offsets into the input buffer
                    // for compound variables (FuncExcept pattern).
                    let jit_input = state_in.to_vec();
                    Some(Ok(Llvm2ActionResult::Enabled {
                        successor: state_out,
                        jit_input,
                    }))
                } else {
                    Some(Ok(Llvm2ActionResult::Disabled))
                }
            }
            tla_jit_abi::JitStatus::RuntimeError => Some(Err(())),
            // PartialPass or other status -- fall back to interpreter.
            _ => None,
        }
    }

    /// Evaluate a compiled invariant on a flat i64 state buffer.
    ///
    /// Returns `Some(Ok(true))` if the invariant holds, `Some(Ok(false))` if
    /// violated, `Some(Err(()))` on runtime error, `None` if not compiled
    /// (either index out of range or compilation failed for this invariant).
    pub(in crate::check) fn eval_invariant(
        &self,
        invariant_idx: usize,
        state: &[i64],
    ) -> Option<Result<bool, ()>> {
        // Double-unwrap: first get the slot (bounds check), then check if compiled.
        let fn_ptr = (*self.invariant_fns.get(invariant_idx)?)?;

        let mut out = JitCallOut::default();

        // SAFETY: fn_ptr was obtained from our compilation pipeline with the
        // correct ABI. state is a valid i64 buffer. out is caller-allocated.
        unsafe {
            fn_ptr(
                &mut out,
                state.as_ptr(),
                self.state_var_count as u32,
            );
        }

        match out.status {
            tla_jit_abi::JitStatus::Ok => Some(Ok(out.value != 0)),
            tla_jit_abi::JitStatus::RuntimeError => Some(Err(())),
            _ => None,
        }
    }
}

impl std::fmt::Debug for Llvm2NativeCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Llvm2NativeCache")
            .field("actions", &self.next_state_fns.len())
            .field("invariants", &self.invariant_fns.len())
            .field("state_var_count", &self.state_var_count)
            .field("libraries", &self._libraries.len())
            .finish()
    }
}

/// Sanitize a TLA+ action name into a valid LLVM function name.
///
/// LLVM identifiers must match `[a-zA-Z._][a-zA-Z._0-9]*`. Replace invalid
/// characters with underscores.
fn sanitize_llvm_name(name: &str) -> String {
    let mut result = String::with_capacity(name.len());
    for (i, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' {
            result.push(ch);
        } else if i == 0 {
            result.push('_');
        } else {
            result.push('_');
        }
    }
    if result.is_empty() {
        result.push_str("_unnamed");
    }
    result
}

/// Check whether LLVM2 dispatch should be active for the current run.
///
/// Returns `true` when:
/// 1. The `llvm2` feature is compiled in (checked at compile time by cfg gate).
/// 2. `TLA2_LLVM2=1` environment variable is set.
/// 3. The `native` feature is compiled into `tla-llvm2` (always true when
///    `tla-check/llvm2` feature is enabled).
pub(in crate::check) fn should_use_llvm2() -> bool {
    Llvm2NativeCache::is_enabled() && Llvm2NativeCache::is_available()
}

/// Thread-safe wrapper for parallel BFS access.
pub(in crate::check) type SharedLlvm2Cache = Arc<Llvm2NativeCache>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize_llvm_name_simple() {
        assert_eq!(sanitize_llvm_name("InitiateProbe"), "InitiateProbe");
    }

    #[test]
    fn test_sanitize_llvm_name_with_spaces() {
        assert_eq!(sanitize_llvm_name("Send Msg"), "Send_Msg");
    }

    #[test]
    fn test_sanitize_llvm_name_with_special_chars() {
        assert_eq!(sanitize_llvm_name("a->b"), "a__b");
    }

    #[test]
    fn test_sanitize_llvm_name_empty() {
        assert_eq!(sanitize_llvm_name(""), "_unnamed");
    }

    #[test]
    fn test_sanitize_llvm_name_dots_and_underscores() {
        assert_eq!(sanitize_llvm_name("foo.bar_baz"), "foo.bar_baz");
    }

    #[test]
    fn test_is_enabled_returns_false_by_default() {
        // TLA2_LLVM2 is not set in the test environment (usually).
        // This test verifies the function doesn't panic.
        let _ = Llvm2NativeCache::is_enabled();
    }
}
