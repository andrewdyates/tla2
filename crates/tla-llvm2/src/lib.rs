// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM2 compilation backend for TLA2.
//!
//! Takes [`tmir::Module`] output from [`tla_tmir`] and compiles it to native
//! code via the LLVM2 verified compiler backend. This crate is the bridge
//! between TLA+-specific IR lowering (tla-tmir) and the language-agnostic
//! LLVM2 compiler.
//!
//! # Architecture
//!
//! ```text
//! TLA+ Spec
//!     |  (tla-core: parse + resolve)
//!     v
//! TIR (typed bytecode)
//!     |  (tla-tmir: TLA+ semantics -> tMIR)
//!     v
//! tmir::Module (SSA IR)
//!     |  (tla-llvm2: THIS CRATE)
//!     v
//! LLVM2 backend (optimize + codegen)
//!     |
//!     v
//! Native code (AArch64/x86)
//! ```
//!
//! # Pipeline
//!
//! 1. **Validate** the tMIR module structure ([`lower::validate_module`])
//! 2. **Lower** tMIR instructions to LLVM2 IR ([`lower::lower_module`])
//! 3. **Compile** to native code via LLVM2 ([`compile::compile_module`])
//!
//! # Optimization Levels
//!
//! - [`OptLevel::O1`]: Fast compilation (~50-200ms). Tier 1 warmup.
//! - [`OptLevel::O3`]: Peak throughput (~0.5-2s). Tier 2 steady-state.
//!
//! # ABI Compatibility
//!
//! Uses the `extern "C"` ABI re-exported from `tla-jit-abi` via
//! [`crate::runtime_abi::abi`]:
//! - Invariant: `fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
//! - Next-state: `fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
//!
//! # Example
//!
//! ```no_run
//! use tla_llvm2::compile_module;
//! # fn example(module: &tmir::Module) -> Result<(), tla_llvm2::Llvm2Error> {
//! let compiled = compile_module(module)?;
//! println!("Compiled {} functions ({} instructions, {} helper calls)",
//!     compiled.stats.functions, compiled.stats.instructions,
//!     compiled.stats.helper_calls);
//! # Ok(())
//! # }
//! ```

pub mod artifact_cache;
pub mod bfs_level;
pub(crate) mod compiled_fingerprint;
pub mod compiled_liveness;
pub(crate) mod emit;
mod error;
pub mod pgo;
pub mod prefetch;
pub mod runtime_abi;
pub mod tmir_lower;
/// Backwards-compatibility alias. `tir_lower` was renamed to `tmir_lower`
/// per the supremacy design doc (§11 Stream 3). Call sites that still
/// reference `tir_lower::*` continue to work via this re-export.
pub use tmir_lower as tir_lower;
pub mod compile;
pub mod lower;
mod native_bfs;
pub mod runtime;
#[cfg(test)]
mod validate_ir;

#[inline]
pub fn ensure_jit_execute_mode() {
    #[cfg(feature = "native")]
    llvm2_codegen::ensure_jit_execute_mode();
}

pub use bfs_level::{
    ActionDescriptor, InvariantDescriptor, Llvm2BfsLevelCapabilities, Llvm2BfsLevelError,
    Llvm2BfsLevelNative, Llvm2BfsLevelNativeMetadata, Llvm2BfsLevelOutcome, Llvm2BfsLevelPrototype,
    Llvm2BfsLevelStatus, Llvm2BfsParentArenaAbi, Llvm2BfsSuccessorArenaAbi, Llvm2CompiledAction,
    Llvm2CompiledInvariant, Llvm2FusedLevelFn, Llvm2InvariantStatus, Llvm2SuccessorArena,
    LLVM2_BFS_LEVEL_ABI_VERSION, LLVM2_BFS_NO_INDEX,
};
#[cfg(feature = "native")]
pub use compile::extern_symbol_map_for_tests;
pub use compile::{
    compile_and_link, compile_bfs_level_native, compile_bfs_level_native_actions_only,
    compile_bfs_level_native_with_state_constraints, compile_bfs_step,
    compile_entry_invariant_native_with_chunk,
    compile_entry_invariant_native_with_chunk_and_layout,
    compile_entry_next_state_native_with_chunk,
    compile_entry_next_state_native_with_chunk_and_layout, compile_invariant,
    compile_invariant_native, compile_invariant_native_with_constants,
    compile_invariant_native_with_constants_and_layout, compile_invariant_with_constants,
    compile_module, compile_module_native, compile_module_native_with_extern_symbols,
    compile_next_state, compile_next_state_native, compile_next_state_native_with_constants,
    compile_next_state_native_with_constants_and_layout, compile_next_state_with_constants,
    compile_spec_invariant, compile_spec_invariant_native, compile_spec_next_state,
    compile_spec_next_state_native, find_llc, is_native_available,
    llvm2_entry_counter_dispatch_gate_limit, CompiledBfsLevel, CompiledBfsStep, CompiledModule,
    Llvm2BfsLevelNativeAction, Llvm2BfsLevelNativeInvariant, Llvm2BfsLevelNativeStateConstraint,
    NativeExternSymbol, NativeExternSymbolOverlay, NativeLibrary, OptLevel,
    LLVM2_ENTRY_COUNTER_DISPATCH_GATE_ENV,
};
pub use error::Llvm2Error;
pub use lower::LoweringStats;
pub use runtime::{find_helper, RuntimeHelper, RUNTIME_HELPERS};
pub use tmir_lower::{
    is_tir_eligible, is_tir_eligible_with_state, lower_tir_to_llvm_ir,
    lower_tir_to_llvm_ir_with_state, StateAccessConfig, TirLoweredModule, TirLoweringStats,
};
