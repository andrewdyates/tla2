// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ JIT Compiler using Cranelift
//!
//! This crate provides JIT compilation of TLA+ expressions to native code
//! via Cranelift. The goal is ~20x speedup over TLC with ~500ms compile time.
//!
//! # Architecture
//!
//! ```text
//! TLA+ Expr → ExprCompiler → Cranelift IR → Native Code
//! ```
//!
//! # Current Status
//!
//! This is a prototype implementing basic expression compilation:
//! - Integer arithmetic: +, -, *, div, mod
//! - Comparisons: =, <, >, <=, >=
//! - Boolean operations: /\, \/, ~
//!
//! # Example
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use tla_jit::JitContext;
//! use tla_core::ast::Unit;
//! use tla_core::{lower, parse_to_syntax_tree, FileId};
//!
//! let tree = parse_to_syntax_tree(
//!     r#"---- MODULE M ----
//! Op == 2 + 3 * 4
//! ===="#,
//! );
//! let lowered = lower(FileId(0), &tree);
//! assert!(lowered.errors.is_empty(), "Lower errors: {:?}", lowered.errors);
//! let module = lowered.module.expect("Expected module");
//! let expr = match &module.units[0].node {
//!     Unit::Operator(op) => &op.body,
//!     other => panic!("Expected operator, got: {other:?}"),
//! };
//!
//! let mut jit = JitContext::new()?;
//! let func = jit.compile_expr(expr)?;
//! let result = func();
//! assert_eq!(result, 14);
//! # Ok(())
//! # }
//! ```

pub mod abi;
pub mod atomic_fp_set;
pub mod bfs_step;
pub mod bytecode_lower;
pub mod compiled_bfs;
pub mod compiled_bfs_level;
pub(crate) mod compiled_fingerprint;
pub mod compiled_liveness;
mod compiler;
pub mod compound_layout;
pub(crate) mod flat_state;
pub(crate) mod deoptimization;
mod error;
pub(crate) mod jit_native;
pub mod recompilation;
pub(crate) mod speculative;
pub mod tiered;
pub mod tir_inlining;
pub(crate) mod type_profile;
pub(crate) mod type_specializer;

#[cfg(test)]
mod tests;

pub use abi::{
    JitCallOut, JitExprFn, JitFn0, JitInvariantFn, JitNextStateFn, JitRuntimeErrorKind, JitStatus,
};
pub use atomic_fp_set::{
    atomic_fp_set_probe, resizable_fp_set_probe, AtomicFpSet, CumulativeProbeStats, InsertResult,
    ProbeStats, ResizableAtomicFpSet,
};
pub use bfs_step::{
    jit_fp_set_probe, jit_xxh3_fingerprint_128, jit_xxh3_fingerprint_64, ActionDescriptor,
    BfsStepCompiler, BfsStepResult, BfsStepSpec, CompiledActionFn, CompiledInvariantFn,
    InvariantDescriptor, JitBfsStepFn,
};
pub use bytecode_lower::{
    bindings_to_jit_i64, check_eligibility, check_eligibility_with_constants,
    check_opcode_eligibility, check_opcode_eligibility_with_constants, specialized_key,
    value_to_jit_i64, ActionMeta, BindingSpec, BytecodeLowerer, JitActionResult,
    JitDispatchCounters, JitInvariantCache, JitInvariantResult, JitNextStateCache,
    NextStateDispatchCounters, QuantifierDomains,
};
pub use compiled_bfs::{
    BfsBatchResult, BfsLevelResult, BfsMultiLevelResult, BfsStepError, BfsStepOutput,
    BfsStepScratch, CompiledBfsStep, FlatBfsStepOutput, FlatBfsStepOutputRef,
};
pub use compiled_bfs_level::{
    BfsLevelLoopResult, CompiledBfsLevel, CompiledLevelResult, CompiledMultiLevelResult,
    JitBfsLevelFn,
};
pub use compiled_fingerprint::{CompiledFingerprint128Fn, CompiledFingerprintFn};
pub use compiled_liveness::{compile_acceptance_checker, CompiledSccHelpers, SccHelperStats};
pub use compiled_liveness::{
    compile_liveness_predicates, CompiledActionPredBatchFn, CompiledLivenessBatch,
    CompiledStatePredBatchFn, LivenessCompileStats, LivenessPredInfo, LivenessPredKind,
    ScalarCompOp,
};
pub use compiler::JitContext;
pub use compound_layout::{
    deserialize_value, infer_layout, infer_var_layout, serialize_value, CompoundLayout,
    StateLayout, VarLayout,
};
pub use error::JitError;
pub use flat_state::{
    flat_to_state, flat_to_state_from_slice, state_to_flat, state_to_flat_reuse, FlatState,
    FlatStateSchema,
};
pub use recompilation::{RecompilationController, RecompilationResult};
pub use tiered::{
    ActionProfile, CacheBuildStats, CompilationTier, CompileStats, TierConfig, TierManager,
    TierPromotion, TierSummary,
};
pub use tir_inlining::{
    inline_and_compile, preprocess_tir_for_jit, JitInliningConfig, JitPreprocessConfig,
    PreprocessStats,
};
pub use type_profile::{classify_value, SpecType, TypeProfile, TypeProfiler};
pub use type_specializer::SpecializationPlan;

use cranelift_codegen::settings::{self, Configurable};
use jit_native::{JITBuilder, JITModule};

/// Create a Cranelift JIT module configured for the host target.
///
/// Shared by both `JitContext` (AST compiler) and `BytecodeLowerer` (bytecode compiler)
/// to avoid duplicating Cranelift flag/ISA/builder setup.
pub(crate) fn create_jit_module() -> Result<JITModule, JitError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| JitError::InitError(e.to_string()))?;
    flag_builder
        .set("is_pic", "false")
        .map_err(|e| JitError::InitError(e.to_string()))?;
    flag_builder
        .set("opt_level", "speed")
        .map_err(|e| JitError::InitError(e.to_string()))?;

    let isa_builder = jit_native::native_isa_builder()
        .map_err(|e| JitError::InitError(format!("Native ISA not available: {e}")))?;
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| JitError::InitError(e.to_string()))?;

    let mut builder = JITBuilder::with_isa(isa, jit_native::default_libcall_names());

    // Register runtime helper symbols so the JIT can resolve them at link time.
    // These are `#[no_mangle] pub extern "C"` functions defined in this crate
    // that JIT-compiled code calls via Cranelift's Import linkage.
    builder.symbol(
        "jit_pow_i64",
        bytecode_lower::scalar_ops::jit_pow_i64 as *const u8,
    );
    builder.symbol(
        "jit_set_contains_i64",
        abi::jit_set_contains_i64 as *const u8,
    );
    builder.symbol("jit_record_get_i64", abi::jit_record_get_i64 as *const u8);
    builder.symbol("jit_func_apply_i64", abi::jit_func_apply_i64 as *const u8);
    builder.symbol("jit_compound_count", abi::jit_compound_count as *const u8);
    builder.symbol("jit_seq_get_i64", abi::jit_seq_get_i64 as *const u8);
    builder.symbol(
        "jit_func_set_membership_check",
        abi::jit_func_set_membership_check as *const u8,
    );
    builder.symbol(
        "jit_record_new_scalar",
        abi::jit_record_new_scalar as *const u8,
    );
    builder.symbol("jit_set_diff_i64", abi::jit_set_diff_i64 as *const u8);
    builder.symbol("jit_seq_tail", abi::jit_seq_tail as *const u8);
    builder.symbol("jit_seq_append", abi::jit_seq_append as *const u8);
    builder.symbol(
        "jit_set_union_i64",
        abi::jit_set_union_i64 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_fingerprint_64",
        bfs_step::jit_xxh3_fingerprint_64 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_fingerprint_128",
        bfs_step::jit_xxh3_fingerprint_128 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_batch_fingerprint_64",
        bfs_step::jit_xxh3_batch_fingerprint_64 as *const u8,
    );
    builder.symbol(
        "jit_xxh3_batch_fingerprint_128",
        bfs_step::jit_xxh3_batch_fingerprint_128 as *const u8,
    );

    Ok(JITModule::new(builder))
}
