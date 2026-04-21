// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backend-agnostic JIT runtime types for TLA2.
//!
//! This crate provides the shared runtime infrastructure used by both the
//! Cranelift backend (`tla-jit`) and the LLVM2 backend (`tla-llvm2`):
//!
//! - **ABI types** — `JitCallOut`, `JitStatus`, `JitRuntimeErrorKind`, function pointer types,
//!   `extern "C"` runtime helpers for compound operations, compound scratch buffer
//! - **Flat state** — `FlatState`, `FlatStateSchema`, `VarEncoding` for mapping TLA+ states to i64 arrays
//! - **Compound layout** — `CompoundLayout`, `StateLayout`, `VarLayout` for serializing
//!   compound TLA+ values (records, sequences, sets, functions, tuples) to flat i64 buffers
//! - **Fingerprint set** — `AtomicFpSet`, `ResizableAtomicFpSet` lock-free dedup sets
//! - **Fingerprint functions** — xxh3-based fingerprint computation
//! - **Error types** — `JitRuntimeError` (backend-agnostic subset of JitError)
//!
//! Part of #4199: Extract tla-jit-runtime shared crate.

pub mod abi;
pub mod atomic_fp_set;
pub mod bfs_descriptors;
pub mod bfs_output;
pub mod compound_layout;
pub mod error;
pub mod fingerprint;
pub mod flat_state;
pub mod helpers;

// Re-export key types at crate root for convenience.
pub use abi::{
    clear_compound_scratch, compound_scratch_guard, read_compound_scratch, CompoundScratchGuard,
    JitCallOut, JitExprFn, JitFn0, JitInvariantFn, JitNextStateFn, JitRuntimeErrorKind, JitStatus,
    COMPOUND_SCRATCH_BASE,
};
pub use atomic_fp_set::{
    atomic_fp_set_probe, resizable_fp_set_probe, AtomicFpSet, CumulativeProbeStats, InsertResult,
    ProbeStats, ResizableAtomicFpSet,
};
pub use bfs_descriptors::{
    ActionDescriptor, BfsStepSpec, CompiledActionFn, CompiledInvariantFn, InvariantDescriptor,
};
pub use bfs_output::{
    BfsBatchResult, BfsStepError, BfsStepOutput, FlatBfsStepOutput, FlatBfsStepOutputRef,
};
pub use compound_layout::{
    deserialize_value, infer_layout, infer_var_layout, serialize_value, CompoundLayout, StateLayout,
    VarLayout, TAG_BOOL, TAG_FUNC, TAG_INT, TAG_RECORD, TAG_SEQ, TAG_SET, TAG_STRING, TAG_TUPLE,
};
pub use error::JitRuntimeError;
pub use fingerprint::{
    jit_xxh3_batch_fingerprint_128, jit_xxh3_batch_fingerprint_64, jit_xxh3_fingerprint_128,
    jit_xxh3_fingerprint_64,
};
pub use flat_state::{
    flat_to_state, flat_to_state_from_slice, state_to_flat, state_to_flat_reuse, FlatState,
    FlatStateSchema, VarEncoding,
};
pub use helpers::{bindings_to_jit_i64, classify_value, value_to_jit_i64};
