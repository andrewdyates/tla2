// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Re-exports from `tla-jit-abi` for the pure-data liveness predicate types.
//!
//! These types (`LivenessPredInfo`, `LivenessPredKind`, `ScalarCompOp`,
//! `LivenessCompileStats`, and the compiled-function pointer aliases) used to
//! live here and in `tla-jit::compiled_liveness` as two independent copies.
//! Stage 2d of #4251 (epic) consolidated them in the `tla-jit-abi` leaf crate
//! so both the Cranelift and LLVM2 backends share a single source of truth
//! without creating a cargo cycle. Part of #4267.
//!
//! Existing `crate::runtime_abi::liveness_types::*` imports throughout
//! `tla-llvm2` continue to resolve unchanged.

pub use tla_jit_abi::liveness_types::{
    CompiledAcceptanceCheckFn, CompiledActionPredBatchFn, CompiledStatePredBatchFn,
    LivenessCompileStats, LivenessPredInfo, LivenessPredKind, ScalarCompOp,
};
