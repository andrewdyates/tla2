// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error types for the LLVM2 compilation backend.

/// Errors that can occur during tMIR-to-native compilation via LLVM2.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Llvm2Error {
    /// The input tMIR module is malformed or contains unsupported constructs.
    #[error("invalid tMIR module: {0}")]
    InvalidModule(String),

    /// A tMIR instruction is not yet supported by the LLVM2 lowering.
    #[error("unsupported tMIR instruction: {0}")]
    UnsupportedInst(String),

    /// Error during LLVM2 IR construction.
    #[error("LLVM2 IR emission failed: {0}")]
    Emission(String),

    /// Error during LLVM2 optimization passes.
    #[error("LLVM2 optimization failed: {0}")]
    Optimization(String),

    /// Error during native code generation (register allocation, ISel, encoding).
    #[error("LLVM2 code generation failed: {0}")]
    CodeGen(String),

    /// Error loading or linking the compiled native code.
    #[error("native code loading failed: {0}")]
    Loading(String),

    /// The LLVM2 backend is not available (feature not enabled or library missing).
    #[error("LLVM2 backend not available: {0}")]
    BackendUnavailable(String),

    /// Error from the upstream tMIR lowering phase.
    #[error("tMIR lowering error: {source}")]
    TmirLowering {
        #[from]
        source: tla_tmir::TmirError,
    },
}
