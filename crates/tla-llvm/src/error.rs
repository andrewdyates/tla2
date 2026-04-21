// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for the LLVM AOT backend.

use thiserror::Error;

/// Errors that can occur while lowering bytecode to LLVM IR or compiling it.
#[derive(Debug, Error)]
pub enum LlvmError {
    /// Error during LLVM IR generation.
    #[error("LLVM IR emission failed: {0}")]
    IrEmission(String),

    /// Opcode is not supported by the LLVM backend.
    #[error("unsupported opcode for LLVM backend: {0}")]
    UnsupportedOpcode(String),

    /// Bytecode function is not eligible for LLVM lowering.
    #[error("bytecode function is not eligible for LLVM lowering: {reason}")]
    NotEligible { reason: String },

    /// Error during native compilation with llc or clang.
    #[error("native compilation failed: {0}")]
    CompileError(String),

    /// Error during object or shared library linking.
    #[error("linking failed: {0}")]
    LinkError(String),

    /// Error loading the compiled shared library.
    #[error("failed to load compiled library: {0}")]
    LoadError(String),

    /// Filesystem I/O error.
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}
