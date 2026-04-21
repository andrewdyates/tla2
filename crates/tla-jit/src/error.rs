// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JIT compilation errors

use thiserror::Error;

/// JIT compilation error types
#[derive(Debug, PartialEq, Error)]
pub enum JitError {
    /// Failed to initialize the JIT context
    #[error("JIT initialization failed: {0}")]
    InitError(String),

    /// Failed to compile a function
    #[error("Compilation failed: {0}")]
    CompileError(String),

    /// Unsupported TLA+ expression type
    #[error("Unsupported expression: {0}")]
    UnsupportedExpr(String),

    /// Type mismatch during compilation
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    /// Internal Cranelift error
    #[error("Cranelift error: {0}")]
    CraneliftError(String),

    /// Bytecode function is not eligible for JIT compilation
    #[error("Not JIT-eligible: {reason}")]
    NotEligible { reason: String },

    /// Unsupported bytecode opcode for JIT lowering
    #[error("Unsupported bytecode opcode: {0}")]
    UnsupportedOpcode(String),

    /// Runtime error from JIT-compiled code (e.g., division by zero)
    #[error("JIT runtime error: {kind:?}")]
    RuntimeError {
        kind: crate::abi::JitRuntimeErrorKind,
    },
}

impl From<crate::jit_native::ModuleError> for JitError {
    fn from(e: crate::jit_native::ModuleError) -> Self {
        JitError::CraneliftError(e.to_string())
    }
}

impl From<tla_jit_runtime::JitRuntimeError> for JitError {
    fn from(e: tla_jit_runtime::JitRuntimeError) -> Self {
        match e {
            tla_jit_runtime::JitRuntimeError::CompileError(msg) => JitError::CompileError(msg),
            tla_jit_runtime::JitRuntimeError::UnsupportedExpr(msg) => {
                JitError::UnsupportedExpr(msg)
            }
            tla_jit_runtime::JitRuntimeError::TypeMismatch { expected, actual } => {
                JitError::TypeMismatch { expected, actual }
            }
            tla_jit_runtime::JitRuntimeError::NotEligible { reason } => {
                JitError::NotEligible { reason }
            }
            tla_jit_runtime::JitRuntimeError::UnsupportedOpcode(msg) => {
                JitError::UnsupportedOpcode(msg)
            }
            tla_jit_runtime::JitRuntimeError::RuntimeError { kind } => {
                JitError::RuntimeError { kind }
            }
        }
    }
}
