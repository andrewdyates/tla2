// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error types for tMIR lowering.

/// Errors that can occur during bytecode-to-tMIR lowering.
#[derive(Debug, thiserror::Error)]
pub enum TmirError {
    /// Error during tMIR construction.
    #[error("tMIR emission failed: {0}")]
    Emission(String),

    /// Opcode is not supported by the tMIR backend.
    #[error("unsupported opcode for tMIR backend: {0}")]
    UnsupportedOpcode(String),

    /// Bytecode function is not eligible for tMIR lowering.
    #[error("bytecode function is not eligible for tMIR lowering: {reason}")]
    NotEligible { reason: String },
}
