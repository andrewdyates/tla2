// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for GPU operations.

/// Errors that can occur during GPU initialization or compute dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum GpuError {
    /// No suitable GPU adapter was found on this system.
    #[error("no GPU adapter found: request adapter returned None")]
    NoAdapter,

    /// Failed to obtain a GPU device from the adapter.
    #[error("failed to request GPU device: {0}")]
    DeviceRequest(#[from] wgpu::RequestDeviceError),

    /// A buffer mapping operation failed.
    #[error("GPU buffer mapping failed")]
    BufferMapping,

    /// The input batch is empty (zero states).
    #[error("fingerprint batch is empty: nothing to compute")]
    EmptyBatch,

    /// Variable count is zero.
    #[error("variable count is zero: no variables to fingerprint")]
    ZeroVariables,

    /// The states buffer length is not divisible by the variable count.
    #[error(
        "states buffer length {len} is not divisible by variable count {num_vars}"
    )]
    StateLengthMismatch {
        /// Total number of u64 values in the states buffer.
        len: usize,
        /// Expected number of variables per state.
        num_vars: usize,
    },

    /// The salts buffer length does not match the variable count.
    #[error("salts buffer length {salts_len} != variable count {num_vars}")]
    SaltLengthMismatch {
        /// Number of salts provided.
        salts_len: usize,
        /// Expected number of variables.
        num_vars: usize,
    },
}
