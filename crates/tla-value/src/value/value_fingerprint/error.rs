// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint error and result types for TLC-compatible FP64 fingerprinting.

use thiserror::Error;

/// Error during TLC-compatible FP64 fingerprinting.
///
/// These errors occur when a value exceeds the limits of TLC's fingerprinting
/// scheme (i32 lengths, i64 domain keys). Rather than panicking, callers
/// receive a structured error they can report to the user.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum FingerprintError {
    /// A length or index exceeds TLC's i32 range during fingerprinting.
    #[error(
        "Fingerprint overflow: {context} exceeds TLC-compatible i32 range: {value} > {}",
        i32::MAX
    )]
    I32Overflow {
        value: String,
        context: &'static str,
    },

    /// An IntIntervalFunc domain key overflows i64 during fingerprinting.
    #[error("Fingerprint overflow: IntIntervalFunc domain key overflow: {min} + {offset} exceeds i64 range")]
    I64DomainOverflow { min: i64, offset: usize },

    /// TLC-compatible normalization (sort/dedup) failed during fingerprinting.
    ///
    /// This occurs when a set or function domain contains incomparable values
    /// that TLC's comparison ordering cannot handle.
    #[error("Fingerprint normalization failed: {0}")]
    TlcNormalization(String),
}

pub type FingerprintResult<T> = Result<T, FingerprintError>;
