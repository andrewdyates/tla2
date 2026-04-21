// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLC-compatible FP64 fingerprinting for `Value`.
//!
//! Each value type extends a running fingerprint using TLC's incremental
//! approach: type tag, then length/size, then component values recursively.
//!
//! This module is split by concern:
//! - `error`: public fingerprint error/result types
//! - `helpers`: shared numeric-conversion utilities
//! - `concrete`: concrete value families (Set, Func, Record, etc.)
//! - `lazy`: lazy/derived value families (Subset, SetCup, Closure, etc.)

mod concrete;
mod error;
mod helpers;
mod lazy;

pub use error::{FingerprintError, FingerprintResult};
pub(super) use helpers::fp_usize_to_i32;

use super::Value;

impl Value {
    /// Extend a fingerprint with this value using TLC-compatible FP64 algorithm.
    ///
    /// This method implements TLC's incremental fingerprinting approach where
    /// fingerprints are extended one component at a time. This is critical for
    /// performance when modifying large composite values like functions.
    ///
    /// Each value type follows TLC's fingerprinting pattern:
    /// 1. Extend with type tag (from ValueConstants)
    /// 2. Extend with length/size if applicable
    /// 3. Extend with component values recursively
    ///
    /// # Arguments
    /// * `fp` - The current fingerprint to extend
    ///
    /// # Returns
    /// The extended fingerprint including this value, or a `FingerprintError`
    /// if a value exceeds TLC-compatible limits.
    pub fn fingerprint_extend(&self, fp: u64) -> FingerprintResult<u64> {
        match self {
            // Concrete value types — scalar, collection, and structure families
            Value::Bool(_)
            | Value::SmallInt(_)
            | Value::Int(_)
            | Value::String(_)
            | Value::Set(_)
            | Value::Interval(_)
            | Value::Func(_)
            | Value::IntFunc(_)
            | Value::Tuple(_)
            | Value::Seq(_)
            | Value::Record(_)
            | Value::ModelValue(_) => concrete::fingerprint_extend_concrete(self, fp),
            // Lazy/derived set types, lazy functions, and closures
            _ => lazy::fingerprint_extend_lazy(self, fp),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::error::FingerprintError;
    use super::helpers::{fp_bigint_len_to_i32, fp_usize_to_i32};

    #[test]
    fn fp_usize_to_i32_accepts_i32_max() {
        assert_eq!(
            fp_usize_to_i32(i32::MAX as usize, "test length").unwrap(),
            i32::MAX,
        );
    }

    #[test]
    fn fp_usize_to_i32_returns_error_above_i32_max() {
        let result = fp_usize_to_i32(i32::MAX as usize + 1, "test length");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, FingerprintError::I32Overflow { .. }));
        assert!(
            err.to_string().contains("test length"),
            "error should contain context: {}",
            err,
        );
    }

    #[test]
    fn fp_bigint_len_to_i32_accepts_i32_max() {
        let value = num_bigint::BigInt::from(i32::MAX);
        assert_eq!(
            fp_bigint_len_to_i32(&value, "test bigint length").unwrap(),
            i32::MAX,
        );
    }

    #[test]
    fn fp_bigint_len_to_i32_returns_error_above_i32_max() {
        let value = num_bigint::BigInt::from(i32::MAX) + 1;
        let result = fp_bigint_len_to_i32(&value, "test bigint length");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, FingerprintError::I32Overflow { .. }));
        assert!(
            err.to_string().contains("test bigint length"),
            "error should contain context: {}",
            err,
        );
    }
}
