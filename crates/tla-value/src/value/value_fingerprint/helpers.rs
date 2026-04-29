// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared numeric-conversion helpers for fingerprinting.

use super::error::{FingerprintError, FingerprintResult};
use num_traits::ToPrimitive;

#[inline]
pub(crate) fn fp_usize_to_i32(value: usize, context: &'static str) -> FingerprintResult<i32> {
    i32::try_from(value).map_err(|_| FingerprintError::I32Overflow {
        value: value.to_string(),
        context,
    })
}

#[inline]
pub(super) fn fp_bigint_len_to_i32(
    value: &num_bigint::BigInt,
    context: &'static str,
) -> FingerprintResult<i32> {
    value.to_i32().ok_or_else(|| FingerprintError::I32Overflow {
        value: value.to_string(),
        context,
    })
}
