// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set operations harnesses: union, intersection, difference, subset,
//! membership, cardinality, quantifiers, CHOOSE
//! (P9, P41, P45-P48, P51, P56-set, P57-set, P-BoolOnly-set).

#[cfg(kani)]
#[allow(clippy::mutable_key_type)]
// Value uses OnceLock for sort caching; interior mutability does not affect Ord/Eq
mod kani_proofs;

#[cfg(test)]
#[allow(clippy::mutable_key_type)]
// Value uses OnceLock for sort caching; interior mutability does not affect Ord/Eq
mod tests;
