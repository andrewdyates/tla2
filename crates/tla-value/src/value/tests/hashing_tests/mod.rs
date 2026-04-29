// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Targeted unit tests for Value hashing semantics (hashing.rs).
//! Verifies hash stability for equal values and the Hash/Eq contract.
//!
//! Part of #1649: zero-test modules need direct coverage.

use super::super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub(super) fn hash_value(v: &Value) -> u64 {
    let mut hasher = DefaultHasher::new();
    v.hash(&mut hasher);
    hasher.finish()
}

mod contract;
mod lazy_sets;
mod numeric_edges;
mod stability;
