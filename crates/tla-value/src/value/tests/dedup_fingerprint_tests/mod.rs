// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for state-dedup fingerprint cache preservation across EXCEPT updates.
//!
//! Part of #3168: the model checker's hot EXCEPT paths should update cached
//! additive fingerprints incrementally instead of invalidating them.

use crate::dedup_fingerprint::state_value_fingerprint;
use crate::Value;

mod func_cache;
mod readonly_cache;
mod record_cache;
mod tuple_seq_equivalence;

/// Test helper: unwrap the FingerprintResult for test assertions.
fn state_value_fingerprint_unwrap(value: &Value) -> u64 {
    state_value_fingerprint(value).unwrap()
}
