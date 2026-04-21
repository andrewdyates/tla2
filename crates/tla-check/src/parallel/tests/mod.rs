// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checker tests — split from monolithic tests.rs (2,616 lines, 50 tests)
//!
//! Split into 9 themed files — Part of #2779

use super::*;
use crate::check::CheckResult;
use crate::test_support::parse_module;
use crate::{ConfigCheckError, LivenessCheckError};

/// Re-export from crate-level test_utils for convenience. Part of #3300.
pub(super) fn acquire_interner_lock() -> std::sync::MutexGuard<'static, ()> {
    crate::test_utils::acquire_interner_lock()
}

mod basic;
mod config_and_checkpoint;
mod consistency;
mod fairness;
mod limits;
mod liveness;
mod parity;
mod readonly_value_cache_cleanup_tests;
mod storage_capacity;
mod stress;
