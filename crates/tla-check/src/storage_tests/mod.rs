// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Storage tests — split from monolithic storage_tests.rs (3,044 lines, 95 tests)
//!
//! Split into 10 themed files — Part of #2779

use super::*;

fn fp(v: u64) -> Fingerprint {
    Fingerprint(v)
}

mod checkpoint;
mod collect_fingerprints;
mod disk_eviction;
mod disk_fpset;
mod disk_streaming;
mod error_capacity;
mod inmemory_progressive_warning;
mod mmap_alignment;
mod mmap_basic;
mod mmap_collect_flushed;
mod sharded;
mod trace_locations;
