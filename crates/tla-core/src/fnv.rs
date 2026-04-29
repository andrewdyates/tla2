// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FNV-1a hash constants shared across the TLA2 crate stack.
//!
//! These constants are used by:
//! - `tla-core::var_index` — variable registry salt computation
//! - `tla-check::state::value_hash` — FNV-1a value fingerprinting
//! - `tla-check::state::array_state` — state fingerprint finalization
//! - `tla-check::state::diff_successor` — diff-based fingerprint finalization
//! - `tla-check::intern` — interning hash computation
//! - `tla-value::value::lazy_func` — lazy function identity hashing
//!
//! Consolidated from 8+ scattered definitions per #2037.

/// FNV-1a 64-bit offset basis.
pub const FNV_OFFSET: u64 = 0xcbf29ce484222325;

/// FNV-1a 64-bit prime multiplier.
pub const FNV_PRIME: u64 = 0x100000001b3;
