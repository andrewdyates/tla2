// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible FP64 polynomial rolling hash — re-exported from tla-value.
//!
//! The fingerprint algorithm and value type tags have moved to `tla_value::fingerprint`
//! so that downstream crates (tla-value, tla-eval) can use them without depending
//! on tla-check.
//!
//! Part of #1269 Phase 3: relocate fingerprint primitives.

pub use tla_value::fingerprint::*;
