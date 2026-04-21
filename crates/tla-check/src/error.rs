// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluation errors — re-exported from tla-value.
//!
//! The `EvalError` enum and `EvalResult` type alias have moved to `tla_value::error`
//! so that downstream crates can use them without depending on tla-check.
//!
//! Part of #1269 Phase 4: value extraction to tla-value.

pub use tla_value::error::*;
