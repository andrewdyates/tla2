// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Targeted unit tests for the TLC-compatible comparison module (`tlc_cmp/`).
//! Tests iter_set_tlc_normalized which uses TLC's ordering for bounded CHOOSE.
//!
//! Part of #1649: zero-test modules need direct coverage.

use super::super::*;

mod errors;
mod functions;
mod model_values;
mod scalars_and_iteration;
mod set_fast_path;
mod structured_values;

/// Collect iter_set_tlc_normalized into a Vec for easy comparison.
fn tlc_normalized(v: &Value) -> Vec<Value> {
    v.iter_set_tlc_normalized()
        .expect("iter_set_tlc_normalized failed")
        .collect()
}
