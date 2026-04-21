// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Re-exports from tla-jit-runtime. See `tla_jit_runtime::compound_layout` for docs.
//!
//! Part of #4199: thin re-export wrapper so all `crate::compound_layout::*` references
//! within tla-jit continue to resolve without changes.

pub use tla_jit_runtime::compound_layout::*;
