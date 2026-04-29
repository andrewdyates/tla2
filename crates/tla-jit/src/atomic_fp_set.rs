// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Re-exports from tla-jit-runtime. See `tla_jit_runtime::atomic_fp_set` for docs.
//!
//! Part of #4199: thin re-export wrapper so all `crate::atomic_fp_set::*` references
//! within tla-jit continue to resolve without changes.

pub use tla_jit_runtime::atomic_fp_set::*;
