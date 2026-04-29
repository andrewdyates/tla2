// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backend-agnostic JIT runtime errors.
//!
//! The canonical `JitRuntimeError` definition now lives in `tla-jit-abi`
//! (Part of #4265, Stage 2b of epic #4251). This module re-exports it so
//! existing `tla_jit_runtime::error::JitRuntimeError` call sites keep working.

pub use tla_jit_abi::JitRuntimeError;
