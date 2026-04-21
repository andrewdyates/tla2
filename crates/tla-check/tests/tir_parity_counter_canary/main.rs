// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR parity and eval canary tests for the model checker.
//!
//! Split from a single 1013-line file into submodules (Part of #3482).

#[path = "../common/mod.rs"]
mod common;

mod specs;

mod counter;
mod defaults;
mod diehard;
mod liveness;
