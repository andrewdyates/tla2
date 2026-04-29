// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level integration tests for the JIT compilation pipeline.
//!
//! These tests exercise the full path from TIR -> bytecode -> native code
//! -> execution, verifying end-to-end correctness of the JIT compiler.

mod integration;
mod type_specialization;
