// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for symmetry permutation, cross-type hash/equality equivalence,
//! FuncSet iterator semantics, and regression suites for Bug #179 and Bug #1713.
//!
//! Split from monolithic equivalence.rs per #3343.

mod bug_1713;
mod bug_179;
mod cmp_consistency;
mod funcset;
mod hash_eq;
mod permute;
