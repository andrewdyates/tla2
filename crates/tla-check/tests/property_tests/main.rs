// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Property-based tests for TLA+ evaluator
//!
//! These tests verify algebraic laws and semantic properties using proptest.
//! They ensure correctness of the evaluator across randomized inputs.
//!
//! Split from monolithic property_tests.rs (4,483 lines) per #1371 design.

mod helpers;

mod arithmetic;
mod bags;
mod boolean;
mod fingerprint;
mod finite_sets_ext;
mod functions;
mod intervals;
mod json;
mod quantifiers;
mod randomization;
mod reals;
mod sequences;
mod sequences_ext;
mod sets;
mod strings;
mod tlc;
mod tlc_ext;
mod transitive_closure;
