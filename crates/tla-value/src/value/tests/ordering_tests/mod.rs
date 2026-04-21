// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Targeted unit tests for Value ordering semantics (ordering.rs).
//! Covers cross-type comparison, partial-order edge cases, and Ord/Eq consistency.
//!
//! Part of #1649: zero-test modules need direct coverage.

mod intfunc_cases;
mod invariants;
mod primitives_and_sets;
mod tuple_seq_func;
