// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `impl Value` constructors, type predicates, and extractors.
//!
//! Extracted from `value/mod.rs` as part of #1398 decomposition.
//! Split into focused sub-modules as part of #3341.

mod constructors;
mod function_like;
mod scalars;
mod set_like;
