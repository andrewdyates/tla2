// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Targeted unit tests for lazy set operations (set_ops.rs).
//! Part of #1649: zero-test modules need direct coverage.

use super::super::*;
use std::sync::Arc;

mod big_union;
mod lazy_binary_ops;
mod seqset;
