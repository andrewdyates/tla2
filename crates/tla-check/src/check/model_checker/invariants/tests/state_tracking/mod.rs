// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for state tracking: counts, mark-seen, trace degradation, bulk solve.

use super::*;

mod bookkeeping;
mod bulk_init;
mod streaming_scan;
mod tir_eval;
