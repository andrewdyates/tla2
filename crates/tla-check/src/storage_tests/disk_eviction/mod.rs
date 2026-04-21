// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Disk eviction tests — split from monolithic disk_eviction.rs (594 lines, 12 tests)
//!
//! Split into 3 themed files — Part of #3520

use super::fp;
use super::*;

mod barrier;
mod insert;
mod rollback;
