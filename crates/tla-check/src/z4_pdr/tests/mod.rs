// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4 PDR tests — split from monolithic tests.rs (1095 lines)
//!
//! Split into 4 themed files — Part of #3692

use super::*;

mod helpers;

mod chc_translation;
mod end_to_end;
mod end_to_end_domain;
mod generalization;
mod sort_inference;
