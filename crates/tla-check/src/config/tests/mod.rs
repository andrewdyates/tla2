// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Config tests — split from monolithic tests.rs (1,112 lines)
//!
//! Split into 6 themed files — Part of #2779

use super::types::ConfigValidationIssue;
use super::*;

mod basics;
mod init_mode;
mod validation;
mod view_terminal;
