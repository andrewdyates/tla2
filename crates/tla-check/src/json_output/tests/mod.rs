// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for JSON output format: serialization, error codes, diagnostics,
//! DOT graph output, and liveness error handling.

mod actions;
mod diagnostics;
mod dot_output;
mod error_code_mapping;
mod liveness_errors;
mod serialization;

use super::*;
use crate::Value;
use std::path::Path;
use std::time::Duration;
