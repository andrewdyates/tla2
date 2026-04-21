// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Config validation parity tests (#2675) and checkpoint save/load/resume (#2749)

use super::parse_module;
use super::*;
use std::time::Duration;

mod config_setup;
mod property_trace;
mod resume_roundtrip;
