// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode VM invariant evaluation tests.
//!
//! Extracted from `invariants/eval.rs` as part of #3603 to consolidate tests
//! in the existing `invariants/tests/` directory.
//! Split into child modules as part of #3647.

use super::*;
use crate::config::Config;
use crate::test_support::parse_module;
use crate::State;
use crate::Value;
use tla_core::ast::Unit;

mod basics;
mod fallbacks;
mod integration;
