// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for finalize_check result precedence (#1850).

use super::*;
use crate::check::{CheckError, CheckResult};
use crate::eval::EvalCtx;
use crate::test_support::parse_module;
use crate::EvalCheckError;
use crossbeam_channel::bounded;
use std::sync::atomic::Ordering;

mod collision_stats;
mod interner_cleanup;
mod merge_outcome;
mod oncelock_snapshot;
mod periodic_maintenance;
mod postcondition_and_guards;
mod result_precedence;
