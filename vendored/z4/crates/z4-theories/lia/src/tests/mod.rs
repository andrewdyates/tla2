// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the LIA (Linear Integer Arithmetic) solver.

use super::*;
use z4_core::assert_conflict_soundness;
use z4_core::term::{TermId, TermStore};

mod core_solver;
mod modular;
mod rational;
mod verification;
