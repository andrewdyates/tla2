// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dual simplex algorithm, pivoting, and conflict generation.

use std::sync::OnceLock;

use num_rational::BigRational;
use num_traits::{One, Zero};
use tracing::{debug, info, trace};
use z4_core::{FarkasAnnotation, TheoryConflict, TheoryLit, TheoryResult};

use crate::rational::Rational;
use crate::types::{ErrorKey, InfRational};
use crate::{BoundType, LraSolver, TableauRow, VarInfo, VarStatus};

/// After this many consecutive iterations with the same basis hash,
/// switch to Bland's rule for anti-cycling. Reference: Z3 uses 1000
/// (lp_primal_core_solver.h:380-381 `m_bland_mode_threshold`).
const BLAND_THRESHOLD: u32 = 1000;

/// Cached `Z4_DEBUG_LRA` env var (checked once per process).
fn debug_lra() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_LRA").is_ok())
}

mod debug;
mod feasibility;
mod pivot;
mod solve;
#[cfg(test)]
mod tests;
mod updates;
