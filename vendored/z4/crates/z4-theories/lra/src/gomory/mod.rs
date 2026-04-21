// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gomory cutting plane methods for LRA.
//!
//! Generates and adds Gomory cuts from the simplex tableau for
//! mixed-integer linear programming.

use std::cmp::Ordering;
use std::sync::OnceLock;

#[cfg(not(kani))]
use hashbrown::HashSet;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::TermId;

use crate::rational::Rational;
use crate::{BoundType, GomoryCut, LinearExpr, LraSolver, TableauRow, VarInfo, VarStatus};

/// Cached `Z4_DEBUG_GOMORY` env var (checked once per process).
fn debug_gomory() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_GOMORY").is_ok())
}

const MAX_GOMORY_CUTS_PER_CHECK: usize = 2;

#[derive(Clone)]
struct GomoryCandidate {
    row_idx: usize,
    basic_var: u32,
    score: BigRational,
    /// Number of rows referencing this basic variable (Z3 `usage_in_terms`).
    usage: usize,
}

mod generation;
mod support;
#[cfg(test)]
mod tests;
