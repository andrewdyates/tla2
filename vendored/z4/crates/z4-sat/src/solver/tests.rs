// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) use super::*;
pub(super) use crate::solver::preprocess::ModelViolation;

mod benchmarks;
mod congruence;
mod decompose_lrat;
mod decompose_rewrite;
mod deduplicate_proof;
mod diagnostic_trace;
mod incremental;
mod instantiate;
mod inprocessing;
mod inprocessing_large_formula_gate;
mod kitten;
mod lifecycle;
mod lookahead;
mod minimize;
mod original_clause_ledger;
mod preprocessing_bve;
mod proof_checking;
mod proof_lrat;
mod propagation;
#[cfg(feature = "unsafe-bcp")]
mod propagation_bcp_unsafe;
mod reason_marks;
mod reconstruction;
mod reduction;
mod restart;
mod search;
mod soundness;
mod statistics;
mod subsumption;
mod support;
mod symmetry;
mod theory;
mod vivification;

use support::*;
