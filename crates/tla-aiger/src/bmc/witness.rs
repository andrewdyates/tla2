// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Witness extraction and convenience API for BMC/k-induction results.
//!
//! Provides `BmcResult` (the public result type) and convenience wrappers
//! (`check_bmc`, `check_bmc_dynamic`, `check_kind`, `check_kind_simple_path`)
//! that apply COI reduction and return results with raw literal witness traces.

use crate::check_result::CheckResult;
use crate::sat_types::Lit;
use crate::transys::Transys;

use super::engine::BmcEngine;

/// Result of a BMC or k-induction model checking run.
///
/// This is a lightweight result type suitable for the public API. It carries
/// the verdict, the maximum depth explored, and an optional witness trace
/// as raw SAT literals (one `Vec<Lit>` per time step).
#[derive(Debug, Clone)]
pub struct BmcResult {
    /// `Some(true)` = SAFE, `Some(false)` = UNSAFE, `None` = unknown/bounded.
    pub verdict: Option<bool>,
    /// Maximum depth checked (or depth of counterexample for UNSAFE).
    pub depth: usize,
    /// Counterexample trace for UNSAFE verdicts. Each entry is one time step,
    /// represented as a vector of literals over latch and input variables.
    /// Positive literal = variable is true; negative = variable is false.
    pub witness: Option<Vec<Vec<Lit>>>,
}

/// Run BMC up to `max_depth` steps.
///
/// Convenience wrapper around `BmcEngine` that applies COI reduction,
/// variable compaction, and returns a `BmcResult` with raw literal witness
/// traces.
///
/// ## Preprocessing (#4073)
///
/// Uses COI reduction + variable compaction (not the full `preprocess()`
/// pipeline which includes SCORR/FRTS) to keep startup fast while still
/// reducing the per-step clause count. Compaction renumbers variables to a
/// dense range, improving z4-sat cache locality and reducing memory.
///
/// BMC can only prove UNSAFE (by finding a counterexample). If it reaches
/// `max_depth` without finding one, it returns `verdict = None`.
pub fn check_bmc(ts: &Transys, max_depth: usize) -> BmcResult {
    let reduced = ts.coi_reduce().compact_vars();
    let mut engine = BmcEngine::new(reduced, 1);
    let result = engine.check(max_depth);
    bmc_result_from_engine(&engine, result, max_depth)
}

/// Run BMC with dynamic step size (rIC3's `--dyn-step`).
///
/// Automatically adjusts step size based on circuit complexity:
/// small circuits get large steps (fast deep exploration), large circuits
/// get step=1 (thorough per-depth checking).
///
/// Uses COI reduction + variable compaction for improved per-step efficiency.
pub fn check_bmc_dynamic(ts: &Transys, max_depth: usize) -> BmcResult {
    let reduced = ts.coi_reduce().compact_vars();
    let mut engine = BmcEngine::new_dynamic(reduced);
    let result = engine.check(max_depth);
    bmc_result_from_engine(&engine, result, max_depth)
}

/// Convert a BmcEngine check result into a BmcResult.
fn bmc_result_from_engine(engine: &BmcEngine, result: CheckResult, max_depth: usize) -> BmcResult {
    match result {
        CheckResult::Unsafe { depth, .. } => {
            let witness = engine.extract_lit_trace(depth);
            BmcResult {
                verdict: Some(false),
                depth,
                witness: Some(witness),
            }
        }
        CheckResult::Safe => BmcResult {
            verdict: Some(true),
            depth: max_depth,
            witness: None,
        },
        CheckResult::Unknown { .. } => BmcResult {
            verdict: None,
            depth: max_depth,
            witness: None,
        },
    }
}

/// Run k-induction up to `max_depth` steps.
///
/// Convenience wrapper around `KindEngine` that applies COI reduction and
/// returns a `BmcResult`. k-induction can prove both SAFE (if the inductive
/// step succeeds) and UNSAFE (if the base case finds a counterexample).
pub fn check_kind(ts: &Transys, max_depth: usize) -> BmcResult {
    use crate::kind::KindEngine;

    let reduced = ts.coi_reduce();
    let mut engine = KindEngine::new(reduced);
    let result = engine.check(max_depth);
    kind_result_from_engine(&engine, result, max_depth)
}

/// Run k-induction with the simple-path constraint (rIC3's default mode).
///
/// The simple-path constraint asserts that all states in the induction trace
/// are pairwise distinct. This strengthens the induction hypothesis, helping
/// prove properties that are not directly k-inductive. This is rIC3's default
/// k-induction mode (`kind --step 1 --simple-path`).
pub fn check_kind_simple_path(ts: &Transys, max_depth: usize) -> BmcResult {
    use crate::kind::KindEngine;

    let reduced = ts.coi_reduce();
    let mut engine = KindEngine::new_simple_path(reduced);
    let result = engine.check(max_depth);
    kind_result_from_engine(&engine, result, max_depth)
}

/// Convert a KindEngine check result into a BmcResult.
fn kind_result_from_engine(
    engine: &crate::kind::KindEngine,
    result: CheckResult,
    max_depth: usize,
) -> BmcResult {
    match result {
        CheckResult::Unsafe { depth, .. } => {
            let witness = engine.extract_lit_trace(depth);
            BmcResult {
                verdict: Some(false),
                depth,
                witness: Some(witness),
            }
        }
        CheckResult::Safe => BmcResult {
            verdict: Some(true),
            depth: max_depth,
            witness: None,
        },
        CheckResult::Unknown { .. } => BmcResult {
            verdict: None,
            depth: max_depth,
            witness: None,
        },
    }
}
