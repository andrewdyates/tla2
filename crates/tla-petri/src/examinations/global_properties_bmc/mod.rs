// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BMC and k-induction for GlobalProperties examinations via z4.
//!
//! Extends the existing SMT-based reachability infrastructure to the five
//! GlobalProperty examinations: Deadlock, OneSafe, QuasiLiveness,
//! StableMarking, and Liveness. Each examination gets a direct SMT-LIB
//! encoding (not via `PropertyTracker`) because these properties have
//! specialized structure that doesn't map cleanly to `ResolvedPredicate`.

use std::path::Path;
use std::time::Instant;

use crate::petri_net::PetriNet;

use super::bmc_runner::{run_depth_ladder, DepthAction, DepthQuery};
use super::smt_encoding::{SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT};

mod deadlock;
mod liveness;
mod one_safe;
mod quasi_liveness;
mod stable_marking;

pub(crate) use deadlock::run_deadlock_bmc;
pub(crate) use liveness::run_liveness_bmc;
pub(crate) use one_safe::run_one_safe_bmc;
pub(crate) use quasi_liveness::run_quasi_liveness_bmc;
pub(crate) use stable_marking::run_stable_marking_bmc;

/// Configuration for the generic two-phase BMC + k-induction runner.
struct BmcKindConfig {
    /// Examination name for diagnostic output (e.g., "Deadlock", "OneSafe").
    exam_name: &'static str,
    /// What SAT means in the BMC phase (e.g., `true` = deadlock found, `false` = safety violation).
    bmc_sat_value: bool,
    /// What UNSAT means in the k-induction phase (e.g., `false` = deadlock-free, `true` = 1-safe).
    kind_unsat_value: bool,
}

/// Generic two-phase BMC + k-induction runner.
///
/// Phase 1 (BMC): searches for a witness via increasing depths. SAT at any depth
/// yields `Some(config.bmc_sat_value)`.
///
/// Phase 2 (k-induction): attempts an inductive proof, capped at `max_bmc_depth + 1`
/// for soundness. UNSAT at any depth yields `Some(config.kind_unsat_value)`.
fn run_bmc_and_kinduction(
    z4_path: &Path,
    net: &PetriNet,
    deadline: Option<Instant>,
    config: &BmcKindConfig,
    bmc_encoder: impl Fn(&PetriNet, usize) -> String,
    kind_encoder: impl Fn(&PetriNet, usize) -> String,
) -> Option<bool> {
    // Phase 1: BMC
    let mut bmc_verdict = None;
    let max_bmc_depth = run_depth_ladder(
        z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        &mut bmc_verdict,
        |_, depth| Some(DepthQuery::new(bmc_encoder(net, depth), 1)),
        |bmc_verdict, depth, results| match results {
            Some([SolverOutcome::Sat]) => {
                eprintln!(
                    "{} BMC depth {depth}: SAT (witness found)",
                    config.exam_name
                );
                *bmc_verdict = Some(config.bmc_sat_value);
                DepthAction::StopDeepening
            }
            Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
            Some([SolverOutcome::Unsat]) => DepthAction::Explored,
            other => {
                eprintln!("{} BMC unexpected result: {other:?}", config.exam_name);
                DepthAction::StopDeepening
            }
        },
    );
    if bmc_verdict.is_some() {
        return bmc_verdict;
    }

    // Phase 2: k-induction (soundness gate: depth <= max_bmc_depth + 1)
    let max_kind_depth = match max_bmc_depth {
        Some(d) => d + 1,
        None => return None,
    };
    let mut kind_verdict = None;
    let _ = run_depth_ladder(
        z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        &mut kind_verdict,
        |_, depth| {
            if depth > max_kind_depth {
                None
            } else {
                Some(DepthQuery::new(kind_encoder(net, depth), 1))
            }
        },
        |kind_verdict, depth, results| match results {
            Some([SolverOutcome::Unsat]) => {
                eprintln!("{} k-ind depth {depth}: UNSAT (proved)", config.exam_name);
                *kind_verdict = Some(config.kind_unsat_value);
                DepthAction::StopDeepening
            }
            Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
            Some([SolverOutcome::Sat]) => DepthAction::Explored,
            other => {
                eprintln!("{} k-ind unexpected result: {other:?}", config.exam_name);
                DepthAction::StopDeepening
            }
        },
    );
    kind_verdict
}

#[cfg(test)]
use deadlock::{
    encode_dead_predicate, encode_deadlock_bmc_script, encode_deadlock_kinduction_script,
    encode_not_dead_predicate,
};
#[cfg(test)]
use liveness::{encode_transition_disabled_bmc, encode_transition_disabled_kinduction};
#[cfg(test)]
use one_safe::{encode_one_safe_bmc_script, encode_one_safe_kinduction_script};
#[cfg(test)]
use quasi_liveness::encode_quasi_liveness_bmc_script;
#[cfg(test)]
use stable_marking::{encode_stable_marking_bmc_script, encode_stable_marking_kinduction_script};

#[cfg(test)]
#[path = "../global_properties_bmc_tests.rs"]
mod tests;
