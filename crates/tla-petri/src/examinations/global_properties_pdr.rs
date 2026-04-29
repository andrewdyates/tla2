// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PDR/IC3 verification for global property examinations.
//!
//! Provides PDR-based safety checking for OneSafe, ReachabilityDeadlock,
//! and StableMarking examinations. Each examination is encoded as a safety
//! property over the Petri net's marking variables and solved via the
//! CHC-based PDR solver in [`super::pdr_encoding`].

use std::time::{Duration, Instant};

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::pdr_encoding::{solve_petri_net_pdr, PdrCheckResult, PdrConfig};

const PDR_GLOBAL_TIMEOUT: Duration = Duration::from_secs(10);

/// Run PDR for the OneSafe examination.
///
/// Encodes the safety property: `AG(forall p: m_p <= 1)`.
/// The bad state is any marking where some place exceeds 1 token.
///
/// Returns `Some(true)` if 1-safety is proved, `Some(false)` if a violation
/// exists, `None` if inconclusive.
pub(crate) fn run_one_safe_pdr(net: &PetriNet, deadline: Option<Instant>) -> Option<bool> {
    let np = net.num_places();
    if np == 0 {
        return Some(true); // vacuously 1-safe
    }

    let timeout = deadline
        .map(|limit| PDR_GLOBAL_TIMEOUT.min(limit.saturating_duration_since(Instant::now())))
        .unwrap_or(PDR_GLOBAL_TIMEOUT);
    if timeout.is_zero() {
        return None;
    }

    // Safety property: AND(m_p <= 1) for all places p.
    // Equivalently: IntLe(TokensCount([p]), Constant(1)) for each place.
    let conjuncts: Vec<ResolvedPredicate> = (0..np)
        .map(|p| {
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(p as u32)]),
                ResolvedIntExpr::Constant(1),
            )
        })
        .collect();
    let safety_property = ResolvedPredicate::And(conjuncts);

    let config = PdrConfig {
        time_budget: timeout,
        ..PdrConfig::default()
    };
    let result = solve_petri_net_pdr(net, &safety_property, &config);

    match result {
        PdrCheckResult::Safe => {
            eprintln!("OneSafe: PDR proved 1-safety");
            Some(true)
        }
        PdrCheckResult::Unsafe => {
            eprintln!("OneSafe: PDR found violation (some place > 1)");
            Some(false)
        }
        PdrCheckResult::Unknown => None,
    }
}

/// Run PDR for the ReachabilityDeadlock examination.
///
/// Encodes the safety property: `AG(exists t: enabled(t))` —
/// "in every reachable state, at least one transition is fireable."
/// The bad state is a deadlock (no transition enabled).
///
/// Returns `Some(true)` if a deadlock is found (property violated),
/// `Some(false)` if deadlock-freedom is proved, `None` if inconclusive.
pub(crate) fn run_deadlock_pdr(net: &PetriNet, deadline: Option<Instant>) -> Option<bool> {
    let nt = net.num_transitions();
    if nt == 0 {
        // No transitions: initial state is always a deadlock.
        return Some(true);
    }

    // A net with a source transition (no inputs) is never deadlocked.
    if net.transitions.iter().any(|t| t.inputs.is_empty()) {
        return Some(false);
    }

    let timeout = deadline
        .map(|limit| PDR_GLOBAL_TIMEOUT.min(limit.saturating_duration_since(Instant::now())))
        .unwrap_or(PDR_GLOBAL_TIMEOUT);
    if timeout.is_zero() {
        return None;
    }

    // Safety property: "some transition is fireable" =
    // IsFireable([all transitions]).
    let all_transitions: Vec<TransitionIdx> = (0..nt).map(|t| TransitionIdx(t as u32)).collect();
    let safety_property = ResolvedPredicate::IsFireable(all_transitions);

    let config = PdrConfig {
        time_budget: timeout,
        ..PdrConfig::default()
    };
    let result = solve_petri_net_pdr(net, &safety_property, &config);

    match result {
        PdrCheckResult::Safe => {
            eprintln!("ReachabilityDeadlock: PDR proved deadlock-free");
            Some(false)
        }
        PdrCheckResult::Unsafe => {
            eprintln!("ReachabilityDeadlock: PDR found deadlock");
            Some(true)
        }
        PdrCheckResult::Unknown => None,
    }
}

/// Result of PDR-based StableMarking analysis.
pub(crate) struct StableMarkingPdrResult {
    /// Definitive verdict if PDR resolved the examination.
    pub verdict: Option<bool>,
    /// Per-place instability: `true` = PDR found a counterexample for that place.
    pub unstable: Vec<bool>,
}

/// Run PDR for the StableMarking examination.
///
/// Encodes each candidate place as a separate safety property:
/// `AG(m_p = init_p)`. If PDR proves any place stable, the verdict is TRUE.
/// If PDR disproves all places (finds counterexamples), the verdict is FALSE.
///
/// Returns `None` if z4 CHC is unavailable or all queries are inconclusive.
pub(crate) fn run_stable_marking_pdr(
    net: &PetriNet,
    deadline: Option<Instant>,
) -> Option<StableMarkingPdrResult> {
    let np = net.num_places();
    if np == 0 {
        return None;
    }

    let mut unstable = vec![false; np];

    // Time budget per place: divide evenly but cap at PDR_GLOBAL_TIMEOUT.
    let total_budget = deadline
        .map(|limit| PDR_GLOBAL_TIMEOUT.min(limit.saturating_duration_since(Instant::now())))
        .unwrap_or(PDR_GLOBAL_TIMEOUT);
    if total_budget.is_zero() {
        return None;
    }
    let per_place_budget = Duration::from_millis(
        (total_budget.as_millis() as u64)
            .saturating_div(np as u64)
            .max(100),
    );

    for p in 0..np {
        if let Some(limit) = deadline {
            if Instant::now() >= limit {
                break;
            }
        }

        let timeout = deadline
            .map(|limit| per_place_budget.min(limit.saturating_duration_since(Instant::now())))
            .unwrap_or(per_place_budget);
        if timeout.is_zero() {
            break;
        }

        // Safety property for place p: m_p = init_p, encoded as
        // AND(m_p <= init_p, init_p <= m_p).
        let init_val = net.initial_marking[p];
        let safety_property = ResolvedPredicate::And(vec![
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(p as u32)]),
                ResolvedIntExpr::Constant(init_val),
            ),
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(init_val),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(p as u32)]),
            ),
        ]);

        let config = PdrConfig {
            time_budget: timeout,
            ..PdrConfig::default()
        };
        let result = solve_petri_net_pdr(net, &safety_property, &config);

        match result {
            PdrCheckResult::Safe => {
                eprintln!("StableMarking: PDR proved place {p} stable (marking = {init_val})");
                // Early exit: at least one stable place => verdict TRUE
                return Some(StableMarkingPdrResult {
                    verdict: Some(true),
                    unstable,
                });
            }
            PdrCheckResult::Unsafe => {
                unstable[p] = true;
            }
            PdrCheckResult::Unknown => {}
        }
    }

    // If all places are proven unstable, verdict is FALSE.
    if unstable.iter().all(|&u| u) {
        return Some(StableMarkingPdrResult {
            verdict: Some(false),
            unstable,
        });
    }

    // Partial result: some places unstable via PDR, rest unknown.
    if unstable.iter().any(|&u| u) {
        Some(StableMarkingPdrResult {
            verdict: None,
            unstable,
        })
    } else {
        None
    }
}

#[cfg(test)]
#[path = "global_properties_pdr_tests.rs"]
mod tests;
