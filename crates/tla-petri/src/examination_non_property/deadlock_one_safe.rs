// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::super::super::examination_plan::ExecutionPlan;
use super::common::{checkpoint_cannot_compute, reduction_cannot_compute};
use crate::examinations::deadlock::{DeadlockObserver, PortfolioDeadlockObserver};
use crate::examinations::global_properties_bmc;
use crate::examinations::global_properties_pdr;
use crate::examinations::one_safe::{one_safe_por_config, OneSafeObserver};
use crate::explorer::{explore_observer, ExplorationConfig};
use crate::output::Verdict;
use crate::petri_net::PetriNet;
use crate::portfolio::SharedVerdict;
use crate::reduction::reduce_iterative_structural_one_safe;
use crate::stubborn::PorStrategy;

/// Compute BFS worker count for the portfolio, if applicable.
///
/// Returns `None` when `workers == 1` (stay sequential — the public
/// `ExplorationConfig::workers()` contract says 1 = sequential).
/// Returns `Some(bfs_workers)` when `workers >= 2`, reserving 1 for BMC.
fn deadlock_portfolio_bfs_workers(total_workers: usize) -> Option<usize> {
    (total_workers >= 2).then_some(total_workers.saturating_sub(1))
}

pub(crate) fn deadlock_verdict(net: &PetriNet, config: &ExplorationConfig) -> Verdict {
    // --- Phase 0: cheap structural pre-checks (sequential, <1s) ---
    if let Some(true) = crate::structural::structural_deadlock_free(net) {
        eprintln!("ReachabilityDeadlock: structurally deadlock-free (siphon/trap)");
        return Verdict::False;
    }

    // LP state equation: proves deadlock-freedom on ALL net types by checking
    // if some transition is always enabled in the LP relaxation.
    if let Some(true) = crate::structural::lp_deadlock_free(net) {
        eprintln!("ReachabilityDeadlock: LP-proved deadlock-free (always-enabled transition)");
        return Verdict::False;
    }

    // --- Phase 0b: PDR/IC3 (symbolic, no state space) ---
    match global_properties_pdr::run_deadlock_pdr(net, config.deadline()) {
        Some(true) => return Verdict::True,
        Some(false) => return Verdict::False,
        None => {}
    }

    // --- Phase 1: expensive verification ---
    if config.checkpoint().is_some() {
        return deadlock_sequential(net, &config.clone().with_workers(1));
    }

    // Portfolio (BMC vs BFS in parallel) when workers >= 2;
    // sequential fallback when workers == 1 to honour the public API contract.
    match deadlock_portfolio_bfs_workers(config.workers()) {
        Some(bfs_workers) => deadlock_portfolio(net, config, bfs_workers),
        None => deadlock_sequential(net, config),
    }
}

/// Sequential deadlock verification: BMC then BFS. Used when workers == 1.
fn deadlock_sequential(net: &PetriNet, config: &ExplorationConfig) -> Verdict {
    match global_properties_bmc::run_deadlock_bmc(net, config.deadline()) {
        Some(true) => return Verdict::True,
        Some(false) => return Verdict::False,
        None => {}
    }

    let plan = ExecutionPlan::observer(PorStrategy::DeadlockPreserving);
    let mut observer = DeadlockObserver::new();
    let result = match plan.run_checkpointable_observer(net, config, &mut observer) {
        Ok(result) => result,
        Err(error) => return checkpoint_cannot_compute("ReachabilityDeadlock", &error),
    };

    if observer.found_deadlock() {
        Verdict::True
    } else if result.completed {
        Verdict::False
    } else {
        Verdict::CannotCompute
    }
}

/// Portfolio deadlock verification: race BMC vs BFS. Used when workers >= 2.
fn deadlock_portfolio(net: &PetriNet, config: &ExplorationConfig, bfs_workers: usize) -> Verdict {
    let shared = Arc::new(SharedVerdict::new());
    let bfs_config = config.clone().with_workers(bfs_workers);

    std::thread::scope(|s| {
        let shared_bmc = Arc::clone(&shared);
        let bmc_handle = s.spawn(move || {
            if shared_bmc.is_resolved() {
                return;
            }
            match global_properties_bmc::run_deadlock_bmc(net, config.deadline()) {
                Some(true) => {
                    shared_bmc.publish(Verdict::True);
                }
                Some(false) => {
                    shared_bmc.publish(Verdict::False);
                }
                None => {}
            }
        });

        let shared_bfs = Arc::clone(&shared);
        let bfs_handle = s.spawn(move || {
            if shared_bfs.is_resolved() {
                return;
            }
            let plan = ExecutionPlan::observer(PorStrategy::DeadlockPreserving);
            let mut observer = PortfolioDeadlockObserver::new(Arc::clone(&shared_bfs));
            let result = plan.run_observer(net, &bfs_config, &mut observer);

            if shared_bfs.is_resolved() {
                return; // BMC won while we explored
            }
            if observer.found_deadlock() {
                shared_bfs.publish(Verdict::True);
            } else if result.completed {
                shared_bfs.publish(Verdict::False);
            }
        });

        let _ = bmc_handle.join();
        let _ = bfs_handle.join();
    });

    shared.verdict().unwrap_or(Verdict::CannotCompute)
}

/// Colored place groups for OneSafe checking.
///
/// For colored models, MCC defines 1-safe as: no colored place holds more
/// than 1 token total (sum across all color instances). Each group is a set
/// of unfolded PT place indices from the same colored parent. When empty,
/// the standard per-place check is used.
pub(crate) fn one_safe_verdict(
    net: &PetriNet,
    config: &ExplorationConfig,
    colored_groups: &[Vec<usize>],
) -> Verdict {
    // Fast FALSE: initial marking is reachable.
    if !colored_groups.is_empty() {
        // Colored: check group sums in initial marking.
        for group in colored_groups {
            let sum: u64 = group.iter().map(|&p| net.initial_marking[p]).sum();
            if sum > 1 {
                return Verdict::False;
            }
        }
    } else if net.initial_marking.iter().any(|&m| m > 1) {
        return Verdict::False;
    }

    // Structural short-circuit: if P-invariants prove all places <= 1,
    // the net is 1-safe without state space exploration.
    // For colored models, we must check group-level bounds, not individual.
    let invariants = crate::invariant::compute_p_invariants(net);
    if !colored_groups.is_empty() {
        // Check that every colored group is bounded <= 1 by some P-invariant.
        let all_bounded = colored_groups.iter().all(|group| {
            let places: Vec<usize> = group.clone();
            crate::invariant::structural_set_bound(&invariants, &places)
                .is_some_and(|bound| bound <= 1)
        });
        if all_bounded {
            eprintln!(
                "OneSafe: structurally 1-safe (all colored groups bounded ≤ 1 by P-invariants)"
            );
            return Verdict::True;
        }

        // LP fallback for colored groups not bounded by P-invariants.
        let unbounded_groups: Vec<&Vec<usize>> = colored_groups
            .iter()
            .filter(|group| {
                let places: Vec<usize> = (*group).clone();
                !crate::invariant::structural_set_bound(&invariants, &places)
                    .is_some_and(|bound| bound <= 1)
            })
            .collect();
        if !unbounded_groups.is_empty() {
            use crate::lp_state_equation::lp_upper_bound;
            use crate::petri_net::PlaceIdx;
            let all_lp_bounded = unbounded_groups.iter().all(|group| {
                let place_indices: Vec<PlaceIdx> =
                    group.iter().map(|&p| PlaceIdx(p as u32)).collect();
                lp_upper_bound(net, &place_indices).is_some_and(|b| b <= 1)
            });
            if all_lp_bounded {
                eprintln!(
                    "OneSafe: structurally 1-safe (LP bounds ≤ 1 for {} colored groups not covered by P-invariants)",
                    unbounded_groups.len()
                );
                return Verdict::True;
            }
        }
    } else {
        let bounds: Vec<Option<u64>> = (0..net.num_places())
            .map(|p| crate::invariant::structural_place_bound(&invariants, p))
            .collect();
        if !bounds.is_empty() && bounds.iter().all(|b| b.is_some_and(|v| v <= 1)) {
            eprintln!("OneSafe: structurally 1-safe (all places bounded ≤ 1 by P-invariants)");
            return Verdict::True;
        }

        // LP state equation gives tighter bounds than P-invariants alone.
        // For places where P-invariants don't prove bound ≤ 1, try LP.
        let unbounded_places: Vec<usize> = bounds
            .iter()
            .enumerate()
            .filter(|(_, b)| !b.is_some_and(|v| v <= 1))
            .map(|(i, _)| i)
            .collect();
        if !unbounded_places.is_empty() {
            use crate::lp_state_equation::lp_upper_bound;
            use crate::petri_net::PlaceIdx;
            let all_lp_bounded = unbounded_places
                .iter()
                .all(|&p| lp_upper_bound(net, &[PlaceIdx(p as u32)]).is_some_and(|b| b <= 1));
            if all_lp_bounded {
                eprintln!(
                    "OneSafe: structurally 1-safe (LP bounds ≤ 1 for {} places not covered by P-invariants)",
                    unbounded_places.len()
                );
                return Verdict::True;
            }
        }
    }

    // SMT-based BMC + k-induction on the original net before reduction/BFS.
    // Note: BMC checks individual places only; skip for colored models to avoid
    // false TRUE on group-level violations.
    if colored_groups.is_empty() {
        match global_properties_bmc::run_one_safe_bmc(net, config.deadline()) {
            Some(true) => return Verdict::True,
            Some(false) => return Verdict::False,
            None => {}
        }
    }

    // PDR/IC3 for OneSafe (PT nets only, same rationale as BMC above).
    if colored_groups.is_empty() {
        match global_properties_pdr::run_one_safe_pdr(net, config.deadline()) {
            Some(true) => return Verdict::True,
            Some(false) => return Verdict::False,
            None => {}
        }
    }

    // For colored models, skip reduction (group-level token accounting is
    // complex with reduction place remapping) and BFS on original net with
    // the colored group observer.
    if !colored_groups.is_empty() {
        let mut observer = OneSafeObserver::new_colored(colored_groups.to_vec());
        let result = if config.checkpoint().is_some() {
            match crate::explorer::explore_checkpointable_observer(net, config, &mut observer) {
                Ok(result) => result,
                Err(error) => return checkpoint_cannot_compute("OneSafe", &error),
            }
        } else {
            explore_observer(net, config, &mut observer)
        };
        return if !observer.is_safe() {
            Verdict::False
        } else if result.completed {
            Verdict::True
        } else {
            Verdict::CannotCompute
        };
    }

    // OneSafe reasons directly on reduced token magnitudes, so it must stay on
    // the structural-only path until it becomes scale-aware. It also needs a
    // stricter reduction contract than deadlock: source-place elimination,
    // agglomeration, and non-decreasing place removal can hide token counts > 1.
    let reduced = match reduce_iterative_structural_one_safe(net) {
        Ok(reduced) => reduced,
        Err(error) => return reduction_cannot_compute("OneSafe", &error),
    };
    let config = config.refitted_for_net(&reduced.net);
    let removed_unsafe = reduced
        .report
        .constant_places
        .iter()
        .chain(reduced.report.isolated_places.iter())
        .any(|&place| reduced.constant_value(place).is_some_and(|value| value > 1));
    if removed_unsafe {
        return Verdict::False;
    }

    // POR: places already proven 1-safe by reduced-net structural bounds do not
    // need to stay visible. That leaves a smaller safety-relevant subset on many
    // MCC-style models with independent resource-conserving subnets.
    let por_config = one_safe_por_config(&reduced, &config);
    let mut observer = OneSafeObserver::new();
    let result = if por_config.checkpoint().is_some() {
        match crate::explorer::explore_checkpointable_observer(
            &reduced.net,
            &por_config,
            &mut observer,
        ) {
            Ok(result) => result,
            Err(error) => return checkpoint_cannot_compute("OneSafe", &error),
        }
    } else {
        explore_observer(&reduced.net, &por_config, &mut observer)
    };

    if !observer.is_safe() {
        Verdict::False
    } else if result.completed {
        // LP-redundant places were removed from the reduced net but their
        // values may exceed 1 in the original net. The P-invariant upper
        // bound C/d is the maximum possible value; if it exceeds 1, we
        // cannot guarantee 1-safety from the reduced net alone.
        let redundant_bounded = reduced
            .reconstructions
            .iter()
            .all(|r| r.constant / r.divisor <= 1);
        if redundant_bounded {
            Verdict::True
        } else {
            Verdict::CannotCompute
        }
    } else {
        Verdict::CannotCompute
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deadlock_portfolio_bfs_workers_contract() {
        // workers == 1: sequential, no portfolio
        assert_eq!(deadlock_portfolio_bfs_workers(1), None);
        // workers == 2: portfolio with 1 BFS worker
        assert_eq!(deadlock_portfolio_bfs_workers(2), Some(1));
        // workers == 4 (MCC default): portfolio with 3 BFS workers
        assert_eq!(deadlock_portfolio_bfs_workers(4), Some(3));
        // workers == 0 edge case: sequential
        assert_eq!(deadlock_portfolio_bfs_workers(0), None);
    }
}
