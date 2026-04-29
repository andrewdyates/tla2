// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::super::examination_plan::ExecutionPlan;
use super::common::checkpoint_cannot_compute;
use crate::examinations::global_properties_bmc;
use crate::examinations::liveness::check_liveness;
use crate::examinations::quasi_liveness::QuasiLivenessObserver;
use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::petri_net::PetriNet;
use crate::reduction::ReducedNet;
use crate::scc::{bottom_sccs, tarjan_scc};
use crate::stubborn::PorStrategy;

pub(crate) fn quasi_liveness_verdict(net: &PetriNet, config: &ExplorationConfig) -> Verdict {
    // --- Pre-reduction structural analysis on the ORIGINAL net ---
    // L4-liveness implies quasi-liveness (L1). Run on the original net before
    // reduction because agglomeration can destroy the free-choice property.
    // Only the TRUE direction is sound: structural non-liveness does NOT
    // imply non-quasi-liveness (a net can be quasi-live without being L4-live).
    if let Some(true) = crate::structural::structural_live(net) {
        eprintln!("QuasiLiveness: structurally live (original net, free-choice siphon/trap)");
        return Verdict::True;
    }

    // LP dead-transition on the original net: if some transition can never fire
    // (LP upper bound insufficient), the net is NOT quasi-live.
    if let Some(false) = crate::structural::lp_dead_transition(net) {
        eprintln!("QuasiLiveness: LP-proved dead transition on original net");
        return Verdict::False;
    }

    // --- Identity net (no reduction) ---
    // Structural reductions are currently unsound for QuasiLiveness: on nets
    // like FMS-PT-*, agglomeration/source-place elimination suppresses real
    // firing behavior, flipping the verdict from TRUE to FALSE. Use the
    // identity net until a sound reduction contract is validated.
    let reduced = ReducedNet::identity(net);
    let config = config.refitted_for_net(&reduced.net);

    // --- Post-reduction structural analysis on the REDUCED net ---
    // Structural liveness is stronger than quasi-liveness. On ordinary
    // free-choice nets, siphon/trap coverage can therefore short-circuit the
    // examination before exploration.
    if let Some(true) = crate::structural::structural_live(&reduced.net) {
        eprintln!("QuasiLiveness: structurally live (free-choice siphon/trap)");
        return Verdict::True;
    }

    // LP dead-transition check: if the LP state equation proves some input
    // place can never have enough tokens, that transition can never fire →
    // net is NOT quasi-live. Works on ALL net types.
    if let Some(false) = crate::structural::lp_dead_transition(&reduced.net) {
        eprintln!("QuasiLiveness: LP-proved dead transition (upper bound insufficient)");
        return Verdict::False;
    }

    // SMT-based per-transition BMC on the reduced net.
    let bmc_resolved =
        global_properties_bmc::run_quasi_liveness_bmc(&reduced.net, config.deadline());
    if bmc_resolved.iter().all(|&r| r) {
        eprintln!("QuasiLiveness: all transitions resolved by BMC");
        return Verdict::True;
    }

    let plan = ExecutionPlan::observer(PorStrategy::None);
    // Seed the observer with BMC results so BFS only needs to discover
    // the remaining unresolved transitions.
    let mut observer = QuasiLivenessObserver::new_seeded(&bmc_resolved);
    let result = match plan.run_checkpointable_observer(&reduced.net, &config, &mut observer) {
        Ok(result) => result,
        Err(error) => return checkpoint_cannot_compute("QuasiLiveness", &error),
    };

    if observer.all_fired() {
        Verdict::True
    } else if result.completed {
        Verdict::False
    } else {
        Verdict::CannotCompute
    }
}

pub(crate) fn liveness_verdict(net: &PetriNet, config: &ExplorationConfig) -> Verdict {
    // --- Pre-reduction structural analysis on the ORIGINAL net ---
    // Reduction (agglomeration) can destroy free-choice structure, making
    // structural_live return None on the reduced net when it would have
    // succeeded on the original. These checks are O(|P|²·|T|) — negligible
    // compared to BFS — and resolve nets that become non-free-choice after
    // reduction.
    match crate::structural::structural_live(net) {
        Some(true) => {
            eprintln!("Liveness: structurally live (original net, free-choice siphon/trap)");
            return Verdict::True;
        }
        Some(false) => {
            eprintln!("Liveness: structurally non-live (original net, free-choice siphon/trap)");
            return Verdict::False;
        }
        None => {}
    }

    if let Some(false) = crate::structural::structural_not_live_t_semiflows(net) {
        eprintln!("Liveness: uncovered transition on original net (T-semiflow + bounded)");
        return Verdict::False;
    }

    if let Some(false) = crate::structural::lp_dead_transition(net) {
        eprintln!("Liveness: LP-proved dead transition on original net");
        return Verdict::False;
    }

    // --- Identity net (no reduction) ---
    // Structural reductions are currently unsound for Liveness: on nets like
    // FMS-PT-*, agglomeration/source-place elimination suppresses real firing
    // behavior, flipping the verdict from TRUE to FALSE. Use the identity net
    // until a sound reduction contract is validated.
    let reduced = ReducedNet::identity(net);
    let config = config.refitted_for_net(&reduced.net);

    // --- Post-reduction structural analysis on the REDUCED net ---
    // The reduced net may have different structural properties (smaller, possibly
    // free-choice when the original was not). Re-run structural checks.
    match crate::structural::structural_live(&reduced.net) {
        Some(true) => {
            eprintln!("Liveness: structurally live (free-choice siphon/trap)");
            return Verdict::True;
        }
        Some(false) => {
            eprintln!("Liveness: structurally non-live (free-choice siphon/trap)");
            return Verdict::False;
        }
        None => {}
    }

    // T-semiflow coverage: sound FALSE shortcut on ALL bounded nets (not just
    // free-choice). An uncovered transition can fire at most finitely many
    // times in a bounded net, disproving L4-liveness.
    if let Some(false) = crate::structural::structural_not_live_t_semiflows(&reduced.net) {
        eprintln!("Liveness: uncovered transition (T-semiflow + bounded)");
        return Verdict::False;
    }

    // LP dead-transition check: if the LP state equation proves some input
    // place can never have enough tokens for a transition to fire, that
    // transition is dead → net is NOT live. Works on ALL net types.
    if let Some(false) = crate::structural::lp_dead_transition(&reduced.net) {
        eprintln!("Liveness: LP-proved dead transition (upper bound insufficient)");
        return Verdict::False;
    }

    // Deadlock implies non-liveness: if any reachable state is a deadlock
    // (no transition enabled), then every transition is dead from that state,
    // directly disproving L4-liveness. This catches non-free-choice nets
    // where siphon/trap analysis is inconclusive but BMC + k-induction can
    // find or rule out deadlocks.
    if let Some(true) = global_properties_bmc::run_deadlock_bmc(&reduced.net, config.deadline()) {
        eprintln!("Liveness: reachable deadlock found (BMC) → NOT live");
        return Verdict::False;
    }

    // Per-transition liveness BMC: for each transition, check if it can
    // become permanently disabled from some reachable marking. Uses
    // k-induction to prove "disabled → stays disabled" combined with BMC
    // to find a reachable marking where the transition is disabled.
    if let Some(false) = global_properties_bmc::run_liveness_bmc(&reduced.net, config.deadline()) {
        eprintln!("Liveness: transition permanently disabled (BMC + k-induction) → NOT live");
        return Verdict::False;
    }

    let live_transition_count = reduced.transition_unmap.len();

    let plan = ExecutionPlan::graph();
    let graph = plan.run_graph(&reduced.net, &config);

    if !graph.completed {
        Verdict::CannotCompute
    } else {
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        let live = check_liveness(&graph, &sccs, &bottoms, live_transition_count);
        if live {
            Verdict::True
        } else {
            Verdict::False
        }
    }
}
