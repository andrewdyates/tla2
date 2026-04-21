// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RF-10 reduction diagnostics and expansion soundness probes for NeoElection-COL-2.

use super::*;
use fixtures::mcc_input_dir;

/// Diagnostic: check predicate evaluation on the initial marking for RF-10.
///
/// The formula is `AG(NOT is-fireable(T-poll__handleAskP) OR is-fireable(T-sendAnnPs__end))`.
/// A counterexample is any state where is-fireable(handleAskP) AND NOT is-fireable(sendAnnPs__end).
#[test]
fn test_neo_election_rf10_predicate_initial_marking() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    let col = load_model_dir(&dir).expect("COL");

    // Parse and resolve RF-10 predicate.
    let props =
        crate::property_xml::parse_properties(&dir, "ReachabilityFireability").expect("parse RF");
    let prop_10 = &props[10]; // -2024-10
    assert!(
        prop_10.id.ends_with("-10"),
        "expected property -10, got {}",
        prop_10.id
    );
    let rf = match &prop_10.formula {
        Formula::Reachability(rf) => rf,
        _ => panic!("expected Reachability"),
    };

    // Resolve predicate with aliases.
    let resolved =
        crate::resolved_predicate::resolve_predicate_with_aliases(&rf.predicate, col.aliases());

    // Evaluate on initial marking.
    let init_val =
        crate::resolved_predicate::eval_predicate(&resolved, &col.net().initial_marking, col.net());
    eprintln!("RF-10 predicate on initial marking: {init_val}");

    // Also check: is any handleAskP enabled at initial marking?
    let ask_indices = col.aliases().resolve_transitions("T-poll__handleAskP");
    let ask_enabled = ask_indices.map(|idxs| {
        idxs.iter()
            .any(|&t| col.net().is_enabled(&col.net().initial_marking, t))
    });
    eprintln!("T-poll__handleAskP enabled at M0: {:?}", ask_enabled);

    let end_indices = col.aliases().resolve_transitions("T-sendAnnPs__end");
    let end_enabled = end_indices.map(|idxs| {
        idxs.iter()
            .any(|&t| col.net().is_enabled(&col.net().initial_marking, t))
    });
    eprintln!("T-sendAnnPs__end enabled at M0: {:?}", end_enabled);

    // Run simplification and check result.
    let facts = crate::formula_simplify::compute_facts(col.net());
    let simplified = crate::formula_simplify::simplify_predicate(
        &rf.predicate,
        col.net(),
        &facts,
        col.aliases(),
    );
    eprintln!("Simplified predicate: {:?}", simplified);

    // Now run JUST exploration (no reduction, no slicing) to count states.
    let mut observer =
        crate::examinations::reachability::ReachabilityObserver::new(col.net(), &props[10..11]);
    let result = crate::explorer::explore_observer(
        col.net(),
        &ExplorationConfig::new(50_000).with_workers(1),
        &mut observer,
    );
    eprintln!(
        "Unreduced exploration: completed={}, states={}",
        result.completed, result.states_visited
    );
    eprintln!("stopped_by_observer={}", result.stopped_by_observer);

    // Compare: PT model state space.
    let pt = load_model_dir(&mcc_input_dir("NeoElection-PT-2")).expect("PT");
    let result_pt = crate::explorer::explore_observer(
        pt.net(),
        &ExplorationConfig::new(50_000).with_workers(1),
        &mut crate::examinations::reachability::ReachabilityObserver::new(pt.net(), &[]),
    );
    eprintln!(
        "PT model: states={}, completed={}",
        result_pt.states_visited, result_pt.completed
    );

    // Print net sizes for comparison.
    eprintln!(
        "COL net: {} places, {} transitions",
        col.net().num_places(),
        col.net().num_transitions()
    );
    eprintln!(
        "PT net: {} places, {} transitions",
        pt.net().num_places(),
        pt.net().num_transitions()
    );
    eprintln!(
        "COL initial marking sum: {}",
        col.net().initial_marking.iter().sum::<u64>()
    );
    eprintln!(
        "PT initial marking sum: {}",
        pt.net().initial_marking.iter().sum::<u64>()
    );
}

/// Isolate whether the RF-10 wrong answer is from alias resolution or reduction.
///
/// Runs BFS on the UNREDUCED COL net with CORRECT COL aliases (not identity).
/// If this gives the wrong answer, the bug is in alias resolution.
/// If correct, the bug is in the reduction pipeline.
#[test]
fn test_neo_election_rf10_unreduced_with_col_aliases() {
    use crate::examinations::reachability::PropertyTracker;
    use crate::resolved_predicate::resolve_predicate_with_aliases;

    let dir = mcc_input_dir("NeoElection-COL-2");
    let col = load_model_dir(&dir).expect("COL");
    let props =
        crate::property_xml::parse_properties(&dir, "ReachabilityFireability").expect("parse RF");

    // Resolve RF-10 with the CORRECT COL aliases.
    let prop_10 = &props[10];
    assert!(
        prop_10.id.ends_with("-10"),
        "expected -10, got {}",
        prop_10.id
    );
    let rf = match &prop_10.formula {
        Formula::Reachability(rf) => rf,
        _ => panic!("expected Reachability"),
    };

    let resolved = resolve_predicate_with_aliases(&rf.predicate, col.aliases());
    eprintln!("RF-10 resolved predicate: {:?}", resolved);

    // Build tracker for just RF-10.
    let trackers = vec![PropertyTracker {
        id: prop_10.id.clone(),
        quantifier: rf.quantifier,
        predicate: resolved,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    // Explore UNREDUCED COL net with the correct COL aliases.
    let mut observer =
        crate::examinations::reachability::ReachabilityObserver::from_trackers(col.net(), trackers);
    let config = ExplorationConfig::new(50_000).with_workers(1);
    let result = crate::explorer::explore_observer(col.net(), &config, &mut observer);

    eprintln!(
        "Unreduced COL (with COL aliases): completed={}, states={}",
        result.completed, result.states_visited
    );

    let results = observer.results_completed();
    let (_, verdict) = &results[0];
    eprintln!("RF-10 verdict on unreduced COL: {}", verdict);

    // Ground truth: RF-10 should be FALSE.
    assert!(
        !verdict,
        "RF-10 should be FALSE on unreduced COL net with correct COL aliases"
    );
}

/// Verify that the `predicate_transitions_survived` safety check detects
/// eliminated IsFireable transitions in the NeoElection-COL-2 reduced net.
///
/// The reduction eliminates all T-sendAnnPs__end transitions (part of
/// RF-10's IsFireable disjunction). Without the safety check, this produces
/// a false-positive AG=TRUE verdict (i.e., EF=FALSE→TRUE inversion).
/// The safety check forces a fallback to unreduced BFS.
#[test]
fn test_neo_election_rf10_safety_check_triggers() {
    use crate::examinations::query_support::reachability_support;
    use crate::examinations::reachability::PropertyTracker;
    use crate::reduction::{reduce_iterative_structural_with_protected, ReducedNet};
    use crate::resolved_predicate::{
        predicate_transitions_survived, resolve_predicate_with_aliases,
    };

    let dir = mcc_input_dir("NeoElection-COL-2");
    let col = load_model_dir(&dir).expect("COL");
    let props =
        crate::property_xml::parse_properties(&dir, "ReachabilityFireability").expect("parse RF");

    // Build all 16 trackers.
    let all_trackers: Vec<PropertyTracker> = props
        .iter()
        .filter_map(|prop| {
            let Formula::Reachability(ref r) = prop.formula else {
                return None;
            };
            Some(PropertyTracker {
                id: prop.id.clone(),
                quantifier: r.quantifier,
                predicate: resolve_predicate_with_aliases(&r.predicate, col.aliases()),
                verdict: None,
                resolved_by: None,
                flushed: false,
            })
        })
        .collect();
    assert_eq!(all_trackers.len(), 16);

    // Reduce with the same logic as the real pipeline.
    let identity = ReducedNet::identity(col.net());
    let support = reachability_support(&identity, &all_trackers).unwrap();
    // Inline protected_places_for_prefire (private in reachability.rs).
    let initial_protected = {
        let mut protected = support.places.clone();
        for (idx, targeted) in support.transitions.iter().enumerate() {
            if !*targeted {
                continue;
            }
            for arc in col.net().transitions[idx]
                .inputs
                .iter()
                .chain(col.net().transitions[idx].outputs.iter())
            {
                protected[arc.place.0 as usize] = true;
            }
        }
        protected
    };
    let reduced = reduce_iterative_structural_with_protected(col.net(), &initial_protected)
        .expect("reduction should succeed");

    // RF-10's T-sendAnnPs__end transitions must NOT all survive the reduction.
    let send_end_indices = col
        .aliases()
        .resolve_transitions("T-sendAnnPs__end")
        .expect("alias exists");
    let send_surviving = send_end_indices
        .iter()
        .filter(|t| reduced.transition_map[t.0 as usize].is_some())
        .count();
    assert_eq!(
        send_surviving, 0,
        "sendAnnPs__end transitions should all be eliminated by reduction"
    );

    // The safety check must detect this: RF-10's predicate references transitions
    // that were eliminated, so predicate_transitions_survived must return false.
    let rf10_tracker = &all_trackers[10];
    assert!(
        rf10_tracker.id.ends_with("-10"),
        "sanity check: tracker 10 is RF-10"
    );
    assert!(
        !predicate_transitions_survived(&rf10_tracker.predicate, &reduced.transition_map),
        "predicate_transitions_survived should return false for RF-10 \
         because sendAnnPs__end transitions were eliminated"
    );

    // The pipeline should NOT trust the reduced BFS for RF-10; it should
    // fall back to unreduced BFS. Verify the full pipeline produces the
    // correct answer.
    let config = ExplorationConfig::new(50_000).with_workers(1);
    let records = collect_examination_for_model(
        &col,
        crate::examination::Examination::ReachabilityFireability,
        &config,
    )
    .expect("should succeed");

    let rf10_record = records
        .iter()
        .find(|r| r.formula_id.ends_with("-10"))
        .expect("RF-10 record");
    match rf10_record.value {
        crate::examination::ExaminationValue::Verdict(crate::examination::Verdict::False) => {
            // Correct: ground truth for RF-10 is FALSE.
        }
        ref v => panic!("RF-10 should be FALSE but got {:?}", v),
    }
}

/// Diagnostic: expand every reduced-net marking and verify soundness.
/// Checks:
///   (a) P-invariant reconstruction exactness (division truncation)
///   (b) expanded marking is in the unreduced state space
///   (c) which state triggers the false-positive IsFireable
#[test]
fn test_neo_election_rf10_expansion_soundness() {
    use crate::examinations::query_support::reachability_support;
    use crate::examinations::reachability::PropertyTracker;
    use crate::reduction::{reduce_iterative_structural_with_protected, ReducedNet};
    use crate::resolved_predicate::resolve_predicate_with_aliases;

    let dir = mcc_input_dir("NeoElection-COL-2");
    let col = load_model_dir(&dir).expect("COL");
    let props =
        crate::property_xml::parse_properties(&dir, "ReachabilityFireability").expect("parse RF");

    // Build all 16 trackers (same as real pipeline).
    let all_trackers: Vec<PropertyTracker> = props
        .iter()
        .filter_map(|prop| {
            let Formula::Reachability(ref r) = prop.formula else {
                return None;
            };
            Some(PropertyTracker {
                id: prop.id.clone(),
                quantifier: r.quantifier,
                predicate: resolve_predicate_with_aliases(&r.predicate, col.aliases()),
                verdict: None,
                resolved_by: None,
                flushed: false,
            })
        })
        .collect();

    // Reduce with same logic as real pipeline.
    let identity = ReducedNet::identity(col.net());
    let support = reachability_support(&identity, &all_trackers).unwrap();
    let mut initial_protected = support.places.clone();
    for (idx, targeted) in support.transitions.iter().enumerate() {
        if !*targeted {
            continue;
        }
        for arc in col.net().transitions[idx]
            .inputs
            .iter()
            .chain(col.net().transitions[idx].outputs.iter())
        {
            initial_protected[arc.place.0 as usize] = true;
        }
    }
    let reduced = reduce_iterative_structural_with_protected(col.net(), &initial_protected)
        .expect("reduction should succeed");

    eprintln!(
        "Reduced: {} places, {} transitions, {} reconstructions",
        reduced.net.num_places(),
        reduced.net.num_transitions(),
        reduced.reconstructions.len()
    );

    // Collect all reduced-net markings.
    struct MarkingCollector {
        markings: Vec<Vec<u64>>,
    }
    impl crate::explorer::ExplorationObserver for MarkingCollector {
        fn on_new_state(&mut self, marking: &[u64]) -> bool {
            self.markings.push(marking.to_vec());
            true
        }
        fn on_transition_fire(&mut self, _t: TransitionIdx) -> bool {
            true
        }
        fn on_deadlock(&mut self, _marking: &[u64]) {}
        fn is_done(&self) -> bool {
            false
        }
    }

    let config = ExplorationConfig::new(50_000).with_workers(1);
    let mut collector = MarkingCollector {
        markings: Vec::new(),
    };
    crate::explorer::explore(&reduced.net, &config, &mut collector);
    eprintln!("Reduced BFS: {} states", collector.markings.len());

    // Also collect all UNREDUCED markings (for state-space membership check).
    let mut unreduced_collector = MarkingCollector {
        markings: Vec::new(),
    };
    crate::explorer::explore(col.net(), &config, &mut unreduced_collector);
    let unreduced_set: std::collections::HashSet<Vec<u64>> =
        unreduced_collector.markings.into_iter().collect();
    eprintln!("Unreduced BFS: {} states", unreduced_set.len());

    // Get transition indices for RF-10.
    let handle_ask_indices: Vec<TransitionIdx> = col
        .aliases()
        .resolve_transitions("T-poll__handleAskP")
        .unwrap()
        .to_vec();
    let send_end_indices: Vec<TransitionIdx> = col
        .aliases()
        .resolve_transitions("T-sendAnnPs__end")
        .unwrap()
        .to_vec();

    let mut truncation_count = 0u32;
    let mut not_in_unreduced = 0u32;
    let mut rf10_triggers = 0u32;

    for (state_idx, reduced_marking) in collector.markings.iter().enumerate() {
        let expanded = reduced.expand_marking(reduced_marking).expect("expand");

        // Check (a): reconstruction exactness.
        for recon in &reduced.reconstructions {
            let weighted_sum: u64 = recon
                .terms
                .iter()
                .map(|&(PlaceIdx(p), w)| w * expanded[p as usize])
                .sum();
            let lhs = recon.divisor * expanded[recon.place.0 as usize] + weighted_sum;
            if lhs != recon.constant {
                truncation_count += 1;
                if truncation_count <= 3 {
                    eprintln!(
                        "  TRUNCATION at state {}, place {:?}: \
                         divisor*val + weighted_sum = {}*{} + {} = {} != constant {}",
                        state_idx,
                        recon.place,
                        recon.divisor,
                        expanded[recon.place.0 as usize],
                        weighted_sum,
                        lhs,
                        recon.constant,
                    );
                }
            }
        }

        // Check (b): is this expanded marking in the unreduced state space?
        if !unreduced_set.contains(&expanded) {
            not_in_unreduced += 1;
            if not_in_unreduced <= 3 {
                let diff_places: Vec<(usize, u64)> = expanded
                    .iter()
                    .enumerate()
                    .filter(|&(_, &v)| v > 0)
                    .map(|(i, &v)| (i, v))
                    .collect();
                eprintln!(
                    "  NOT IN UNREDUCED STATE SPACE at state {}: \
                     {} non-zero places (out of {})",
                    state_idx,
                    diff_places.len(),
                    expanded.len()
                );
            }
        }

        // Check (c): does RF-10's IsFireable trigger here?
        let handle_fireable = handle_ask_indices
            .iter()
            .any(|&t| col.net().is_enabled(&expanded, t));
        let send_fireable = send_end_indices
            .iter()
            .any(|&t| col.net().is_enabled(&expanded, t));
        if handle_fireable || send_fireable {
            rf10_triggers += 1;
            if rf10_triggers <= 3 {
                // Find which transition is "enabled".
                let enabled_handle: Vec<u32> = handle_ask_indices
                    .iter()
                    .filter(|&&t| col.net().is_enabled(&expanded, t))
                    .map(|t| t.0)
                    .collect();
                let enabled_send: Vec<u32> = send_end_indices
                    .iter()
                    .filter(|&&t| col.net().is_enabled(&expanded, t))
                    .map(|t| t.0)
                    .collect();
                eprintln!(
                    "  RF-10 TRIGGER at state {}: handle_ask={:?}, send_end={:?}",
                    state_idx, enabled_handle, enabled_send,
                );
            }
        }
    }

    eprintln!(
        "\nSummary: {} states, {} truncations, {} not in unreduced, {} RF-10 triggers",
        collector.markings.len(),
        truncation_count,
        not_in_unreduced,
        rf10_triggers,
    );

    assert_eq!(
        truncation_count, 0,
        "P-invariant reconstruction produced non-exact divisions"
    );
    assert_eq!(
        not_in_unreduced, 0,
        "Expanded markings not in unreduced state space — reduction is unsound"
    );
    assert_eq!(
        rf10_triggers, 0,
        "RF-10 should never trigger on correctly expanded markings"
    );
}

/// Diagnostic: compare RF-09 results with and without colored pre-unfolding
/// reductions to isolate whether the wrong answer is caused by the colored
/// constant-place collapsing.
#[test]
fn test_neo_election_rf09_colored_reduce_comparison() {
    let dir = mcc_input_dir("NeoElection-COL-2");

    // Load WITH colored reductions (the default pipeline).
    let col_reduced = load_model_dir(&dir).expect("COL with reduction");

    // Load WITHOUT colored reductions.
    let col_unreduced =
        crate::model::load_model_dir_no_colored_reduce(&dir).expect("COL without reduction");

    eprintln!(
        "With reduction:    {} places, {} transitions, marking sum={}",
        col_reduced.net().num_places(),
        col_reduced.net().num_transitions(),
        col_reduced.net().initial_marking.iter().sum::<u64>(),
    );
    eprintln!(
        "Without reduction: {} places, {} transitions, marking sum={}",
        col_unreduced.net().num_places(),
        col_unreduced.net().num_transitions(),
        col_unreduced.net().initial_marking.iter().sum::<u64>(),
    );

    let config = ExplorationConfig::new(50_000).with_workers(1);

    // Run full examination on both.
    let reduced_records =
        collect_examination_for_model(&col_reduced, Examination::ReachabilityFireability, &config)
            .expect("reduced RF");
    let unreduced_records = collect_examination_for_model(
        &col_unreduced,
        Examination::ReachabilityFireability,
        &config,
    )
    .expect("unreduced RF");

    assert_eq!(reduced_records.len(), unreduced_records.len());

    let truth = &super::neo_election_ground_truth::NEO_ELECTION_COL2_RF_TRUTH;
    let mut any_diverged = false;

    for (red, unred) in reduced_records.iter().zip(unreduced_records.iter()) {
        let idx: usize = red
            .formula_id
            .rsplit('-')
            .next()
            .and_then(|s| s.parse().ok())
            .expect("formula_id should end with numeric index");

        let red_verdict = match red.value {
            ExaminationValue::Verdict(Verdict::True) => Some(true),
            ExaminationValue::Verdict(Verdict::False) => Some(false),
            _ => None,
        };
        let unred_verdict = match unred.value {
            ExaminationValue::Verdict(Verdict::True) => Some(true),
            ExaminationValue::Verdict(Verdict::False) => Some(false),
            _ => None,
        };

        let reduced_correct = red_verdict.map(|v| v == truth[idx]);
        let _unreduced_correct = unred_verdict.map(|v| v == truth[idx]);

        if red_verdict != unred_verdict {
            any_diverged = true;
            eprintln!(
                "RF-{idx:02}: DIVERGED — reduced={red_verdict:?} unreduced={unred_verdict:?} truth={}",
                truth[idx],
            );
        } else if reduced_correct == Some(false) {
            eprintln!(
                "RF-{idx:02}: BOTH WRONG — verdict={red_verdict:?} truth={}",
                truth[idx],
            );
        }
    }

    // Check RF-09 specifically.
    let rf09_reduced = &reduced_records[9];
    let rf09_unreduced = &unreduced_records[9];
    eprintln!(
        "\nRF-09 (target): reduced={:?}, unreduced={:?}, truth={}",
        rf09_reduced.value, rf09_unreduced.value, truth[9],
    );

    // RF-09 ground truth is FALSE.
    match rf09_unreduced.value {
        ExaminationValue::Verdict(Verdict::False) => {
            eprintln!("RF-09 WITHOUT reduction: CORRECT (FALSE)");
        }
        ref v => {
            eprintln!("RF-09 WITHOUT reduction: {:?} (truth=false)", v);
        }
    }
    match rf09_reduced.value {
        ExaminationValue::Verdict(Verdict::False) => {
            eprintln!("RF-09 WITH reduction: CORRECT (FALSE)");
        }
        ref v => {
            eprintln!("RF-09 WITH reduction: {:?} (truth=false) — BUG", v);
        }
    }

    if any_diverged {
        eprintln!("\nColored reduction causes verdict divergence!");
    }

    // Compare alias resolutions for RF-09 transitions.
    let transitions_to_check = [
        "T-poll__handleAnnP1",
        "T-poll__iAmSecondary",
        "T-poll__handleRP",
    ];
    for tname in &transitions_to_check {
        let red_t = col_reduced.aliases().resolve_transitions(tname);
        let unred_t = col_unreduced.aliases().resolve_transitions(tname);
        let red_count = red_t.map(|v| v.len()).unwrap_or(0);
        let unred_count = unred_t.map(|v| v.len()).unwrap_or(0);
        eprintln!("  {tname}: reduced has {red_count} instances, unreduced has {unred_count}");
        // Transition indices may differ; compare input place structure.
        if let (Some(ridxs), Some(uidxs)) = (red_t, unred_t) {
            for (&ri, &ui) in ridxs.iter().zip(uidxs.iter()) {
                let rt = &col_reduced.net().transitions[ri.0 as usize];
                let ut = &col_unreduced.net().transitions[ui.0 as usize];
                let r_inputs: Vec<(u32, u64)> =
                    rt.inputs.iter().map(|a| (a.place.0, a.weight)).collect();
                let u_inputs: Vec<(u32, u64)> =
                    ut.inputs.iter().map(|a| (a.place.0, a.weight)).collect();
                if r_inputs != u_inputs {
                    eprintln!(
                        "    {} vs {}: DIFFERENT inputs! reduced={r_inputs:?} unreduced={u_inputs:?}",
                        rt.id, ut.id,
                    );
                }
            }
        }
    }

    // Compare state space sizes via raw BFS.
    struct StateCounter {
        count: usize,
    }
    impl crate::explorer::ExplorationObserver for StateCounter {
        fn on_new_state(&mut self, _: &[u64]) -> bool {
            self.count += 1;
            true
        }
        fn on_transition_fire(&mut self, _: crate::petri_net::TransitionIdx) -> bool {
            true
        }
        fn on_deadlock(&mut self, _: &[u64]) {}
        fn is_done(&self) -> bool {
            false
        }
    }

    let mut rc = StateCounter { count: 0 };
    crate::explorer::explore(col_reduced.net(), &config, &mut rc);
    let mut uc = StateCounter { count: 0 };
    crate::explorer::explore(col_unreduced.net(), &config, &mut uc);
    eprintln!("State space: reduced={}, unreduced={}", rc.count, uc.count);
}
