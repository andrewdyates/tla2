// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
use super::super::maximal_path_suffix::{af_holds_from_mask, eg_holds_from_mask};
use super::super::query_support::{
    closure_on_reduced_net, ctl_support_with_aliases, relevance_cone_on_reduced_net,
};
use super::super::reachability::check_reachability_properties_with_aliases;
use super::checker::CtlChecker;
use super::local_checker::LocalCtlChecker;
use super::resolve;
use super::routing::{
    classify_shallow_ctl, classify_shallow_ctl_suffix, ctl_batch_contains_next_step, ShallowCtl,
    ShallowCtlSuffix,
};
use super::{is_known_mcc_ctl_soundness_guard, SoundnessGuardMode};
use crate::explorer::{explore_full, ExplorationConfig};
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::petri_net::PetriNet;
use crate::property_xml::{
    CtlFormula, Formula, PathQuantifier, Property, ReachabilityFormula, StatePredicate,
};
use crate::query_slice::{build_query_local_slice, build_query_slice};
use crate::reduction::{reduce_iterative_structural_with_mode, ReducedNet, ReductionMode};
use crate::resolved_predicate::{
    count_unresolved_with_aliases, eval_predicate, resolve_predicate_with_aliases,
};
use std::collections::{HashMap, HashSet};

fn flush_shallow_results(
    properties: &[Property],
    shallow_map: &HashMap<String, Verdict>,
    flushed_ids: &mut HashSet<String>,
    flush: bool,
) {
    if !flush {
        return;
    }

    for prop in properties {
        if flushed_ids.contains(&prop.id) {
            continue;
        }
        if let Some(verdict) = shallow_map.get(&prop.id) {
            println!("FORMULA {} {} TECHNIQUES EXPLICIT", prop.id, verdict);
            flushed_ids.insert(prop.id.clone());
        }
    }
}

fn collect_shallow_or_cannot_compute(
    properties: &[Property],
    shallow_map: &HashMap<String, Verdict>,
    flushed_ids: &HashSet<String>,
) -> Vec<(String, Verdict)> {
    properties
        .iter()
        .filter_map(|prop| {
            if flushed_ids.contains(&prop.id) {
                return None;
            }
            let verdict = shallow_map
                .get(&prop.id)
                .copied()
                .unwrap_or(Verdict::CannotCompute);
            Some((prop.id.clone(), verdict))
        })
        .collect()
}
/// Count unresolved names in a CTL formula's atoms.
pub(super) fn count_unresolved_ctl_with_aliases(
    formula: &CtlFormula,
    aliases: &PropertyAliases,
) -> (usize, usize) {
    match formula {
        CtlFormula::Atom(pred) => count_unresolved_with_aliases(pred, aliases),
        CtlFormula::Not(inner)
        | CtlFormula::EX(inner)
        | CtlFormula::AX(inner)
        | CtlFormula::EF(inner)
        | CtlFormula::AF(inner)
        | CtlFormula::EG(inner)
        | CtlFormula::AG(inner) => count_unresolved_ctl_with_aliases(inner, aliases),
        CtlFormula::And(children) | CtlFormula::Or(children) => {
            children.iter().fold((0, 0), |(t, u), c| {
                let (ct, cu) = count_unresolved_ctl_with_aliases(c, aliases);
                (t + ct, u + cu)
            })
        }
        CtlFormula::EU(phi, psi) | CtlFormula::AU(phi, psi) => {
            let (pt, pu) = count_unresolved_ctl_with_aliases(phi, aliases);
            let (qt, qu) = count_unresolved_ctl_with_aliases(psi, aliases);
            (pt + qt, pu + qu)
        }
    }
}

pub(super) fn check_ctl_properties_inner(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
    guard_mode: SoundnessGuardMode,
    flush: bool,
) -> Vec<(String, Verdict)> {
    // Simplify formulas using structural facts and LP proofs.
    let simplified =
        crate::formula_simplify::simplify_properties_with_aliases(net, properties, aliases);
    let properties = simplified.as_slice();
    let mut flushed_ids = HashSet::new();

    let mut shallow_map: HashMap<String, Verdict> = {
        let shallow_reachability_props: Vec<Property> = properties
            .iter()
            .filter_map(|prop| {
                let Formula::Ctl(ctl) = &prop.formula else {
                    return None;
                };
                let class = classify_shallow_ctl(ctl)?;
                let (quantifier, predicate) = match class {
                    ShallowCtl::ExistsFinally(pred) => (PathQuantifier::EF, pred),
                    ShallowCtl::AlwaysGlobally(pred) => (PathQuantifier::AG, pred),
                };
                Some(Property {
                    id: prop.id.clone(),
                    formula: Formula::Reachability(ReachabilityFormula {
                        quantifier,
                        predicate,
                    }),
                })
            })
            .collect();

        if !shallow_reachability_props.is_empty() {
            let shallow_count = shallow_reachability_props.len();
            let total = properties.len();
            eprintln!(
                "CTL shallow routing: {shallow_count}/{total} properties routed to reachability"
            );
            check_reachability_properties_with_aliases(
                net,
                &shallow_reachability_props,
                aliases,
                config,
            )
            .into_iter()
            .filter(|(_, verdict)| *verdict != Verdict::CannotCompute)
            .filter(|(id, verdict)| {
                let Some(prop) = shallow_reachability_props
                    .iter()
                    .find(|prop| &prop.id == id)
                else {
                    return true;
                };
                let Formula::Reachability(rf) = &prop.formula else {
                    return true;
                };
                let resolved = resolve_predicate_with_aliases(&rf.predicate, aliases);
                let init_holds = eval_predicate(&resolved, &net.initial_marking, net);
                match (rf.quantifier, *verdict) {
                    (PathQuantifier::EF, Verdict::False) if init_holds => {
                        eprintln!(
                            "CTL shallow sanity: {} EF verdict FALSE contradicts \
                             initial state -> falling through to full CTL",
                            id
                        );
                        false
                    }
                    (PathQuantifier::AG, Verdict::True) if !init_holds => {
                        eprintln!(
                            "CTL shallow sanity: {} AG verdict TRUE contradicts \
                             initial state -> falling through to full CTL",
                            id
                        );
                        false
                    }
                    _ => true,
                }
            })
            .collect()
        } else {
            HashMap::new()
        }
    };

    // Inject formulas that simplified to constant verdicts into the shallow
    // map. The simplifier may collapse e.g. AG(trivially_true) → Atom(True),
    // removing the temporal wrapper that classify_shallow_ctl needs.
    for prop in properties {
        match &prop.formula {
            Formula::Ctl(CtlFormula::Atom(StatePredicate::True)) => {
                shallow_map.insert(prop.id.clone(), Verdict::True);
            }
            Formula::Ctl(CtlFormula::Atom(StatePredicate::False)) => {
                shallow_map.insert(prop.id.clone(), Verdict::False);
            }
            _ => {}
        }
    }

    flush_shallow_results(properties, &shallow_map, &mut flushed_ids, flush);

    if properties
        .iter()
        .all(|prop| shallow_map.contains_key(&prop.id))
    {
        return properties
            .iter()
            .filter_map(|prop| {
                if flushed_ids.contains(&prop.id) {
                    return None;
                }
                let verdict = shallow_map
                    .get(&prop.id)
                    .cloned()
                    .unwrap_or(Verdict::CannotCompute);
                Some((prop.id.clone(), verdict))
            })
            .collect();
    }

    let suffix_props: Vec<(String, ShallowCtlSuffix)> = properties
        .iter()
        .filter(|prop| !shallow_map.contains_key(&prop.id))
        .filter_map(|prop| {
            let Formula::Ctl(ctl) = &prop.formula else {
                return None;
            };
            classify_shallow_ctl_suffix(ctl).map(|class| (prop.id.clone(), class))
        })
        .collect();

    if !suffix_props.is_empty() {
        let suffix_count = suffix_props.len();
        let total = properties.len();
        eprintln!(
            "CTL suffix routing: {suffix_count}/{total} properties routed to suffix analysis"
        );

        let identity = ReducedNet::identity(net);
        let slice = ctl_support_with_aliases(&identity, properties, aliases).and_then(|support| {
            let closure = closure_on_reduced_net(net, support);
            build_query_slice(net, &closure)
        });

        let explore_net = slice.as_ref().map_or(net, |slice| &slice.net);
        let suffix_config = config.refitted_for_full_graph(explore_net);
        let full = explore_full(explore_net, &suffix_config);

        if full.graph.completed {
            let markings: Vec<Vec<u64>> = if let Some(ref slice) = slice {
                full.markings
                    .iter()
                    .map(|marking| {
                        let mut original = vec![0u64; net.num_places()];
                        for (sliced_idx, &tokens) in marking.iter().enumerate() {
                            original[slice.place_unmap[sliced_idx].0 as usize] = tokens;
                        }
                        original
                    })
                    .collect()
            } else {
                full.markings.clone()
            };

            for (prop_id, class) in &suffix_props {
                let predicate = match class {
                    ShallowCtlSuffix::ExistsGlobally(predicate) => predicate,
                    ShallowCtlSuffix::AlwaysFinally(predicate) => predicate,
                };
                let resolved = resolve_predicate_with_aliases(predicate, aliases);

                let sat: Vec<bool> = markings
                    .iter()
                    .map(|marking| eval_predicate(&resolved, marking, net))
                    .collect();

                let verdict = match class {
                    ShallowCtlSuffix::ExistsGlobally(_) => {
                        if eg_holds_from_mask(&full.graph, &sat) {
                            Verdict::True
                        } else {
                            Verdict::False
                        }
                    }
                    ShallowCtlSuffix::AlwaysFinally(_) => {
                        if af_holds_from_mask(&full.graph, &sat) {
                            Verdict::True
                        } else {
                            Verdict::False
                        }
                    }
                };

                let init_holds = eval_predicate(&resolved, &net.initial_marking, net);
                let sane = !matches!(
                    (class, verdict),
                    (ShallowCtlSuffix::ExistsGlobally(_), Verdict::True) if !init_holds
                ) && !matches!(
                    (class, verdict),
                    (ShallowCtlSuffix::AlwaysFinally(_), Verdict::False) if init_holds
                );

                if sane {
                    shallow_map.insert(prop_id.clone(), verdict);
                }
            }
        }
    }

    if properties
        .iter()
        .all(|prop| shallow_map.contains_key(&prop.id))
    {
        return properties
            .iter()
            .filter_map(|prop| {
                if flushed_ids.contains(&prop.id) {
                    return None;
                }
                let verdict = shallow_map
                    .get(&prop.id)
                    .cloned()
                    .unwrap_or(Verdict::CannotCompute);
                Some((prop.id.clone(), verdict))
            })
            .collect();
    }

    // Query-aware reduction: select mode based on whether the CTL batch
    // contains next-step operators (EX/AX). CTLWithNext mode applies only
    // dead/constant/isolated reductions (universally safe). NextFreeCTL
    // additionally allows source-place, parallel-place, LP-redundant, and
    // duplicate/dominated transition removal.
    //
    // This replaces the historical identity-only path. The prior broader
    // structural lane (with agglomeration) was unsound for CTL per IBM5964
    // CTLCardinality-11. The new mode-gated approach is strictly conservative:
    // CTLWithNext only applies dead/constant/isolated (proven safe for all
    // temporal logics), and NextFreeCTL excludes agglomeration.
    let has_next_step = ctl_batch_contains_next_step(properties);
    let ctl_mode = if has_next_step {
        ReductionMode::CTLWithNext
    } else {
        ReductionMode::NextFreeCTL
    };
    let reduced = {
        let support =
            ctl_support_with_aliases(&ReducedNet::identity(net), properties, aliases);
        let protected = match support {
            Some(ref s) => s.places.clone(),
            None => vec![],
        };
        match reduce_iterative_structural_with_mode(net, &protected, ctl_mode) {
            Ok(r) => {
                let removed = r.report.places_removed() + r.report.transitions_removed();
                if removed > 0 {
                    eprintln!(
                        "CTL {mode:?} reduction: removed {removed} elements \
                         ({p} places, {t} transitions)",
                        mode = ctl_mode,
                        p = r.report.places_removed(),
                        t = r.report.transitions_removed(),
                    );
                }
                r
            }
            Err(error) => {
                eprintln!("CTL reduction error: {error} — falling back to identity");
                ReducedNet::identity(net)
            }
        }
    };
    let use_deep_slice = !has_next_step;
    let slice = ctl_support_with_aliases(&reduced, properties, aliases).and_then(|support| {
        if use_deep_slice {
            let cone = relevance_cone_on_reduced_net(&reduced.net, support);
            build_query_local_slice(&reduced.net, &cone)
        } else {
            let closure = closure_on_reduced_net(&reduced.net, support);
            build_query_slice(&reduced.net, &closure)
        }
    });

    let explore_net = slice.as_ref().map_or(&reduced.net, |slice| &slice.net);
    let explore_config = config.refitted_for_full_graph(explore_net);
    let mut full = explore_full(explore_net, &explore_config);
    if !full.graph.completed {
        return properties
            .iter()
            .filter_map(|prop| {
                if flushed_ids.contains(&prop.id) {
                    return None;
                }
                if let Some(&verdict) = shallow_map.get(&prop.id) {
                    return Some((prop.id.clone(), verdict));
                }

                if guard_mode == SoundnessGuardMode::Enforce
                    && is_known_mcc_ctl_soundness_guard(&prop.id)
                {
                    return Some((prop.id.clone(), Verdict::CannotCompute));
                }

                let verdict = match &prop.formula {
                    Formula::Ctl(ctl) => {
                        let (total, unresolved) = count_unresolved_ctl_with_aliases(ctl, aliases);
                        if unresolved > 0 {
                            eprintln!(
                                "CTL resolution guard: {} has {unresolved}/{total} \
                                 unresolved names -> CANNOT_COMPUTE",
                                prop.id
                            );
                            return Some((prop.id.clone(), Verdict::CannotCompute));
                        }

                        let resolved = resolve::resolve_ctl_with_aliases(ctl, aliases);
                        let mut checker = LocalCtlChecker::new(net, config);
                        match checker.eval_root(&resolved) {
                            Ok(true) => Verdict::True,
                            Ok(false) => Verdict::False,
                            Err(error) => {
                                eprintln!(
                                    "CTL local fallback: {} -> CANNOT_COMPUTE ({error})",
                                    prop.id
                                );
                                Verdict::CannotCompute
                            }
                        }
                    }
                    _ => Verdict::CannotCompute,
                };
                Some((prop.id.clone(), verdict))
            })
            .collect();
    }

    for marking in &mut full.markings {
        if let Some(ref slice) = slice {
            let mut reduced_marking = vec![0u64; reduced.net.num_places()];
            for (sliced_idx, &tokens) in marking.iter().enumerate() {
                reduced_marking[slice.place_unmap[sliced_idx].0 as usize] = tokens;
            }
            match reduced.expand_marking(&reduced_marking) {
                Ok(expanded) => *marking = expanded,
                Err(error) => {
                    eprintln!("CTL: CANNOT_COMPUTE ({error})");
                    return collect_shallow_or_cannot_compute(
                        properties,
                        &shallow_map,
                        &flushed_ids,
                    );
                }
            }
        } else {
            match reduced.expand_marking(marking) {
                Ok(expanded) => *marking = expanded,
                Err(error) => {
                    eprintln!("CTL: CANNOT_COMPUTE ({error})");
                    return collect_shallow_or_cannot_compute(
                        properties,
                        &shallow_map,
                        &flushed_ids,
                    );
                }
            }
        }
    }

    let checker = CtlChecker::new(&full, net);

    properties
        .iter()
        .filter_map(|prop| {
            if flushed_ids.contains(&prop.id) {
                return None;
            }
            if let Some(&verdict) = shallow_map.get(&prop.id) {
                return Some((prop.id.clone(), verdict));
            }

            if guard_mode == SoundnessGuardMode::Enforce
                && is_known_mcc_ctl_soundness_guard(&prop.id)
            {
                return Some((prop.id.clone(), Verdict::CannotCompute));
            }

            let verdict = match &prop.formula {
                Formula::Ctl(ctl) => {
                    let (total, unresolved) = count_unresolved_ctl_with_aliases(ctl, aliases);
                    if unresolved > 0 {
                        eprintln!(
                            "CTL resolution guard: {} has {unresolved}/{total} \
                             unresolved names -> CANNOT_COMPUTE",
                            prop.id
                        );
                        return Some((prop.id.clone(), Verdict::CannotCompute));
                    }

                    let resolved = resolve::resolve_ctl_with_aliases(ctl, aliases);
                    if checker.eval(&resolved)[0] {
                        Verdict::True
                    } else {
                        Verdict::False
                    }
                }
                _ => Verdict::CannotCompute,
            };
            Some((prop.id.clone(), verdict))
        })
        .collect()
}
