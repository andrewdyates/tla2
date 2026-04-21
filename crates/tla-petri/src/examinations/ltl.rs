// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LTL model checking for MCC LTLCardinality and LTLFireability examinations.
//!
//! Uses Buchi automaton product construction: negate the formula, convert to
//! a Generalized Buchi Automaton, build the product with the system's state
//! graph, and check for accepting cycles.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use crate::buchi::{check_ltl_on_the_fly, to_nnf, PorContext};
use crate::explorer::ExplorationConfig;
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::property_xml::{
    Formula, LtlFormula, PathQuantifier, Property, ReachabilityFormula, StatePredicate,
};
use crate::query_slice::{build_query_local_slice, build_query_slice, QuerySlice};
use crate::reduction::{
    reduce_iterative_structural_with_mode, ReducedNet, ReductionMode, ReductionReport,
};
use crate::resolved_predicate::count_unresolved_with_aliases;
use crate::stubborn::DependencyGraph;

use super::ltl_por::{formula_contains_next, ltl_visible_reduced_transitions};
use super::query_support::{
    closure_on_reduced_net, ltl_property_support_with_aliases, relevance_cone_on_reduced_net,
};
use super::reachability::check_reachability_properties_with_aliases;

/// Count unresolved place/transition names in an LTL formula's atoms.
///
/// Returns `(total_names, unresolved_count)`. If `unresolved_count > 0`,
/// the formula references names absent from the model — the resolved formula
/// is degenerate and evaluation may produce wrong answers.
fn count_unresolved_ltl(formula: &LtlFormula, aliases: &PropertyAliases) -> (usize, usize) {
    match formula {
        LtlFormula::Atom(pred) => count_unresolved_with_aliases(pred, aliases),
        LtlFormula::Not(inner)
        | LtlFormula::Next(inner)
        | LtlFormula::Finally(inner)
        | LtlFormula::Globally(inner) => count_unresolved_ltl(inner, aliases),
        LtlFormula::And(children) | LtlFormula::Or(children) => {
            children.iter().fold((0, 0), |(t, u), c| {
                let (ct, cu) = count_unresolved_ltl(c, aliases);
                (t + ct, u + cu)
            })
        }
        LtlFormula::Until(phi, psi) => {
            let (pt, pu) = count_unresolved_ltl(phi, aliases);
            let (qt, qu) = count_unresolved_ltl(psi, aliases);
            (pt + qt, pu + qu)
        }
    }
}

/// An LTL property reducible to or pre-filterable by reachability.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone, PartialEq, Eq))]
pub(crate) enum ShallowLtl {
    /// G(pred): AG(pred) — fully routable through reachability.
    Invariant(StatePredicate),
    /// F(pred): AF(pred) — pre-filterable but not fully routable.
    /// Try AG(pred) for quick TRUE, EF(pred) for quick FALSE.
    Eventually(StatePredicate),
}

/// Classify an LTL formula as shallow (reachability-relevant) or deep.
///
/// Returns `Some` for formulas that can be fully routed through, or
/// pre-filtered by, the reachability pipeline.
pub(crate) fn classify_shallow_ltl(formula: &LtlFormula) -> Option<ShallowLtl> {
    match formula {
        // G(atom) = AG(atom) — invariant
        LtlFormula::Globally(inner) => extract_state_pred_ltl(inner)
            .map(ShallowLtl::Invariant)
            .or_else(|| match inner.as_ref() {
                // G(G(atom)) = AG(atom) — idempotent
                LtlFormula::Globally(_) => classify_shallow_ltl(inner),
                _ => None,
            }),
        // F(atom) = AF(atom) — pre-filterable
        LtlFormula::Finally(inner) => extract_state_pred_ltl(inner)
            .map(ShallowLtl::Eventually)
            .or_else(|| match inner.as_ref() {
                // F(F(atom)) = AF(atom) — idempotent
                LtlFormula::Finally(_) => classify_shallow_ltl(inner),
                _ => None,
            }),
        // Not(F(atom)) = G(Not(atom)) — invariant
        // Not(G(atom)) = F(Not(atom)) — eventually
        LtlFormula::Not(inner) => match inner.as_ref() {
            LtlFormula::Finally(f_inner) => extract_state_pred_ltl(f_inner)
                .map(|pred| ShallowLtl::Invariant(StatePredicate::Not(Box::new(pred)))),
            LtlFormula::Globally(g_inner) => extract_state_pred_ltl(g_inner)
                .map(|pred| ShallowLtl::Eventually(StatePredicate::Not(Box::new(pred)))),
            _ => None,
        },
        _ => None,
    }
}

/// Extract a pure state predicate from an LTL formula.
///
/// Returns `Some` only if the formula contains no temporal operators.
fn extract_state_pred_ltl(formula: &LtlFormula) -> Option<StatePredicate> {
    match formula {
        LtlFormula::Atom(pred) => Some(pred.clone()),
        LtlFormula::Not(inner) => {
            extract_state_pred_ltl(inner).map(|p| StatePredicate::Not(Box::new(p)))
        }
        LtlFormula::And(children) => {
            let preds: Option<Vec<_>> = children.iter().map(extract_state_pred_ltl).collect();
            preds.map(StatePredicate::And)
        }
        LtlFormula::Or(children) => {
            let preds: Option<Vec<_>> = children.iter().map(extract_state_pred_ltl).collect();
            preds.map(StatePredicate::Or)
        }
        // Any temporal operator means not a pure state predicate.
        LtlFormula::Next(_)
        | LtlFormula::Finally(_)
        | LtlFormula::Globally(_)
        | LtlFormula::Until(_, _) => None,
    }
}

/// Build a `ReducedNet` that composes a query slice with the upstream
/// structural reduction: sliced-net indices map directly to original-net
/// indices, so `expand_marking_into` works in a single step.
fn compose_slice_and_reduction(slice: &QuerySlice, reduced: &ReducedNet) -> ReducedNet {
    let place_map = slice.compose_place_map(&reduced.place_map);
    let transition_map = slice.compose_transition_map(&reduced.transition_map);

    let place_unmap: Vec<PlaceIdx> = slice
        .place_unmap
        .iter()
        .map(|&reduced_idx| reduced.place_unmap[reduced_idx.0 as usize])
        .collect();
    let transition_unmap: Vec<TransitionIdx> = slice
        .transition_unmap
        .iter()
        .map(|&reduced_idx| reduced.transition_unmap[reduced_idx.0 as usize])
        .collect();

    ReducedNet {
        net: slice.net.clone(),
        place_map,
        place_unmap,
        place_scales: reduced.place_scales.clone(),
        transition_map,
        transition_unmap,
        constant_values: reduced.constant_values.clone(),
        reconstructions: reduced.reconstructions.clone(),
        report: ReductionReport::default(),
    }
}

/// Run LTL model checking for a set of properties.
///
/// Uses the on-the-fly product construction: system successors are computed
/// lazily by firing transitions on the reduced net, eliminating the need to
/// build and store the full system reachability graph.
///
/// Returns `(property_id, verdict)` for each property.
#[cfg(test)]
pub(crate) fn check_ltl_properties(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let aliases = PropertyAliases::identity(net);
    check_ltl_properties_inner(net, properties, &aliases, config, false)
}

pub(crate) fn check_ltl_properties_with_aliases(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    check_ltl_properties_inner(net, properties, aliases, config, false)
}

pub(crate) fn check_ltl_properties_with_flush(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    check_ltl_properties_inner(net, properties, aliases, config, true)
}

fn check_ltl_properties_inner(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
    flush: bool,
) -> Vec<(String, Verdict)> {
    // Simplify formulas using structural facts and LP proofs.
    let simplified =
        crate::formula_simplify::simplify_properties_with_aliases(net, properties, aliases);
    let properties = simplified.as_slice();
    let mut flushed_ids = HashSet::new();

    // ── Phase 0: classify shallow LTL properties ──
    let classifications: Vec<Option<ShallowLtl>> = properties
        .iter()
        .map(|prop| match &prop.formula {
            Formula::Ltl(ltl) => classify_shallow_ltl(ltl),
            _ => None,
        })
        .collect();

    // ── Phase 1: route G(atom) invariants through reachability as AG ──
    // Only definitive verdicts (True/False) short-circuit Buchi. CannotCompute
    // falls through so the Buchi path still gets a chance (#1370 design).
    let invariant_props: Vec<Property> = properties
        .iter()
        .zip(&classifications)
        .filter_map(|(prop, class)| match class {
            Some(ShallowLtl::Invariant(pred)) => Some(Property {
                id: prop.id.clone(),
                formula: Formula::Reachability(ReachabilityFormula {
                    quantifier: PathQuantifier::AG,
                    predicate: pred.clone(),
                }),
            }),
            _ => None,
        })
        .collect();

    let mut invariant_map: HashMap<String, Verdict> = if !invariant_props.is_empty() {
        check_reachability_properties_with_aliases(net, &invariant_props, aliases, config)
            .into_iter()
            .filter(|(_, v)| *v != Verdict::CannotCompute)
            .collect()
    } else {
        HashMap::new()
    };

    // Inject formulas that simplified to constant verdicts. The simplifier
    // may collapse e.g. G(trivially_true) → Atom(True), removing the temporal
    // wrapper that classify_shallow_ltl needs.
    for prop in properties {
        match &prop.formula {
            Formula::Ltl(LtlFormula::Atom(StatePredicate::True)) => {
                invariant_map.insert(prop.id.clone(), Verdict::True);
            }
            Formula::Ltl(LtlFormula::Atom(StatePredicate::False)) => {
                invariant_map.insert(prop.id.clone(), Verdict::False);
            }
            _ => {}
        }
    }

    // ── Phase 2: pre-filter F(atom) via batched reachability shortcuts ──
    // Batch 2a: AG(pred) for all eventual properties — quick TRUE shortcut.
    let eventually_ag_props: Vec<Property> = properties
        .iter()
        .zip(&classifications)
        .filter_map(|(prop, class)| match class {
            Some(ShallowLtl::Eventually(pred)) => Some(Property {
                id: prop.id.clone(),
                formula: Formula::Reachability(ReachabilityFormula {
                    quantifier: PathQuantifier::AG,
                    predicate: pred.clone(),
                }),
            }),
            _ => None,
        })
        .collect();

    let mut prefilter_map: HashMap<String, Verdict> = HashMap::new();
    if !eventually_ag_props.is_empty() {
        let ag_results =
            check_reachability_properties_with_aliases(net, &eventually_ag_props, aliases, config);
        for (id, verdict) in ag_results {
            if verdict == Verdict::True {
                prefilter_map.insert(id, Verdict::True);
            }
        }
    }

    // Batch 2b: EF(pred) for still-unresolved eventual properties — quick FALSE.
    let eventually_ef_props: Vec<Property> = properties
        .iter()
        .zip(&classifications)
        .filter_map(|(prop, class)| match class {
            Some(ShallowLtl::Eventually(pred)) if !prefilter_map.contains_key(&prop.id) => {
                Some(Property {
                    id: prop.id.clone(),
                    formula: Formula::Reachability(ReachabilityFormula {
                        quantifier: PathQuantifier::EF,
                        predicate: pred.clone(),
                    }),
                })
            }
            _ => None,
        })
        .collect();

    if !eventually_ef_props.is_empty() {
        let ef_results =
            check_reachability_properties_with_aliases(net, &eventually_ef_props, aliases, config);
        for (id, verdict) in ef_results {
            if verdict == Verdict::False {
                prefilter_map.insert(id, Verdict::False);
            }
        }
    }

    if flush {
        for prop in properties {
            if flushed_ids.contains(&prop.id) {
                continue;
            }
            let verdict = invariant_map
                .get(&prop.id)
                .or_else(|| prefilter_map.get(&prop.id));
            if let Some(verdict) = verdict {
                println!("FORMULA {} {} TECHNIQUES EXPLICIT", prop.id, verdict);
                flushed_ids.insert(prop.id.clone());
            }
        }
    }

    // ── Phase 3: Buchi pipeline for remaining (deep + unresolved) ──
    //
    // Query-aware reduction: StutterInsensitiveLTL mode applies
    // dead/constant/isolated/source/parallel/LP-redundant/duplicate/dominated
    // reductions but NOT agglomeration (which changes path structure).
    //
    // Agglomeration is the rule that was unsound in the historical temporal
    // lane — it merges transitions, altering which paths exist. All other
    // rules either remove unreachable structure (dead transitions, isolated
    // places) or remove observationally equivalent structure (parallel
    // places, LP-redundant places whose marking is reconstructable).
    //
    // Query slicing is still applied on top (safe: removes only disconnected
    // structure from the COI perspective).
    let ltl_mode = ReductionMode::StutterInsensitiveLTL;
    let reduced = match reduce_iterative_structural_with_mode(net, &[], ltl_mode) {
        Ok(r) => {
            let removed = r.report.places_removed() + r.report.transitions_removed();
            if removed > 0 {
                eprintln!(
                    "LTL {mode:?} reduction: removed {removed} elements \
                     ({p} places, {t} transitions)",
                    mode = ltl_mode,
                    p = r.report.places_removed(),
                    t = r.report.transitions_removed(),
                );
            }
            r
        }
        Err(error) => {
            eprintln!("LTL reduction error: {error} — falling back to identity");
            ReducedNet::identity(net)
        }
    };

    let unresolved_indices: Vec<usize> = properties
        .iter()
        .enumerate()
        .filter_map(|(index, prop)| {
            (!invariant_map.contains_key(&prop.id) && !prefilter_map.contains_key(&prop.id))
                .then_some(index)
        })
        .collect();

    let mut buchi_map: HashMap<String, Verdict> = HashMap::new();
    for (position, &index) in unresolved_indices.iter().enumerate() {
        let prop = &properties[index];
        let remaining_count = unresolved_indices.len() - position;
        let buchi_config = config
            .clone()
            .with_deadline(fair_share_deadline(config.deadline(), remaining_count));
        let verdict = match &prop.formula {
            Formula::Ltl(ltl) => {
                check_single_ltl_buchi(prop, ltl, net, &reduced, aliases, &buchi_config)
            }
            _ => Verdict::CannotCompute,
        };
        buchi_map.insert(prop.id.clone(), verdict);
    }

    // ── Phase 4: merge all results preserving original property order ──
    properties
        .iter()
        .filter_map(|prop| {
            if flushed_ids.contains(&prop.id) {
                return None;
            }
            let verdict = invariant_map
                .get(&prop.id)
                .or_else(|| prefilter_map.get(&prop.id))
                .or_else(|| buchi_map.get(&prop.id))
                .cloned()
                .unwrap_or(Verdict::CannotCompute);
            Some((prop.id.clone(), verdict))
        })
        .collect()
}

fn fair_share_budget(remaining: Duration, remaining_count: usize) -> Duration {
    let divisor = remaining_count.clamp(1, u32::MAX as usize) as u32;
    remaining / divisor
}

fn fair_share_deadline(
    global_deadline: Option<Instant>,
    remaining_count: usize,
) -> Option<Instant> {
    global_deadline.map(|deadline| {
        let now = Instant::now();
        now + fair_share_budget(deadline.saturating_duration_since(now), remaining_count)
    })
}

/// Run the Buchi product pipeline for a single LTL property.
fn check_single_ltl_buchi(
    prop: &Property,
    ltl: &LtlFormula,
    net: &PetriNet,
    reduced: &ReducedNet,
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Verdict {
    // Safety: detect formulas with unresolved names.
    let (total, unresolved) = count_unresolved_ltl(ltl, aliases);
    if unresolved > 0 {
        eprintln!(
            "LTL resolution guard: {} has {unresolved}/{total} \
             unresolved names → CANNOT_COMPUTE",
            prop.id
        );
        return Verdict::CannotCompute;
    }

    // Convert LTL formula to NNF early so we can gate on X.
    let mut atom_preds = Vec::new();
    let nnf = to_nnf(ltl, &mut atom_preds);
    let has_next = formula_contains_next(&nnf);

    // Per-property query slicing on the reduced net.
    let slice = ltl_property_support_with_aliases(reduced, prop, aliases).and_then(|support| {
        if has_next {
            let closure = closure_on_reduced_net(&reduced.net, support);
            build_query_slice(&reduced.net, &closure)
        } else {
            let cone = relevance_cone_on_reduced_net(&reduced.net, support);
            build_query_local_slice(&reduced.net, &cone)
        }
    });

    // When a slice was produced, build a composed ReducedNet.
    let composed;
    let (explore_net, explore_reduced): (&PetriNet, &ReducedNet) = if let Some(ref s) = slice {
        composed = compose_slice_and_reduction(s, reduced);
        (&s.net, &composed)
    } else {
        (&reduced.net, reduced)
    };

    // Resolve atoms to indices on the original net.
    let resolved_atoms: Vec<_> = atom_preds
        .iter()
        .map(|pred| crate::buchi::resolve_atom_with_aliases(pred, aliases))
        .collect();

    // POR: use stubborn sets if the formula is stutter-insensitive.
    let por = if !has_next {
        let visible = ltl_visible_reduced_transitions(&resolved_atoms, explore_reduced);
        if visible.len() < explore_net.num_transitions() {
            Some(PorContext {
                dep: DependencyGraph::build(explore_net),
                visible,
            })
        } else {
            None
        }
    } else {
        None
    };

    // On-the-fly Buchi product.
    match check_ltl_on_the_fly(
        &nnf,
        explore_net,
        explore_reduced,
        net,
        &resolved_atoms,
        por.as_ref(),
        config.max_states(),
        config.deadline(),
    ) {
        Ok(Some(true)) => Verdict::True,
        Ok(Some(false)) => Verdict::False,
        Ok(None) => Verdict::CannotCompute,
        Err(error) => {
            eprintln!("LTL: {} → CANNOT_COMPUTE ({error})", prop.id);
            Verdict::CannotCompute
        }
    }
}

#[cfg(test)]
#[path = "ltl_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "ltl_query_slicing_tests.rs"]
mod query_slicing_tests;
