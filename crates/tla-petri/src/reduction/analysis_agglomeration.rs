// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, TransitionIdx};

use super::model::{PostAgglomeration, PreAgglomeration, RuleRAgglomeration, RuleSAgglomeration};

/// Per-place connectivity: which transitions produce into / consume from each place.
pub(in crate::reduction) struct PlaceConnectivity {
    /// For each place: transitions that produce tokens into it (place's pre-set).
    pub(in crate::reduction) producers: Vec<Vec<(TransitionIdx, u64)>>,
    /// For each place: transitions that consume tokens from it (place's post-set).
    pub(in crate::reduction) consumers: Vec<Vec<(TransitionIdx, u64)>>,
}

/// Build per-place connectivity, ignoring dead transitions.
pub(in crate::reduction) fn build_place_connectivity(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> PlaceConnectivity {
    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut producers = vec![Vec::new(); num_places];
    let mut consumers = vec![Vec::new(); num_places];

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        let t_idx = TransitionIdx(tidx as u32);
        for arc in &t.outputs {
            producers[arc.place.0 as usize].push((t_idx, arc.weight));
        }
        for arc in &t.inputs {
            consumers[arc.place.0 as usize].push((t_idx, arc.weight));
        }
    }

    PlaceConnectivity {
        producers,
        consumers,
    }
}

/// Find all agglomeration candidates and resolve conflicts.
///
/// Wraps the 3-step sequence: build connectivity, find pre/post candidates,
/// then resolve conflicts (pre-agglomerations get priority).
pub(super) fn find_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> (Vec<PreAgglomeration>, Vec<PostAgglomeration>) {
    let connectivity = build_place_connectivity(net, dead_transitions);
    let pre_candidates = find_pre_agglomerations(net, dead_transitions, &connectivity);
    let post_candidates = find_post_agglomerations(net, dead_transitions, &connectivity);
    resolve_agglomeration_conflicts(pre_candidates, post_candidates)
}

/// Find pre-agglomeration candidates (Berthelot 1987).
///
/// A transition `t` is pre-agglomeratable when:
/// 1. `t` has exactly one output place `p` with arc weight 1
/// 2. `p` has exactly one producer (which is `t`)
/// 3. `p` has zero initial tokens
/// 4. Every consumer of `p` reads exactly one token
/// 5. `t` is not in its own successor set (no self-loop through `p`)
/// 6. Source inputs ∩ successor outputs = ∅ (Berthelot condition 6:
///    prevents creating false self-loops when merged)
fn find_pre_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
) -> Vec<PreAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        // Condition 1: exactly one output place, weight 1.
        if t.outputs.len() != 1 || t.outputs[0].weight != 1 {
            continue;
        }
        let p = t.outputs[0].place;
        let p_idx = p.0 as usize;

        // Condition 2: p has exactly one producer.
        if conn.producers[p_idx].len() != 1 {
            continue;
        }

        // Condition 3: zero initial tokens.
        if net.initial_marking[p_idx] != 0 {
            continue;
        }

        // Condition 4: every consumer reads exactly 1 token.
        if conn.consumers[p_idx].iter().any(|&(_, w)| w != 1) {
            continue;
        }

        let successors: Vec<TransitionIdx> = conn.consumers[p_idx]
            .iter()
            .map(|&(t_idx, _)| t_idx)
            .collect();

        if successors.is_empty() {
            continue;
        }

        // Condition 5: no self-loop through p.
        let t_idx = TransitionIdx(tidx as u32);
        if successors.contains(&t_idx) {
            continue;
        }

        // Condition 6 (Berthelot): source inputs must not overlap with
        // any successor's outputs. Prevents creating self-loops that
        // hide intermediate markings (e.g., mutex cycle).
        let source_inputs: HashSet<u32> = t.inputs.iter().map(|a| a.place.0).collect();
        let overlap = successors.iter().any(|&TransitionIdx(si)| {
            let succ = &net.transitions[si as usize];
            succ.outputs
                .iter()
                .any(|a| source_inputs.contains(&a.place.0))
        });
        if overlap {
            continue;
        }

        results.push(PreAgglomeration {
            transition: t_idx,
            place: p,
            successors,
        });
    }

    results
}

/// Find post-agglomeration candidates (dual of pre-agglomeration).
///
/// A transition `t` is post-agglomeratable when:
/// 1. `t` has exactly one input place `p` with arc weight 1
/// 2. `p` has exactly one consumer (which is `t`)
/// 3. `p` has zero initial tokens
/// 4. Every producer of `p` produces exactly one token
/// 5. `t` is not in its own predecessor set (no self-loop through `p`)
/// 6. Sink outputs ∩ predecessor inputs = ∅ (dual of Berthelot condition 6)
fn find_post_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
) -> Vec<PostAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        // Condition 1: exactly one input place, weight 1.
        if t.inputs.len() != 1 || t.inputs[0].weight != 1 {
            continue;
        }
        let p = t.inputs[0].place;
        let p_idx = p.0 as usize;

        // Condition 2: p has exactly one consumer.
        if conn.consumers[p_idx].len() != 1 {
            continue;
        }

        // Condition 3: zero initial tokens.
        if net.initial_marking[p_idx] != 0 {
            continue;
        }

        // Condition 4: every producer produces exactly 1 token.
        if conn.producers[p_idx].iter().any(|&(_, w)| w != 1) {
            continue;
        }

        let predecessors: Vec<TransitionIdx> = conn.producers[p_idx]
            .iter()
            .map(|&(t_idx, _)| t_idx)
            .collect();

        if predecessors.is_empty() {
            continue;
        }

        // Condition 5: no self-loop through p.
        let t_idx = TransitionIdx(tidx as u32);
        if predecessors.contains(&t_idx) {
            continue;
        }

        // Condition 6 (Berthelot dual): sink outputs must not overlap
        // with any predecessor's inputs. Prevents false self-loops.
        let sink_outputs: HashSet<u32> = t.outputs.iter().map(|a| a.place.0).collect();
        let overlap = predecessors.iter().any(|&TransitionIdx(pi)| {
            let pred = &net.transitions[pi as usize];
            pred.inputs
                .iter()
                .any(|a| sink_outputs.contains(&a.place.0))
        });
        if overlap {
            continue;
        }

        results.push(PostAgglomeration {
            transition: t_idx,
            place: p,
            predecessors,
        });
    }

    results
}

/// Resolve conflicts between agglomeration candidates.
///
/// A transition cannot be both removed (as source/sink) and modified
/// (as successor/predecessor) in the same pass. A place can only appear
/// in one agglomeration. Pre-agglomerations get priority.
fn resolve_agglomeration_conflicts(
    pre: Vec<PreAgglomeration>,
    post: Vec<PostAgglomeration>,
) -> (Vec<PreAgglomeration>, Vec<PostAgglomeration>) {
    use std::collections::HashSet;

    let mut used_places: HashSet<u32> = HashSet::new();
    let mut removed_transitions: HashSet<u32> = HashSet::new();
    // Transitions that receive extra arcs from agglomeration and must NOT
    // be removed by a subsequent agglomeration in the same pass. Without
    // this guard, chained pre-agglomerations (e.g., r0→r1→r2→r3) lose
    // intermediate arcs: the successor of the first agglomeration becomes
    // the source of the second, so its extra inputs are never applied.
    let mut receiving_transitions: HashSet<u32> = HashSet::new();

    let mut selected_pre = Vec::new();
    for agg in pre {
        if used_places.contains(&agg.place.0) {
            continue;
        }
        if removed_transitions.contains(&agg.transition.0) {
            continue;
        }
        // Source must not be a receiving transition from a prior agglomeration.
        if receiving_transitions.contains(&agg.transition.0) {
            continue;
        }
        if agg
            .successors
            .iter()
            .any(|s| removed_transitions.contains(&s.0))
        {
            continue;
        }

        used_places.insert(agg.place.0);
        removed_transitions.insert(agg.transition.0);
        for s in &agg.successors {
            receiving_transitions.insert(s.0);
        }
        selected_pre.push(agg);
    }

    let mut selected_post = Vec::new();
    for agg in post {
        if used_places.contains(&agg.place.0) {
            continue;
        }
        if removed_transitions.contains(&agg.transition.0) {
            continue;
        }
        // Sink must not be a receiving transition from a prior agglomeration.
        if receiving_transitions.contains(&agg.transition.0) {
            continue;
        }
        if agg
            .predecessors
            .iter()
            .any(|p| removed_transitions.contains(&p.0))
        {
            continue;
        }

        used_places.insert(agg.place.0);
        removed_transitions.insert(agg.transition.0);
        for p in &agg.predecessors {
            receiving_transitions.insert(p.0);
        }
        selected_post.push(agg);
    }

    (selected_pre, selected_post)
}

/// Find Tapaal Rule R candidates: post-agglomeration with multi-consumer fan-out.
///
/// A place `p` admits Rule R fusion when:
/// 1. `p` has at least one producer and one consumer (all live).
/// 2. No transition is both a producer and a consumer of `p` (disjoint sets —
///    avoids self-loop synthesis).
/// 3. Every consumer of `p` has pre-set exactly `{p}` (i.e. the consumer reads
///    only from `p`; Tapaal `Reducer.cpp:2421-2428`).
/// 4. No consumer's post-set writes into a query-protected place (we must not
///    fuse away visibility of a protected place).
/// 5. The fan-out product `|fuseable_producers| * |consumers| <=
///    RULE_R_EXPLOSION_LIMITER` (Tapaal `Reducer.cpp:2845` constant, 6).
///
/// A producer is **fuseable** in Phase-1 when its arc weight on `p` equals the
/// maximum consumer arc weight on `p` (no residual tokens left behind).
///
/// If every producer is fuseable AND `initial_marking[p] == 0`, `remove_place`
/// is set: the place and all consumers are removed too.
pub(in crate::reduction) fn find_rule_r_agglomerations(
    net: &PetriNet,
    protected_places: &[bool],
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
    limiter: u32,
) -> Vec<RuleRAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();
    let num_places = net.num_places();

    for p_idx in 0..num_places {
        let producers = &conn.producers[p_idx];
        let consumers = &conn.consumers[p_idx];

        if producers.is_empty() || consumers.is_empty() {
            continue;
        }

        // Condition 2: producer/consumer sets must be disjoint.
        let producer_set: HashSet<u32> =
            producers.iter().map(|&(t, _)| t.0).collect();
        let consumer_set: HashSet<u32> =
            consumers.iter().map(|&(t, _)| t.0).collect();
        if producer_set.intersection(&consumer_set).next().is_some() {
            continue;
        }

        // Condition 3 + 4: consumer pre-set exactly {p}, post-set not touching protected.
        let mut consumers_ok = true;
        let mut max_consumer_weight: u64 = 0;
        for &(TransitionIdx(ci), cw) in consumers {
            let ct = &net.transitions[ci as usize];
            // Pre-set exactly {p}: exactly one input arc, and it's on p.
            if ct.inputs.len() != 1 {
                consumers_ok = false;
                break;
            }
            let only_in = &ct.inputs[0];
            if only_in.place.0 as usize != p_idx {
                consumers_ok = false;
                break;
            }
            // Consumer post-set must not write into protected place.
            for out_arc in &ct.outputs {
                if protected_places[out_arc.place.0 as usize] {
                    consumers_ok = false;
                    break;
                }
            }
            if !consumers_ok {
                break;
            }
            if cw > max_consumer_weight {
                max_consumer_weight = cw;
            }
        }
        if !consumers_ok {
            continue;
        }
        if max_consumer_weight == 0 {
            continue;
        }

        // Phase-1 fuseable partition: arc weight exactly equals max_consumer_weight.
        let mut fuseable_producers: Vec<(TransitionIdx, u64)> = Vec::new();
        let mut residual = false;
        for &(tidx, w) in producers {
            if is_dead[tidx.0 as usize] {
                continue;
            }
            if w == max_consumer_weight {
                fuseable_producers.push((tidx, w));
            } else {
                residual = true;
            }
        }
        if fuseable_producers.is_empty() {
            continue;
        }

        // Condition 5: explosion limiter.
        let prod_n = fuseable_producers.len() as u64;
        let cons_n = consumers.len() as u64;
        if prod_n
            .checked_mul(cons_n)
            .is_none_or(|prod| prod > u64::from(limiter))
        {
            continue;
        }

        let consumer_list: Vec<TransitionIdx> =
            consumers.iter().map(|&(t, _)| t).collect();

        let remove_place = !residual && net.initial_marking[p_idx] == 0;

        // Protected places: cannot be removed even if fully fuseable.
        let remove_place = remove_place && !protected_places[p_idx];

        results.push(RuleRAgglomeration {
            place: crate::petri_net::PlaceIdx(p_idx as u32),
            max_consumer_weight,
            fuseable_producers,
            consumers: consumer_list,
            remove_place,
        });
    }

    results
}

/// Resolve Rule R conflicts with pre/post-agglomerations *and* a set of
/// already-selected Rule S agglomerations. Rule R must avoid any place or
/// transition claimed by Rule S.
pub(in crate::reduction) fn resolve_rule_r_conflicts_with_rule_s(
    candidates: Vec<RuleRAgglomeration>,
    pre: &[PreAgglomeration],
    post: &[PostAgglomeration],
    rule_s: &[RuleSAgglomeration],
) -> Vec<RuleRAgglomeration> {
    use std::collections::HashSet;

    let mut claimed_places: HashSet<u32> = HashSet::new();
    let mut claimed_transitions: HashSet<u32> = HashSet::new();

    for agg in pre {
        claimed_places.insert(agg.place.0);
        claimed_transitions.insert(agg.transition.0);
        for s in &agg.successors {
            claimed_transitions.insert(s.0);
        }
    }
    for agg in post {
        claimed_places.insert(agg.place.0);
        claimed_transitions.insert(agg.transition.0);
        for p in &agg.predecessors {
            claimed_transitions.insert(p.0);
        }
    }
    for agg in rule_s {
        claimed_places.insert(agg.place.0);
        for t in &agg.producers {
            claimed_transitions.insert(t.0);
        }
        for t in &agg.consumers {
            claimed_transitions.insert(t.0);
        }
    }

    let mut selected = Vec::new();
    for agg in candidates {
        if claimed_places.contains(&agg.place.0) {
            continue;
        }
        let prod_clash = agg
            .fuseable_producers
            .iter()
            .any(|(t, _)| claimed_transitions.contains(&t.0));
        if prod_clash {
            continue;
        }
        let cons_clash = agg
            .consumers
            .iter()
            .any(|t| claimed_transitions.contains(&t.0));
        if cons_clash {
            continue;
        }

        claimed_places.insert(agg.place.0);
        for (t, _) in &agg.fuseable_producers {
            claimed_transitions.insert(t.0);
        }
        for t in &agg.consumers {
            claimed_transitions.insert(t.0);
        }
        selected.push(agg);
    }

    selected
}

/// Find Tapaal Rule S candidates: generalized place-centric producer × consumer
/// agglomeration (`Reducer.cpp:2556-2838`). Phase-1 atomic-viable sub-case only.
///
/// A place `p` admits Rule S fusion (Phase-1) when:
/// 1. `p` has at least one producer and one consumer (all live).
/// 2. Producer/consumer sets are disjoint (S4/T4; avoids self-loop synthesis).
/// 3. Every producer has post-set exactly `{p}` (Tapaal S8/S6 `postsetSize==1`
///    at `Reducer.cpp:2650`).
/// 4. Every consumer has pre-set exactly `{p}` (Tapaal S10 k==1 simplification,
///    `Reducer.cpp:2710`).
/// 5. There is a single uniform arc weight `w` such that every consumer's
///    in-weight on `p` equals `w` AND every producer's out-weight on `p`
///    equals `w` (Phase-1 k==1 scope).
/// 6. `initial_marking[p] < w` (Tapaal S3/S9: no consumer can fire initially
///    without a producer firing first).
/// 7. `p` is not query-protected.
/// 8. No producer's pre-place and no consumer's post-place is query-protected
///    (fused transition preserves visibility of protected places elsewhere).
/// 9. `producers.len() * consumers.len() <= limiter` (shared with Rule R).
///
/// Unlike Rule R, Rule S ALWAYS removes every producer, every consumer, and
/// `p` itself — the initial marking bound in (6) guarantees the fused
/// transitions reproduce every consumer firing in the original net.
pub(in crate::reduction) fn find_rule_s_agglomerations(
    net: &PetriNet,
    protected_places: &[bool],
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
    limiter: u32,
) -> Vec<RuleSAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();
    let num_places = net.num_places();

    for p_idx in 0..num_places {
        // Condition 7: `p` itself must not be query-protected.
        if protected_places[p_idx] {
            continue;
        }

        let producers = &conn.producers[p_idx];
        let consumers = &conn.consumers[p_idx];

        // Condition 1: at least one producer and one consumer.
        if producers.is_empty() || consumers.is_empty() {
            continue;
        }

        // Condition 2: disjoint producer/consumer sets.
        let producer_set: HashSet<u32> = producers.iter().map(|&(t, _)| t.0).collect();
        let consumer_set: HashSet<u32> = consumers.iter().map(|&(t, _)| t.0).collect();
        if producer_set.intersection(&consumer_set).next().is_some() {
            continue;
        }

        // Condition 5 (part 1): derive uniform consumer weight `w`.
        let Some(&(_, w)) = consumers.first() else {
            continue;
        };
        if w == 0 {
            continue;
        }

        // Condition 6: initial_marking[p] < w.
        if net.initial_marking[p_idx] >= w {
            continue;
        }

        // Condition 4 + 8 (consumer side): pre-set exactly {p} with weight w,
        // post-set not touching protected places.
        let mut consumers_ok = true;
        for &(TransitionIdx(ci), cw) in consumers {
            if is_dead[ci as usize] {
                consumers_ok = false;
                break;
            }
            if cw != w {
                consumers_ok = false;
                break;
            }
            let ct = &net.transitions[ci as usize];
            // Pre-set exactly {p}: exactly one input arc, on p, weight w.
            if ct.inputs.len() != 1 {
                consumers_ok = false;
                break;
            }
            let only_in = &ct.inputs[0];
            if only_in.place.0 as usize != p_idx || only_in.weight != w {
                consumers_ok = false;
                break;
            }
            // Consumer post-set must not write into protected place.
            if ct
                .outputs
                .iter()
                .any(|arc| protected_places[arc.place.0 as usize])
            {
                consumers_ok = false;
                break;
            }
        }
        if !consumers_ok {
            continue;
        }

        // Condition 3 + 5 (producer side) + 8 (producer pre-places): post-set
        // exactly {p} with weight w, pre-places not protected.
        let mut producers_ok = true;
        for &(TransitionIdx(pi), pw) in producers {
            if is_dead[pi as usize] {
                producers_ok = false;
                break;
            }
            if pw != w {
                producers_ok = false;
                break;
            }
            let pt = &net.transitions[pi as usize];
            // Post-set exactly {p}: exactly one output arc, on p, weight w.
            if pt.outputs.len() != 1 {
                producers_ok = false;
                break;
            }
            let only_out = &pt.outputs[0];
            if only_out.place.0 as usize != p_idx || only_out.weight != w {
                producers_ok = false;
                break;
            }
            // Producer pre-set must not read from protected place.
            if pt
                .inputs
                .iter()
                .any(|arc| protected_places[arc.place.0 as usize])
            {
                producers_ok = false;
                break;
            }
        }
        if !producers_ok {
            continue;
        }

        // Condition 9: explosion limiter.
        let prod_n = producers.len() as u64;
        let cons_n = consumers.len() as u64;
        if prod_n
            .checked_mul(cons_n)
            .is_none_or(|prod| prod > u64::from(limiter))
        {
            continue;
        }

        let producer_list: Vec<TransitionIdx> = producers.iter().map(|&(t, _)| t).collect();
        let consumer_list: Vec<TransitionIdx> = consumers.iter().map(|&(t, _)| t).collect();

        results.push(RuleSAgglomeration {
            place: crate::petri_net::PlaceIdx(p_idx as u32),
            weight: w,
            producers: producer_list,
            consumers: consumer_list,
        });
    }

    results
}

/// Resolve conflicts between Rule S candidates and pre/post-agglomerations.
///
/// Rule S runs BEFORE Rule R (Tapaal `Reducer.cpp:2893-2896`). In a single
/// planner pass we accept pre/post agglomerations first, then Rule S, then
/// Rule R — so Rule S must avoid pre/post already claimed places/transitions.
/// Rule R's resolver consumes Rule S's selections too (handled by its caller
/// threading both sets into a combined claimed-set).
pub(in crate::reduction) fn resolve_rule_s_conflicts(
    candidates: Vec<RuleSAgglomeration>,
    pre: &[PreAgglomeration],
    post: &[PostAgglomeration],
) -> Vec<RuleSAgglomeration> {
    use std::collections::HashSet;

    let mut claimed_places: HashSet<u32> = HashSet::new();
    let mut claimed_transitions: HashSet<u32> = HashSet::new();

    for agg in pre {
        claimed_places.insert(agg.place.0);
        claimed_transitions.insert(agg.transition.0);
        for s in &agg.successors {
            claimed_transitions.insert(s.0);
        }
    }
    for agg in post {
        claimed_places.insert(agg.place.0);
        claimed_transitions.insert(agg.transition.0);
        for p in &agg.predecessors {
            claimed_transitions.insert(p.0);
        }
    }

    let mut selected = Vec::new();
    for agg in candidates {
        if claimed_places.contains(&agg.place.0) {
            continue;
        }
        let prod_clash = agg
            .producers
            .iter()
            .any(|t| claimed_transitions.contains(&t.0));
        if prod_clash {
            continue;
        }
        let cons_clash = agg
            .consumers
            .iter()
            .any(|t| claimed_transitions.contains(&t.0));
        if cons_clash {
            continue;
        }

        claimed_places.insert(agg.place.0);
        for t in &agg.producers {
            claimed_transitions.insert(t.0);
        }
        for t in &agg.consumers {
            claimed_transitions.insert(t.0);
        }
        selected.push(agg);
    }

    selected
}
