// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    apply_closure_with_values, check_arity, eval, eval_iter_set, select_clock_component,
    vc_happened_before, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
// VectorClocks module operators — IsCausalOrder, CausalOrder

pub(super) fn eval_builtin_vector_clocks(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === VectorClocks module (CommunityModules) ===
        // For trace export and causal ordering analysis

        // IsCausalOrder(log, clock) - check if log respects causal ordering
        "IsCausalOrder" => {
            check_arity(name, args, 2, span)?;
            let log = eval(ctx, &args[0])?;
            let clock_op = eval(ctx, &args[1])?;
            let clock_closure = clock_op
                .as_closure()
                .ok_or_else(|| EvalError::type_error("Closure", &clock_op, span))?;
            let elements = log
                .as_seq_or_tuple_elements()
                .ok_or_else(|| EvalError::type_error("Sequence", &log, span))?;
            // For every pair (i < j), check that vc_j does NOT strictly
            // happened-before vc_i (which would mean j should precede i).
            for i in 0..elements.len() {
                let vc_i = apply_closure_with_values(
                    ctx,
                    clock_closure,
                    std::slice::from_ref(&elements[i]),
                    span,
                )?;
                for j in (i + 1)..elements.len() {
                    let vc_j = apply_closure_with_values(
                        ctx,
                        clock_closure,
                        std::slice::from_ref(&elements[j]),
                        span,
                    )?;
                    if vc_happened_before(&vc_j, &vc_i) {
                        return Ok(Some(Value::Bool(false)));
                    }
                }
            }
            Ok(Some(Value::Bool(true)))
        }

        // CausalOrder(log, clock, node, domain) - sort log by vector clock
        // Follows TLC's CommunityModules VectorClocks.java:
        // Phase A: Group by node, sort per-node by own clock value
        // Phase B: Build causal DAG
        // Phase C: Topological sort
        "CausalOrder" => {
            check_arity(name, args, 4, span)?;
            let log = eval(ctx, &args[0])?;
            let clock_op = eval(ctx, &args[1])?;
            let node_op = eval(ctx, &args[2])?;
            let domain_op = eval(ctx, &args[3])?;

            let clock_closure = clock_op
                .as_closure()
                .ok_or_else(|| EvalError::type_error("Closure", &clock_op, span))?;
            let node_closure = node_op
                .as_closure()
                .ok_or_else(|| EvalError::type_error("Closure", &node_op, span))?;
            let domain_closure = domain_op
                .as_closure()
                .ok_or_else(|| EvalError::type_error("Closure", &domain_op, span))?;

            let elements = log
                .as_seq_or_tuple_elements()
                .ok_or_else(|| EvalError::type_error("Sequence", &log, span))?;

            if elements.is_empty() {
                return Ok(Some(Value::tuple(Vec::new())));
            }

            // TLC-parity implementation of VectorClocks.causalOrder:
            // 1. Group events by host and sort each host list by own clock component.
            // 2. Build parent edges with a per-host global clock frontier.
            // 3. Repeatedly scan host heads and remove parent-free nodes.
            let mut node_values: Vec<Value> = Vec::with_capacity(elements.len());
            let mut node_clocks: Vec<Value> = Vec::with_capacity(elements.len());
            let mut node_domains: Vec<Vec<Value>> = Vec::with_capacity(elements.len());
            let mut node_times: Vec<Value> = Vec::with_capacity(elements.len());
            #[allow(clippy::mutable_key_type)]
            // Value's Ord is deterministic despite interior AtomicU64
            let mut per_host: std::collections::BTreeMap<Value, Vec<usize>> =
                std::collections::BTreeMap::new();

            for entry in elements.iter() {
                let host = apply_closure_with_values(
                    ctx,
                    node_closure,
                    std::slice::from_ref(entry),
                    span,
                )?;
                let clock = apply_closure_with_values(
                    ctx,
                    clock_closure,
                    std::slice::from_ref(entry),
                    span,
                )?;
                let time = select_clock_component(&clock, &host, span)?;
                let domain = apply_closure_with_values(
                    ctx,
                    domain_closure,
                    std::slice::from_ref(&clock),
                    span,
                )?;
                // Part of #1828: use eval_iter_set for SetPred-aware iteration.
                let domain_values: Vec<Value> = eval_iter_set(ctx, &domain, span)?.collect();

                let idx = node_values.len();
                node_values.push(entry.clone());
                node_clocks.push(clock);
                node_domains.push(domain_values);
                node_times.push(time);
                per_host.entry(host).or_default().push(idx);
            }

            for indices in per_host.values_mut() {
                indices.sort_by(|a, b| node_times[*a].cmp(&node_times[*b]));
            }

            let mut parents: Vec<std::collections::BTreeSet<usize>> =
                vec![std::collections::BTreeSet::new(); node_values.len()];
            let mut children: Vec<std::collections::BTreeSet<usize>> =
                vec![std::collections::BTreeSet::new(); node_values.len()];
            let host_keys: Vec<Value> = per_host.keys().cloned().collect();

            for host in &host_keys {
                let indices = per_host.get(host).cloned().unwrap_or_default();
                #[allow(clippy::mutable_key_type)]
                let mut global_clock: std::collections::BTreeMap<Value, Value> = host_keys
                    .iter()
                    .cloned()
                    .map(|h| (h, Value::int(0)))
                    .collect();

                for idx in indices {
                    global_clock.insert(host.clone(), node_times[idx].clone());

                    for dep_host in &node_domains[idx] {
                        let event_time = select_clock_component(&node_clocks[idx], dep_host, span)?;
                        let last_seen = global_clock
                            .get(dep_host)
                            .cloned()
                            .unwrap_or_else(|| Value::int(0));

                        if last_seen < event_time {
                            global_clock.insert(dep_host.clone(), event_time.clone());

                            let parent_local = event_time
                                .as_i64()
                                .ok_or_else(|| EvalError::type_error("Int", &event_time, span))?
                                - 1;

                            if parent_local < 0 {
                                return Err(EvalError::Internal {
                                    message: format!(
                                        "CausalOrder: invalid vector clock component {event_time} for host {dep_host}"
                                    ),
                                    span,
                                });
                            }

                            let parent_indices = per_host.get(dep_host).ok_or_else(|| {
                                EvalError::Internal {
                                    message: format!(
                                        "CausalOrder: dependency host {dep_host} not found in grouped events"
                                    ),
                                    span,
                                }
                            })?;
                            let parent_idx = *parent_indices.get(parent_local as usize).ok_or_else(
                                || EvalError::Internal {
                                    message: format!(
                                        "CausalOrder: dependency index {} out of bounds for host {} ({} events)",
                                        parent_local + 1,
                                        dep_host,
                                        parent_indices.len()
                                    ),
                                    span,
                                },
                            )?;

                            if parents[idx].insert(parent_idx) {
                                children[parent_idx].insert(idx);
                            }
                        }
                    }
                }
            }

            #[allow(clippy::mutable_key_type)]
            let mut per_host_queue: std::collections::BTreeMap<
                Value,
                std::collections::VecDeque<usize>,
            > = per_host
                .into_iter()
                .map(|(host, indices)| (host, std::collections::VecDeque::from(indices)))
                .collect();

            let mut sorted: Vec<Value> = Vec::with_capacity(node_values.len());
            for _ in 0..node_values.len() {
                let hosts: Vec<Value> = per_host_queue.keys().cloned().collect();
                for host in hosts {
                    let head = per_host_queue
                        .get(&host)
                        .and_then(|queue| queue.front().copied());
                    let Some(idx) = head else {
                        continue;
                    };

                    if parents[idx].is_empty() {
                        if let Some(queue) = per_host_queue.get_mut(&host) {
                            queue.pop_front();
                        }
                        sorted.push(node_values[idx].clone());
                        let child_list: Vec<usize> = children[idx].iter().copied().collect();
                        for child in child_list {
                            parents[child].remove(&idx);
                        }
                    }
                }
            }

            if sorted.len() != node_values.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "CausalOrder: failed to produce full order (ordered {} of {})",
                        sorted.len(),
                        node_values.len()
                    ),
                    span,
                });
            }

            Ok(Some(Value::tuple(sorted)))
        }

        _ => Ok(None),
    }
}
