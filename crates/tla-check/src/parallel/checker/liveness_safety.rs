// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Safety-temporal fast path for the parallel checker's post-BFS liveness.
//!
//! Part of #2892: For `[]P` properties where P is non-temporal, checks by
//! iterating the state graph directly (O(|V|) or O(|E|)) instead of building
//! the expensive Tableau + behavior graph + SCC cross-product.

use super::liveness::LivenessGraphData;
use super::ParallelChecker;

use crate::check::{check_error_to_result, CheckResult, CheckStats, Trace};
use crate::checker_ops::eval_property_bool_term;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, Fingerprint, State};
use rustc_hash::FxHashMap;
use tla_core::ast::Expr;
use tla_core::Spanned;

impl ParallelChecker {
    /// Safety-temporal fast path: check decomposed terms on the state graph.
    ///
    /// Part of #2892: Parity with sequential checker's `check_safety_temporal_property`.
    /// Checks init terms on initial states, `[]P` on all states, `[]A` on all transitions.
    /// Returns `Some(CheckResult)` on violation, `None` if all terms satisfied.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_safety_temporal_terms(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        graph: &LivenessGraphData,
        prop_name: &str,
        init_terms: &[Spanned<Expr>],
        always_state_terms: &[Spanned<Expr>],
        always_action_terms: &[Spanned<Expr>],
    ) -> Option<CheckResult> {
        // Check init terms on initial states.
        // Part of #2661: Array-backed binding from liveness_init_states DashMap.
        // Parity with sequential safety_temporal.rs:131-187.
        for entry in self.liveness_init_states.iter() {
            let _init_fp = *entry.key();
            let init_array = entry.value();
            let _scope_guard = ctx.scope_guard_with_next_state();
            *ctx.next_state_mut() = None;
            let _next_env_guard = ctx.take_next_state_env_guard();
            let _state_guard = ctx.bind_state_env_guard(init_array.env_ref());
            // Part of #3465: Use array-bound eval boundary helper.
            crate::eval::clear_for_bound_state_eval_scope(ctx);

            for term in init_terms {
                match eval_property_bool_term(ctx, prop_name, term) {
                    Ok(true) => {}
                    Ok(false) => {
                        // Convert ArrayState to State only on violation path (rare).
                        let init_state = init_array.to_state(&self.var_registry);
                        let trace = Trace::from_states(vec![init_state]);
                        return Some(CheckResult::PropertyViolation {
                            property: prop_name.to_string(),
                            kind: crate::check::PropertyViolationKind::StateLevel,
                            trace,
                            stats: stats.clone(),
                        });
                    }
                    Err(error) => {
                        return Some(check_error_to_result(error, stats));
                    }
                }
            }
        }

        // Check state-level []P terms on each reachable state.
        // Part of #2661: Array-backed binding eliminates O(V) HashMap bind_mut per state.
        // Part of #3801: When liveness is active, self.seen is populated even in
        // fp-only mode. Use it directly for zero-conversion iteration.
        // Parity with sequential safety_temporal.rs:196-249.
        if !always_state_terms.is_empty() {
            if self.store_full_states || self.successors.is_some() {
                // Fast path: borrow ArrayState directly from DashMap (no conversion).
                for entry in self.seen.iter() {
                    let fp = *entry.key();
                    let _scope_guard = ctx.scope_guard_with_next_state();
                    *ctx.next_state_mut() = None;
                    let _next_env_guard = ctx.take_next_state_env_guard();
                    let _state_guard = ctx.bind_state_env_guard(entry.value().env_ref());
                    // Part of #3465: Use array-bound eval boundary helper.
                    crate::eval::clear_for_bound_state_eval_scope(ctx);

                    for term in always_state_terms {
                        match eval_property_bool_term(ctx, prop_name, term) {
                            Ok(true) => {}
                            Ok(false) => {
                                let trace =
                                    self.build_trace_from_fingerprint(fp, &graph.state_cache);
                                return Some(CheckResult::PropertyViolation {
                                    property: prop_name.to_string(),
                                    kind: crate::check::PropertyViolationKind::StateLevel,
                                    trace,
                                    stats: stats.clone(),
                                });
                            }
                            Err(error) => {
                                return Some(check_error_to_result(error, stats));
                            }
                        }
                    }
                }
            } else {
                // fp-only fallback: replay already produced ArrayState cache.
                for (fp, cur_array) in graph.state_cache.iter() {
                    let _scope_guard = ctx.scope_guard_with_next_state();
                    *ctx.next_state_mut() = None;
                    let _next_env_guard = ctx.take_next_state_env_guard();
                    let _state_guard = ctx.bind_state_env_guard(cur_array.env_ref());
                    // Part of #3465: Use array-bound eval boundary helper.
                    crate::eval::clear_for_bound_state_eval_scope(ctx);

                    for term in always_state_terms {
                        match eval_property_bool_term(ctx, prop_name, term) {
                            Ok(true) => {}
                            Ok(false) => {
                                let trace =
                                    self.build_trace_from_fingerprint(*fp, &graph.state_cache);
                                return Some(CheckResult::PropertyViolation {
                                    property: prop_name.to_string(),
                                    kind: crate::check::PropertyViolationKind::StateLevel,
                                    trace,
                                    stats: stats.clone(),
                                });
                            }
                            Err(error) => {
                                return Some(check_error_to_result(error, stats));
                            }
                        }
                    }
                }
            }
        }

        // Check action-level []A terms on each transition.
        // Part of #3011: Under symmetry, use succ_witnesses (concrete successor states)
        // instead of canonical representatives from state_cache. Action predicates may
        // have different truth values for different members of a symmetry equivalence class.
        // Matches sequential checker's safety_temporal.rs:372-440.
        if !always_action_terms.is_empty() {
            if let Some(ref witnesses) = graph.succ_witnesses {
                // Symmetry path: iterate concrete witness states.
                for (fp, witness_list) in witnesses.iter() {
                    // Part of #2661: Array-backed binding for current state.
                    // Look up from self.seen (store_full_states=true) or convert
                    // from state_cache (fp-only fallback).
                    let cur_array = self.get_array_state_for_fp(*fp, graph);
                    // Part of #3801: Skip states missing from the cache in
                    // fp-only mode rather than failing hard. Downstream
                    // liveness code handles incomplete graphs gracefully.
                    let Some(cur_array) = cur_array else {
                        continue;
                    };

                    let _scope_guard = ctx.scope_guard_with_next_state();
                    let _state_guard = ctx.bind_state_env_guard(cur_array.env_ref());

                    // Part of #2661: Clear HashMap next_state; successor binding
                    // uses array-backed next_state_env instead of HashMap Env.
                    // Parity with sequential safety_temporal.rs symmetry path.
                    *ctx.next_state_mut() = None;
                    let _outer_next_env_guard = ctx.take_next_state_env_guard();

                    for (dest_canon_fp, succ_arr) in witness_list {
                        // Part of #3140: Skip stuttering transitions (same canonical fp).
                        // Parity with sequential safety_parts.rs:117.
                        if *fp == *dest_canon_fp {
                            continue;
                        }
                        // Part of #2661: Array-backed binding for successor.
                        // Eliminates to_state() + HashMap Env construction per
                        // successor. O(1) slice access via succ_arr.values().
                        let _inner_next_guard = ctx.bind_next_state_env_guard(succ_arr.env_ref());
                        // Part of #3109: Use state boundary clear (retains constants) not full clear.
                        crate::eval::clear_for_state_boundary();

                        for term in always_action_terms {
                            match eval_property_bool_term(ctx, prop_name, term) {
                                Ok(true) => {}
                                Ok(false) => {
                                    let trace = self.build_trace_from_fingerprint(
                                        *dest_canon_fp,
                                        &graph.state_cache,
                                    );
                                    return Some(CheckResult::PropertyViolation {
                                        property: prop_name.to_string(),
                                        kind: crate::check::PropertyViolationKind::ActionLevel,
                                        trace,
                                        stats: stats.clone(),
                                    });
                                }
                                Err(error) => {
                                    return Some(check_error_to_result(error, stats));
                                }
                            }
                        }
                    }
                }
            } else {
                // Non-symmetry path: use canonical representatives from state_cache.
                // Part of #2661: Array-backed binding for both current and successor.
                // Parity with sequential safety_temporal.rs:398-497.
                for (fp, succ_fps) in &graph.cached_successors {
                    let cur_array = self.get_array_state_for_fp(*fp, graph);
                    // Part of #3801: Skip states missing from the cache in
                    // fp-only mode rather than failing hard.
                    let Some(cur_array) = cur_array else {
                        continue;
                    };

                    let _scope_guard = ctx.scope_guard_with_next_state();
                    let _state_guard = ctx.bind_state_env_guard(cur_array.env_ref());
                    *ctx.next_state_mut() = None;
                    let _outer_next_env_guard = ctx.take_next_state_env_guard();

                    for succ_fp in succ_fps {
                        // Part of #3140: Skip stuttering transitions (same fingerprint).
                        // Parity with sequential safety_parts.rs:318-325.
                        if fp == succ_fp {
                            continue;
                        }
                        let succ_array = self.get_array_state_for_fp(*succ_fp, graph);
                        // Part of #3801: Skip successor states missing from the
                        // cache rather than failing hard.
                        let Some(succ_array) = succ_array else {
                            continue;
                        };

                        let _inner_next_guard = ctx.bind_next_state_env_guard(succ_array.env_ref());
                        *ctx.next_state_mut() = None;
                        // Part of #3109: Use state boundary clear (retains constants) not full clear.
                        crate::eval::clear_for_state_boundary();

                        for term in always_action_terms {
                            match eval_property_bool_term(ctx, prop_name, term) {
                                Ok(true) => {}
                                Ok(false) => {
                                    let trace = self
                                        .build_trace_from_fingerprint(*succ_fp, &graph.state_cache);
                                    return Some(CheckResult::PropertyViolation {
                                        property: prop_name.to_string(),
                                        kind: crate::check::PropertyViolationKind::ActionLevel,
                                        trace,
                                        stats: stats.clone(),
                                    });
                                }
                                Err(error) => {
                                    return Some(check_error_to_result(error, stats));
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Get an `ArrayState` for a fingerprint, preferring the `seen` DashMap
    /// (zero conversion) when it contains data, falling back to
    /// `graph.state_cache` for the fp-only path without liveness.
    ///
    /// Part of #2661: Centralizes the DashMap-vs-State-conversion logic.
    /// Part of #3801: When liveness is active, `self.seen` is populated even
    /// in fp-only mode, so we check it first regardless of `store_full_states`.
    /// Part of #3746: When `TLA2_STRICT_LIVENESS=1`, panics on missing states
    /// instead of returning `None`.
    fn get_array_state_for_fp(
        &self,
        fp: Fingerprint,
        graph: &LivenessGraphData,
    ) -> Option<ArrayState> {
        let result = if self.store_full_states || self.successors.is_some() {
            self.seen.get(&fp).map(|r| r.value().clone())
        } else {
            graph.state_cache.get(&fp).cloned()
        };
        if result.is_none() && crate::liveness::debug::strict_liveness() {
            panic!(
                "TLA2_STRICT_LIVENESS: state missing for fp {fp} in \
                 safety-temporal liveness checking"
            );
        }
        result
    }

    /// Build a trace from a fingerprint using the state cache and parent map.
    ///
    /// Walks the parent chain from `target_fp` back to an initial state.
    /// Part of #3801: Falls back to `self.seen` (DashMap) for state data when
    /// the provided `state_cache` is empty, which occurs during periodic
    /// liveness where the lightweight graph builder skips the state cache
    /// snapshot to avoid DashMap weak-consistency issues.
    pub(super) fn build_trace_from_fingerprint(
        &self,
        target_fp: Fingerprint,
        state_cache: &FxHashMap<Fingerprint, ArrayState>,
    ) -> Trace {
        // Part of #3178: Build parent map from the append-only log (cold path).
        let parents = self.parent_log.build_map();

        let mut trace_fps = vec![target_fp];
        let mut current = target_fp;
        while let Some(parent_fp) = parents.get(&current) {
            if *parent_fp == current {
                break; // self-loop guard (initial states have no parent entry)
            }
            trace_fps.push(*parent_fp);
            current = *parent_fp;
        }
        trace_fps.reverse();

        // Part of #3801: When state_cache is empty (periodic liveness), resolve
        // states from self.seen directly. Per-key DashMap::get is strongly
        // consistent (unlike iteration), so this avoids the weak-consistency
        // issue that build_full_state_liveness_cache has.
        let use_seen = state_cache.is_empty();
        let states: Vec<State> = trace_fps
            .iter()
            .filter_map(|fp| {
                if use_seen {
                    self.seen
                        .get(fp)
                        .map(|entry| entry.value().to_state(&self.var_registry))
                } else {
                    state_cache
                        .get(fp)
                        .map(|state| state.to_state(&self.var_registry))
                }
            })
            .collect();
        Trace::from_states(states)
    }
}
