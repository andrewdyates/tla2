// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Debug successor logging helpers for BFS model checking.
//!
//! Extracted from `run.rs` to reduce file size (Part of #1310).
//! Most helpers are only compiled in debug builds (`#[cfg(debug_assertions)]`).
//! FP collision detection is active in both debug and release builds when
//! enabled via env vars (Part of #2841).

#[cfg(debug_assertions)]
use super::debug::DEBUG_LAZY_VALUES_IN_STATE_LINES;
#[cfg(debug_assertions)]
use super::debug::{
    action_filter_matches, debug_successors, debug_successors_action_filter,
    debug_successors_actions, debug_successors_actions_all_states,
    debug_successors_actions_counts_only, debug_successors_dump_state,
    debug_successors_filter_state_tlc_fp, debug_successors_tlc_fp,
    should_debug_successors_for_state, should_print_successor_debug_line,
};
use super::debug::{fmt_tlc_fp, tlc_fp_for_state_values};
#[cfg(debug_assertions)]
use super::AtomicOrdering;
#[cfg(debug_assertions)]
use super::{Arc, Env, FxHashMap, Value};
use super::{ArrayState, Fingerprint, ModelChecker, State};
#[cfg(debug_assertions)]
use crate::eval::eval_entry;

/// Context for `debug_log_successor_details` — bundles the per-state debug
/// information that was previously passed as 8 separate parameters.
#[cfg(debug_assertions)]
pub(super) struct DebugSuccessorCtx<'a> {
    pub fp: Fingerprint,
    pub state_tlc_fp: Option<u64>,
    pub current_depth: usize,
    pub current_array: &'a ArrayState,
    pub registry: &'a crate::var_index::VarRegistry,
    pub had_raw_successors: bool,
    pub debug_actions_this_state: bool,
    pub successors: &'a [(Fingerprint, ArrayState, Option<usize>)],
}

impl<'a> ModelChecker<'a> {
    /// Record a seen state for fingerprint collision detection.
    ///
    /// Part of #2841: FP collision detection is active in both debug and release
    /// builds when enabled via `TLA2_DEBUG_SEEN_TLCFP_DEDUP` or
    /// `TLA2_DEBUG_INTERNAL_FP_COLLISION` env vars. Lazy value tracking remains
    /// debug-only.
    pub(super) fn debug_record_seen_state_array(
        &mut self,
        fp: Fingerprint,
        array_state: &ArrayState,
        depth: usize,
    ) {
        // FP collision detection — active in both debug and release builds
        // when enabled via env var (feature_flag). Part of #2841.
        let tlc_fp = if self.debug.seen_tlc_fp_dedup.is_some()
            || self.debug.internal_fp_collision.is_some()
        {
            let vals = array_state.materialize_values();
            tlc_fp_for_state_values(&vals).ok()
        } else {
            None
        };

        // Check for over-exploration: same TLC FP but different internal FP.
        if let (Some(ref mut seen), Some(tlc_fp)) = (&mut self.debug.seen_tlc_fp_dedup, tlc_fp) {
            match seen.entry(tlc_fp) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(fp);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    let first = *o.get();
                    if first != fp {
                        self.debug.seen_tlc_fp_dedup_collisions += 1;
                        let limit = self.debug.seen_tlc_fp_dedup_collision_limit;
                        if (self.debug.seen_tlc_fp_dedup_collisions as usize) <= limit {
                            eprintln!(
                                "Warning: TLC FP dedup collision tlc={} first={:016x} now={:016x} depth={}",
                                fmt_tlc_fp(tlc_fp),
                                first.0,
                                fp.0,
                                depth
                            );
                        }
                    }
                }
            }
        }

        // Check for under-exploration: same internal FP but different TLC FP.
        if let (Some(ref mut seen), Some(tlc_fp)) = (&mut self.debug.internal_fp_collision, tlc_fp)
        {
            match seen.entry(fp) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(tlc_fp);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    let first_tlc = *o.get();
                    if first_tlc != tlc_fp {
                        self.debug.internal_fp_collisions += 1;
                        let limit = self.debug.internal_fp_collision_limit;
                        if (self.debug.internal_fp_collisions as usize) <= limit {
                            eprintln!(
                                "Warning: internal FP collision internal={:016x} first_tlc={} now_tlc={} depth={}",
                                fp.0,
                                fmt_tlc_fp(first_tlc),
                                fmt_tlc_fp(tlc_fp),
                                depth
                            );
                        }
                    }
                }
            }
        }

        // Lazy value detection — debug builds only.
        #[cfg(debug_assertions)]
        if super::debug::debug_lazy_values_in_state() {
            let registry = self.ctx.var_registry().clone();
            let mut lazy_hits: Vec<(Arc<str>, &'static str)> = Vec::new();
            let materialized = array_state.materialize_values();
            for (idx, name) in registry.iter() {
                let v = &materialized[idx.as_usize()];
                let kind = match v {
                    Value::Subset(_) => Some("Subset"),
                    Value::FuncSet(_) => Some("FuncSet"),
                    Value::RecordSet(_) => Some("RecordSet"),
                    Value::TupleSet(_) => Some("TupleSet"),
                    Value::SetCup(_) => Some("SetCup"),
                    Value::SetCap(_) => Some("SetCap"),
                    Value::SetDiff(_) => Some("SetDiff"),
                    Value::SetPred(_) => Some("SetPred"),
                    Value::KSubset(_) => Some("KSubset"),
                    Value::BigUnion(_) => Some("BigUnion"),
                    Value::SeqSet(_) => Some("SeqSet"),
                    Value::LazyFunc(_) => Some("LazyFunc"),
                    Value::Closure(_) => Some("Closure"),
                    _ => None,
                };
                if let Some(kind) = kind {
                    lazy_hits.push((Arc::clone(name), kind));
                }
            }
            if !lazy_hits.is_empty() {
                self.debug.lazy_values_in_state_states += 1;
                self.debug.lazy_values_in_state_values += lazy_hits.len() as u64;

                let line = DEBUG_LAZY_VALUES_IN_STATE_LINES.fetch_add(1, AtomicOrdering::Relaxed);
                if line < self.debug.lazy_values_in_state_log_limit {
                    let mut parts: Vec<String> = lazy_hits
                        .into_iter()
                        .map(|(name, kind)| format!("{}={}", name, kind))
                        .collect();
                    parts.sort();
                    eprintln!(
                        "DEBUG LAZY VALUES IN STATE fp={:016x} depth={} vars=[{}]",
                        fp.0,
                        depth,
                        parts.join(",")
                    );
                }
            }
        }
    }

    /// Convenience wrapper that converts a State to ArrayState before recording.
    /// Active in both debug and release builds for collision detection.
    #[inline]
    pub(super) fn maybe_debug_record_seen_state(
        &mut self,
        fp: Fingerprint,
        state: &State,
        depth: usize,
    ) {
        let collision_check =
            self.debug.seen_tlc_fp_dedup.is_some() || self.debug.internal_fp_collision.is_some();

        #[cfg(debug_assertions)]
        let lazy_check = super::debug::debug_lazy_values_in_state();
        #[cfg(not(debug_assertions))]
        let lazy_check = false;

        if collision_check || lazy_check {
            let arr = ArrayState::from_state(state, self.ctx.var_registry());
            self.debug_record_seen_state_array(fp, &arr, depth);
        }
    }

    #[cfg(debug_assertions)]
    pub(super) fn debug_action_label_for_transition_array(
        &mut self,
        current: &ArrayState,
        next: &ArrayState,
    ) -> String {
        if self.coverage.actions.is_empty() {
            return "<unknown-action>".to_string();
        }

        let _state_guard = self.ctx.bind_state_env_guard(current.env_ref());
        let _next_guard = self.ctx.bind_next_state_env_guard(next.env_ref());
        let prev_next_state = self.ctx.next_state_mut().take();

        // UNCHANGED requires `ctx.next_state` (HashMap) even when `next_state_env` is set.
        // Build a full next-state environment for action evaluation.
        let mut next_env = Env::new();
        for (idx, name) in self.ctx.var_registry().iter() {
            next_env.insert(Arc::clone(name), next.get(idx));
        }
        *self.ctx.next_state_mut() = Some(Arc::new(next_env));

        let mut fired = Vec::new();
        for action in &self.coverage.actions {
            match eval_entry(&self.ctx, &action.expr) {
                Ok(Value::Bool(true)) => fired.push(action.name.clone()),
                Ok(Value::Bool(false)) => {}
                Ok(other) => {
                    // Part of #1433: warn on non-boolean action result.
                    // TLC would report this as a type error.
                    eprintln!(
                        "WARNING: action '{}' returned non-boolean value {:?} during coverage eval",
                        action.name, other
                    );
                }
                Err(e) => {
                    // Part of #1433: warn instead of silently swallowing.
                    // TLC propagates EvalException from action coverage.
                    eprintln!(
                        "WARNING: action '{}' eval error during coverage: {}",
                        action.name, e
                    );
                }
            }
        }

        *self.ctx.next_state_mut() = prev_next_state;
        // `_next_guard` and `_state_guard` restore array envs on drop.

        if fired.is_empty() {
            "<unmatched-action>".to_string()
        } else {
            fired.join("|")
        }
    }

    /// Compute debug flags for successor logging. Returns (state_tlc_fp, debug_state,
    /// print_state_line, debug_actions_this_state). Only compiled in debug builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_successor_flags(
        &self,
        fp: Fingerprint,
        current_array: &ArrayState,
    ) -> (Option<u64>, bool, bool, bool) {
        let state_tlc_fp =
            if debug_successors_tlc_fp() || debug_successors_filter_state_tlc_fp().is_some() {
                let vals = current_array.materialize_values();
                tlc_fp_for_state_values(&vals).ok()
            } else {
                None
            };
        let debug_state = should_debug_successors_for_state(fp, state_tlc_fp);
        let print_state_line = debug_successors() && should_print_successor_debug_line(debug_state);
        let debug_actions_this_state = debug_successors_actions()
            && (debug_state || (debug_successors_actions_all_states() && print_state_line));
        (
            state_tlc_fp,
            debug_state,
            print_state_line,
            debug_actions_this_state,
        )
    }

    /// Print the "STATE ... -> N successors (mode)" line.
    #[cfg(debug_assertions)]
    pub(super) fn debug_print_state_line(
        fp: Fingerprint,
        state_tlc_fp: Option<u64>,
        depth: usize,
        num_successors: usize,
        mode_suffix: &str,
    ) {
        let suffix = if mode_suffix.is_empty() {
            String::new()
        } else {
            format!(" ({})", mode_suffix)
        };
        if let Some(tlc_fp) = state_tlc_fp {
            eprintln!(
                "STATE {:016x} tlc={} depth={} -> {} successors{}",
                fp.0,
                fmt_tlc_fp(tlc_fp),
                depth,
                num_successors,
                suffix
            );
        } else {
            eprintln!(
                "STATE {:016x} depth={} -> {} successors{}",
                fp.0, depth, num_successors, suffix
            );
        }
    }

    /// Log detailed debug successor information. Handles the "DEBUG SUCCESSORS" header,
    /// per-successor lines (with optional action labels and change counts), and action
    /// count summaries. Each successor is represented as (fingerprint, ArrayState, Option<changes>).
    #[cfg(debug_assertions)]
    pub(super) fn debug_log_successor_details(&mut self, ctx: &DebugSuccessorCtx<'_>) {
        // Header
        if let Some(tlc_fp) = ctx.state_tlc_fp {
            eprintln!(
                "DEBUG SUCCESSORS state internal={:016x} tlc={} depth={} successors={} had_raw={}",
                ctx.fp.0,
                fmt_tlc_fp(tlc_fp),
                ctx.current_depth,
                ctx.successors.len(),
                ctx.had_raw_successors
            );
        } else {
            eprintln!(
                "DEBUG SUCCESSORS state internal={:016x} depth={} successors={} had_raw={}",
                ctx.fp.0,
                ctx.current_depth,
                ctx.successors.len(),
                ctx.had_raw_successors
            );
        }

        debug_block!(debug_successors_dump_state(), {
            eprintln!(
                "DEBUG SUCCESSORS state value: {:?}",
                ctx.current_array.to_state(ctx.registry)
            );
        });

        let action_filter = debug_successors_action_filter();
        let counts_only = ctx.debug_actions_this_state && debug_successors_actions_counts_only();
        let mut action_counts: FxHashMap<String, usize> = FxHashMap::default();

        if counts_only {
            for (_, succ_state, _) in ctx.successors {
                let action_label =
                    self.debug_action_label_for_transition_array(ctx.current_array, succ_state);
                if let Some(ref filter) = action_filter {
                    if !action_filter_matches(&action_label, filter) {
                        continue;
                    }
                }
                *action_counts.entry(action_label).or_insert(0) += 1;
            }
        } else {
            let mut succ_debug: Vec<(Fingerprint, u64, Option<usize>, String)> =
                Vec::with_capacity(ctx.successors.len());
            for (succ_fp, succ_state, changes) in ctx.successors {
                let succ_vals = succ_state.materialize_values();
                let succ_tlc_fp = tlc_fp_for_state_values(&succ_vals).unwrap_or(0);
                let action_label = if ctx.debug_actions_this_state {
                    self.debug_action_label_for_transition_array(ctx.current_array, succ_state)
                } else {
                    String::new()
                };
                if let (true, Some(ref filter)) = (ctx.debug_actions_this_state, &action_filter) {
                    if !action_filter_matches(&action_label, filter) {
                        continue;
                    }
                }
                if ctx.debug_actions_this_state {
                    *action_counts.entry(action_label.clone()).or_insert(0) += 1;
                }
                succ_debug.push((*succ_fp, succ_tlc_fp, *changes, action_label));
            }
            succ_debug.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0 .0.cmp(&b.0 .0)));
            for (succ_fp, succ_tlc_fp, changes, action_label) in succ_debug {
                match (ctx.debug_actions_this_state, changes) {
                    (true, Some(c)) => eprintln!(
                        "  succ internal={:016x} tlc={} changes={} action={}",
                        succ_fp.0,
                        fmt_tlc_fp(succ_tlc_fp),
                        c,
                        action_label
                    ),
                    (true, None) => eprintln!(
                        "  succ internal={:016x} tlc={} action={}",
                        succ_fp.0,
                        fmt_tlc_fp(succ_tlc_fp),
                        action_label
                    ),
                    (false, Some(c)) => eprintln!(
                        "  succ internal={:016x} tlc={} changes={}",
                        succ_fp.0,
                        fmt_tlc_fp(succ_tlc_fp),
                        c
                    ),
                    (false, None) => eprintln!(
                        "  succ internal={:016x} tlc={}",
                        succ_fp.0,
                        fmt_tlc_fp(succ_tlc_fp)
                    ),
                }
            }
        }

        if ctx.debug_actions_this_state && !action_counts.is_empty() {
            let mut items: Vec<(String, usize)> = action_counts.into_iter().collect();
            items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
            for (name, count) in items {
                eprintln!("  action_count {} = {}", name, count);
            }
        }
    }
}
