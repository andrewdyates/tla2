// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Initial-state processing pipeline: constraint checking, fingerprinting,
//! dedup, and invariant verification for the parallel checker.

use super::*;
use crate::{ConfigCheckError, EvalCheckError};

/// Bundled context for initial state seeding (avoids too-many-arguments on helper methods).
pub(super) struct SeedingCtx<'a> {
    pub(super) var_registry: &'a Arc<VarRegistry>,
    pub(super) cached_view_name: &'a Option<String>,
    /// Part of #3053: Init predicates from PROPERTY classification.
    /// Non-Always state/constant-level terms that must be checked against initial states.
    pub(super) property_init_predicates: &'a [(String, tla_core::Spanned<tla_core::ast::Expr>)],
    /// Part of #3011: Symmetry permutations for canonical fingerprinting of initial states.
    /// Must be the computed permutations from `prepare_check()`, not the always-empty
    /// `ParallelChecker.mvperms` field.
    pub(super) mvperms: &'a [crate::value::MVPerm],
    /// Part of #2676: State-level property names promoted to invariant checking.
    /// Used to route violations through `PropertyViolation` (StateLevel) instead
    /// of `InvariantViolation`, matching TLC's error message format.
    pub(super) promoted_property_invariants: &'a [String],
}

#[allow(clippy::result_large_err)] // CheckResult is intentionally large (enum of all outcomes)
pub(super) fn bulk_len_as_u32(s: &BulkStateStorage) -> Result<u32, CheckResult> {
    u32::try_from(s.len()).map_err(|_| {
        CheckResult::from_error(
            ConfigCheckError::Setup(format!("{} initial states exceeds u32", s.len())).into(),
            CheckStats::default(),
        )
    })
}

impl ParallelChecker {
    /// Process a single initial state: check constraints, compute fingerprint,
    /// dedup, and check invariants. Returns `Ok(Some(fp))` to enqueue the state,
    /// `Ok(None)` to skip, or `Err(CheckResult)` for violations/errors.
    #[allow(clippy::result_large_err)]
    pub(super) fn process_initial_state(
        &self,
        ctx: &mut EvalCtx,
        arr_state: &mut ArrayState,
        state_for_trace: Option<&State>,
        seed_ctx: &SeedingCtx,
        num_initial: usize,
    ) -> Result<Option<Fingerprint>, CheckResult> {
        let var_registry = &**seed_ctx.var_registry;
        let cached_view_name = &seed_ctx.cached_view_name;
        // State constraints (CONSTRAINT directive)
        match check_state_constraints_array(ctx, &self.config.constraints, arr_state) {
            Ok(true) => {}
            Ok(false) => return Ok(None),
            Err(error) => {
                // Part of #2777: Route through check_error_to_result so
                // ExitRequested maps to LimitReached(Exit).
                let stats = CheckStats {
                    initial_states: num_initial + 1,
                    states_found: self.states_count(),
                    ..Default::default()
                };
                return Err(check_error_to_result(error, &stats));
            }
        }

        // Part of #2018: Materialize lazy values (SetPred, LazyFunc, Closure)
        // before fingerprinting. TLC always materializes before fingerprinting.
        // Without this, parallel mode uses ID-based fingerprints (#1989).
        if let Err(e) =
            crate::materialize::materialize_array_state(ctx, arr_state, self.spec_may_produce_lazy)
        {
            // Part of #2777: Route through check_error_to_result so
            // ExitRequested maps to LimitReached(Exit).
            let stats = CheckStats {
                initial_states: num_initial + 1,
                states_found: self.states_count(),
                ..Default::default()
            };
            return Err(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &stats,
            ));
        }

        // Compute fingerprint (with VIEW transformation if configured)
        // Part of #3906: Use array-native path to avoid O(n) ArrayState → State (OrdMap)
        // conversion. compute_view_fingerprint_array uses the projection fast-path for
        // simple VIEWs and falls back to eval with array-based binding for complex ones.
        let fp = if let Some(ref view_name) = cached_view_name {
            // Part of #2777: Route through check_error_to_result so
            // ExitRequested maps to LimitReached(Exit).
            crate::checker_ops::compute_view_fingerprint_array(ctx, arr_state, view_name, 1)
                .map_err(|e| {
                    let stats = CheckStats {
                        initial_states: num_initial + 1,
                        states_found: self.states_count(),
                        ..Default::default()
                    };
                    check_error_to_result(e, &stats)
                })?
        } else if !seed_ctx.mvperms.is_empty() {
            // Part of #3011: Apply symmetry canonical fingerprinting for initial states.
            // Uses seed_ctx.mvperms (computed in prepare_check) instead of self.mvperms
            // which is always empty — the struct field is never populated.
            let fp = crate::state::compute_canonical_fingerprint_from_compact_array(
                arr_state.values(),
                var_registry,
                seed_ctx.mvperms,
            );
            // Cache canonical fp so base_fingerprint() returns it when dequeued.
            arr_state.set_cached_fingerprint(fp);
            fp
        } else {
            arr_state.fingerprint(var_registry)
        };

        // Dedup
        // Part of #3175: cache_for_liveness derived from successors presence.
        let cache_for_liveness = self.successors.is_some();
        if let Some(diagnostics) = &self.collision_diagnostics {
            diagnostics.record_state(fp, arr_state, 0);
        }
        let is_new = if self.store_full_states {
            self.seen.insert(fp, arr_state.clone()).is_none()
        } else {
            match self.seen_fps.insert_checked(fp) {
                InsertOutcome::Inserted => {
                    // Part of #3801: When liveness is active, also store the
                    // full ArrayState in `seen` so post-BFS liveness has all
                    // states without needing the unreliable fp-only replay.
                    if cache_for_liveness {
                        self.seen.insert(fp, arr_state.clone());
                    }
                    true
                }
                InsertOutcome::AlreadyPresent => false,
                InsertOutcome::StorageFault(fault) => {
                    // Part of #2056: Use shared conversion helper.
                    let error =
                        crate::checker_ops::storage_fault_to_check_error(&*self.seen_fps, &fault);
                    return Err(CheckResult::from_error(
                        error,
                        CheckStats {
                            initial_states: num_initial + 1,
                            states_found: self.states_count(),

                            ..Default::default()
                        },
                    ));
                }
                _ => unreachable!(),
            }
        };
        if !is_new {
            return Ok(None);
        }

        if cache_for_liveness {
            self.liveness_init_states.insert(fp, arr_state.clone());
        }

        // Part of #2123: Reserve admission slot for initial state.
        if let Some(limit) = self.max_states_limit {
            if !crate::checker_ops::try_reserve_state_slot(&self.admitted_states, limit) {
                return Err(CheckResult::LimitReached {
                    limit_type: LimitType::States,
                    stats: CheckStats {
                        initial_states: num_initial,
                        states_found: self.states_count(),
                        ..Default::default()
                    },
                });
            }
        }

        // Part of #3233: Track depth=0 only when checkpoint or fp-only liveness needs it.
        if self.track_depths_enabled() {
            self.depths.insert(fp, 0);
        }

        // Initial invariants check
        if !self.config.invariants.is_empty() {
            crate::eval::clear_for_state_boundary();
            if self.uses_trace {
                let trace_state = match state_for_trace {
                    Some(s) => states_to_trace_value(std::slice::from_ref(s)),
                    None => {
                        let s = arr_state.to_state(var_registry);
                        states_to_trace_value(&[s])
                    }
                };
                ctx.set_tlc_trace_value(Some(trace_state));
            }
            match check_invariants_array_state(ctx, &self.config.invariants, arr_state) {
                Ok(Some(invariant)) => {
                    if self.uses_trace {
                        ctx.set_tlc_trace_value(None);
                    }
                    if self.continue_on_error {
                        let _ = self.first_violation.set((invariant, fp));
                    } else {
                        let state = match state_for_trace {
                            Some(s) => s.clone(),
                            None => arr_state.to_state(var_registry),
                        };
                        let trace = Trace::from_states(vec![state]);
                        let stats = CheckStats {
                            initial_states: num_initial + 1,
                            states_found: self.states_count(),
                            ..Default::default()
                        };
                        // Part of #2676: check if this invariant was promoted from a PROPERTY entry.
                        return Err(
                            if seed_ctx.promoted_property_invariants.contains(&invariant) {
                                CheckResult::PropertyViolation {
                                    property: invariant,
                                    kind: crate::check::PropertyViolationKind::StateLevel,
                                    trace,
                                    stats,
                                }
                            } else {
                                CheckResult::InvariantViolation {
                                    invariant,
                                    trace,
                                    stats,
                                }
                            },
                        );
                    }
                }
                Ok(None) => {
                    if self.uses_trace {
                        ctx.set_tlc_trace_value(None);
                    }
                }
                Err(error) => {
                    if self.uses_trace {
                        ctx.set_tlc_trace_value(None);
                    }
                    // Part of #2777: Route through check_error_to_result so
                    // ExitRequested maps to LimitReached(Exit).
                    let stats = CheckStats {
                        initial_states: num_initial + 1,
                        states_found: self.states_count(),
                        ..Default::default()
                    };
                    return Err(check_error_to_result(error, &stats));
                }
            }
        }

        // Part of #3053: Check property init predicates against initial states.
        // Mirrors sequential checker's check_init_state (run_bfs_full.rs:116-123).
        // Without this, properties with init predicates (e.g., `M!Init /\ [][M!Next]_M!vars`)
        // have their init predicate silently dropped, causing false negatives.
        if !seed_ctx.property_init_predicates.is_empty() {
            crate::eval::clear_for_state_boundary();
            match crate::checker_ops::check_property_init_predicates(
                ctx,
                seed_ctx.property_init_predicates,
                arr_state,
            ) {
                Ok(Some(property)) => {
                    if self.continue_on_error {
                        let _ = self.first_violation.set((property, fp));
                    } else {
                        let state = match state_for_trace {
                            Some(s) => s.clone(),
                            None => arr_state.to_state(var_registry),
                        };
                        let trace = Trace::from_states(vec![state]);
                        // Part of #2676: property_init_predicates always come from PROPERTY entries.
                        return Err(CheckResult::PropertyViolation {
                            property,
                            kind: crate::check::PropertyViolationKind::StateLevel,
                            trace,
                            stats: CheckStats {
                                initial_states: num_initial + 1,
                                states_found: self.states_count(),
                                ..Default::default()
                            },
                        });
                    }
                }
                Ok(None) => {}
                Err(error) => {
                    let stats = CheckStats {
                        initial_states: num_initial + 1,
                        states_found: self.states_count(),
                        ..Default::default()
                    };
                    return Err(check_error_to_result(error, &stats));
                }
            }
        }

        Ok(Some(fp))
    }
}
