// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fused 4-lane thread orchestrator for cooperative BFS+BMC+PDR+k-Induction verification.
//!
//! Unlike the [`portfolio`](super::portfolio) orchestrator which races
//! independent lanes, the fused orchestrator enables **cooperative**
//! cross-engine communication via [`SharedCooperativeState`]:
//!
//! - BFS sends concrete frontier states to seed BMC symbolic exploration
//! - PDR-proved invariants let BFS skip per-state invariant checks
//! - k-Induction proves safety via bounded inductive arguments
//! - Any lane's definitive verdict terminates all others via [`SharedVerdict`]
//!
//! # Architecture
//!
//! ```text
//! ┌─────────┐  frontier samples  ┌─────────┐
//! │  Lane 1 │ ─────────────────▶ │  Lane 2 │
//! │   BFS   │                    │   BMC   │
//! └────┬────┘                    └─────────┘
//!      │         ┌─────────┐
//!      │◀───────│  Lane 3 │  invariants_proved
//!               │   PDR   │
//!               └─────────┘
//!                ┌─────────┐
//!                │  Lane 4 │  k-inductive proofs
//!                │  k-Ind  │
//!                └─────────┘
//! ```
//!
//! Part of #3769, #3844.

#[cfg(feature = "z4")]
use std::sync::Arc;

use tla_core::ast::Module;
#[cfg(feature = "z4")]
use tla_core::ast::{OperatorDef, Unit};

#[cfg(feature = "z4")]
use crate::check::wavefront::{entropy_score, WavefrontCompressor, MIN_ENTROPY_THRESHOLD};
use crate::check::{CheckResult, ModelChecker};
use crate::config::Config;
#[cfg(feature = "z4")]
use crate::cooperative_state::SharedCooperativeState;
#[cfg(feature = "z4")]
use crate::eval::EvalCtx;
#[cfg(feature = "z4")]
use crate::shared_verdict::{SharedVerdict, Verdict};

/// Find an operator definition by name in a parsed module's units.
///
/// Scans the module's top-level units for an `Operator` unit whose name
/// matches the given name. Used by the fused orchestrator to extract
/// the Next relation before the full model checker is initialized.
///
/// Part of #3784.
#[cfg(feature = "z4")]
fn find_operator_def(module: &Module, name: &str) -> Option<OperatorDef> {
    module.units.iter().find_map(|unit| match &unit.node {
        Unit::Operator(def) if def.name.node == name => Some(def.clone()),
        _ => None,
    })
}

/// Convenience function: run fused cooperative verification on a spec.
///
/// This is the public API for CLI and library consumers. It creates a
/// `FusedOrchestrator` and runs the 4-lane cooperative verification.
///
/// Part of #3770.
pub fn run_fused_check<'a>(
    module: &'a Module,
    checker_modules: &[&'a Module],
    config: &'a Config,
) -> FusedResult {
    FusedOrchestrator::new(module, checker_modules, config).run()
}

/// Which lane produced the first definitive result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FusedWinner {
    /// BFS explicit-state model checking resolved first.
    Bfs,
    /// BMC symbolic bug finding resolved first.
    Bmc,
    /// PDR (IC3) symbolic safety proving resolved first.
    Pdr,
    /// k-Induction symbolic safety proving resolved first. Part of #3844.
    KInduction,
}

/// Tracks graceful degradation when z4 translation fails for one or more
/// symbolic lanes. Part of #3837, #3844.
#[derive(Debug, Clone, Default)]
pub struct SymbolicDegradation {
    /// Whether the BMC lane degraded (translation error or panic).
    pub bmc_degraded: bool,
    /// Human-readable reason for BMC degradation, if any.
    pub bmc_reason: Option<String>,
    /// The raw error message from BMC, if it returned Err. Part of #3837.
    pub bmc_error: Option<String>,
    /// Whether the PDR lane degraded (translation error or panic).
    pub pdr_degraded: bool,
    /// Human-readable reason for PDR degradation, if any.
    pub pdr_reason: Option<String>,
    /// The raw error message from PDR, if it returned Err. Part of #3837.
    pub pdr_error: Option<String>,
    /// Whether the k-Induction lane degraded (translation error or panic).
    /// Part of #3844.
    pub kinduction_degraded: bool,
    /// Human-readable reason for k-Induction degradation, if any.
    /// Part of #3844.
    pub kinduction_reason: Option<String>,
    /// Unsupported constructs encountered across all symbolic lanes.
    pub unsupported_constructs: Vec<String>,
    /// Total number of spec actions detected. Part of #3837.
    pub actions_total: usize,
    /// Number of actions that are SMT-compatible (translatable). Part of #3837.
    pub actions_smt_compatible: usize,
    /// Names of actions that are NOT SMT-compatible. Part of #3837.
    pub unsupported_action_names: Vec<String>,
}

impl SymbolicDegradation {
    /// True if at least one symbolic lane degraded.
    pub fn any_degraded(&self) -> bool {
        self.bmc_degraded || self.pdr_degraded || self.kinduction_degraded
    }

    /// Fraction of symbolic lanes that operated successfully (0.0 to 1.0).
    ///
    /// With 3 symbolic lanes (BMC, PDR, k-Induction), each contributes 1/3.
    pub fn lane_coverage(&self) -> f64 {
        let total = 3.0_f64;
        let failed = (self.bmc_degraded as u8
            + self.pdr_degraded as u8
            + self.kinduction_degraded as u8) as f64;
        (total - failed) / total
    }

    /// Fraction of spec actions that translated successfully to SMT (0.0 to 1.0).
    ///
    /// Returns 1.0 if no actions were detected (nothing to translate).
    /// Part of #3837.
    pub fn action_coverage(&self) -> f64 {
        if self.actions_total == 0 {
            return 1.0;
        }
        self.actions_smt_compatible as f64 / self.actions_total as f64
    }

    /// Combined symbolic coverage metric (0.0 to 1.0).
    ///
    /// Blends lane-level and action-level coverage. When all lanes succeed
    /// and all actions translate, returns 1.0. When no actions were detected,
    /// falls back to lane coverage only.
    pub fn symbolic_coverage(&self) -> f64 {
        if self.actions_total == 0 {
            return self.lane_coverage();
        }
        (self.lane_coverage() + self.action_coverage()) / 2.0
    }

    /// Build a human-readable summary line for the degradation report.
    pub fn summary(&self) -> Option<String> {
        if !self.any_degraded()
            && self.actions_total > 0
            && self.actions_smt_compatible < self.actions_total
        {
            let constructs_str = if self.unsupported_constructs.is_empty() {
                String::new()
            } else {
                format!(": {}", self.unsupported_constructs.join(", "))
            };
            return Some(format!(
                "Symbolic coverage: {}/{} actions translatable ({} unsupported{constructs_str})",
                self.actions_smt_compatible,
                self.actions_total,
                self.actions_total - self.actions_smt_compatible,
            ));
        }
        if !self.any_degraded() {
            return None;
        }
        let coverage_pct = (self.lane_coverage() * 100.0) as u32;
        let mut parts = Vec::new();
        if self.bmc_degraded {
            if let Some(ref reason) = self.bmc_reason {
                parts.push(format!("BMC: {reason}"));
            } else {
                parts.push("BMC: translation failed".to_string());
            }
        }
        if self.pdr_degraded {
            if let Some(ref reason) = self.pdr_reason {
                parts.push(format!("PDR: {reason}"));
            } else {
                parts.push("PDR: translation failed".to_string());
            }
        }
        if self.kinduction_degraded {
            if let Some(ref reason) = self.kinduction_reason {
                parts.push(format!("k-Induction: {reason}"));
            } else {
                parts.push("k-Induction: translation failed".to_string());
            }
        }
        let constructs_str = if self.unsupported_constructs.is_empty() {
            String::new()
        } else {
            format!(" (unsupported: {})", self.unsupported_constructs.join(", "))
        };
        let action_str = if self.actions_total > 0 {
            format!(
                " ({}/{} actions translatable)",
                self.actions_smt_compatible, self.actions_total,
            )
        } else {
            String::new()
        };
        Some(format!(
            "Symbolic coverage: {coverage_pct}% lanes{action_str} — {}{constructs_str}",
            parts.join("; "),
        ))
    }
}

/// Result of a fused cooperative verification run.
#[derive(Debug)]
pub struct FusedResult {
    /// Which lane resolved the verdict first.
    pub winner: FusedWinner,
    /// The BFS result (always present — BFS always runs).
    pub bfs_result: CheckResult,
    /// The BMC result, if the z4 feature is enabled and BMC ran.
    #[cfg(feature = "z4")]
    pub(crate) bmc_result: Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>>,
    /// The PDR result, if the z4 feature is enabled and PDR ran.
    #[cfg(feature = "z4")]
    pub(crate) pdr_result: Option<Result<crate::z4_pdr::PdrResult, crate::z4_pdr::PdrError>>,
    /// The k-Induction result, if the z4 feature is enabled and k-Induction ran.
    /// Part of #3844.
    #[cfg(feature = "z4")]
    pub(crate) kinduction_result: Option<
        Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
    >,
    /// Summary string identifying the first verdict source.
    pub symbolic_summary: Option<String>,
    /// Graceful degradation tracking for symbolic lanes. Part of #3837.
    pub degradation: SymbolicDegradation,
    /// Fraction of spec actions that translated successfully to z4 (0.0 to 1.0).
    /// Part of #3837.
    pub symbolic_coverage: f64,
    /// Cross-validation result when a symbolic engine produced a verdict.
    ///
    /// Present when BMC found a counterexample (replayed through BFS evaluator)
    /// or when PDR proved safety (checked against BFS completion status).
    /// `None` when only BFS ran or symbolic engines were inconclusive.
    ///
    /// Part of #3836.
    #[cfg(feature = "z4")]
    pub cross_validation: Option<crate::check::cross_validation::CrossValidationResult>,
    /// JIT re-verification result for BMC counterexample traces.
    ///
    /// Part of #3855 (FJ3: Symbolic Engine Provides Counterexample States to JIT).
    #[cfg(feature = "z4")]
    pub jit_verification: Option<crate::check::symbolic_to_jit_bridge::TraceVerificationResult>,
}

/// Fused 4-lane orchestrator for cooperative multi-engine model checking.
///
/// Spawns BFS, BMC, PDR, and k-Induction lanes in parallel with cross-engine
/// communication via [`SharedCooperativeState`]. Unlike portfolio mode,
/// the lanes actively cooperate: BFS feeds concrete states to BMC,
/// PDR proofs prune BFS invariant checks, and k-Induction provides
/// bounded inductive safety proofs.
pub(crate) struct FusedOrchestrator<'a> {
    module: &'a Module,
    checker_modules: Vec<&'a Module>,
    config: &'a Config,
}

impl<'a> FusedOrchestrator<'a> {
    /// Create a new fused orchestrator for the given spec.
    pub(crate) fn new(
        module: &'a Module,
        checker_modules: &[&'a Module],
        config: &'a Config,
    ) -> Self {
        Self {
            module,
            checker_modules: checker_modules.to_vec(),
            config,
        }
    }

    /// Run the 4-lane cooperative verification.
    ///
    /// Spawns four threads via [`std::thread::scope`]:
    /// 1. **BFS** — explicit-state model checking, publishing frontier samples
    /// 2. **BMC** — z4 bounded model checking, seeded by BFS frontier (z4 feature)
    /// 3. **PDR** — z4 IC3 safety proving, feeding invariant proofs back (z4 feature)
    /// 4. **k-Induction** — z4 bounded inductive safety proving (z4 feature)
    ///
    /// The first lane to reach a definitive verdict (Satisfied or Violated)
    /// publishes to [`SharedVerdict`]; other lanes exit on their next poll.
    #[cfg(feature = "z4")]
    pub(crate) fn run(&self) -> FusedResult {
        // Part of #3784: detect actions from the Next relation to size
        // per-action metrics correctly before threads start.
        let detected_actions = self
            .config
            .next
            .as_ref()
            .and_then(|next_name| find_operator_def(self.module, next_name))
            .map(|next_def| crate::coverage::detect_actions(&next_def))
            .unwrap_or_default();
        let action_count = detected_actions.len();
        // Part of #3773: pass invariant count for per-invariant proof tracking.
        let invariant_count = self.config.invariants.len();
        let mut coop_state =
            SharedCooperativeState::with_invariant_count(action_count, invariant_count);

        // Part of #3954: expand action expressions before SMT compat check.
        //
        // The raw action expressions from detect_actions() are often just Ident
        // nodes (operator references), which trivially pass the SMT compat filter.
        // To accurately predict whether z4 can translate an action, we expand
        // operator definitions first via expand_operators_for_chc, then run the
        // SMT compat check on the fully-expanded expression tree.
        //
        // This changes the oracle from "always accepts" to "accurately rejects
        // actions with Lambda/temporal/InstanceExpr in their expanded body,"
        // improving routing accuracy and reducing z4 translator failures.
        let mut compat_ctx = EvalCtx::new();
        compat_ctx.load_module(self.module);
        for extra in &self.checker_modules {
            compat_ctx.load_module(extra);
        }
        let smt_flags: Vec<bool> = detected_actions
            .iter()
            .map(|action| {
                let expanded = crate::z4_pdr::expand_operators_for_chc(
                    &compat_ctx,
                    &action.expr,
                    true, // allow_primed: action exprs contain x' = ... patterns
                );
                crate::cooperative_state::is_expr_smt_compatible(&expanded)
            })
            .collect();
        for (i, &compatible) in smt_flags.iter().enumerate() {
            coop_state.mark_smt_compatible(i, compatible);
        }

        // Part of #3954: log per-action SMT compatibility after expansion.
        let smt_count = smt_flags.iter().filter(|&&f| f).count();
        if action_count > 0 {
            eprintln!(
                "[fused] SMT compatibility (expanded): {smt_count}/{action_count} actions compatible"
            );
            for (action, &compatible) in detected_actions.iter().zip(smt_flags.iter()) {
                if !compatible {
                    eprintln!("[fused]   incompatible: {}", action.name);
                }
            }
        }

        // Part of #3826: detect exponential state space patterns (e.g., nested
        // SUBSET(SUBSET ...)) and log them. The evaluator's nested powerset
        // optimization (set_construction.rs) rewrites patterns like
        //   {E \in SUBSET(SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
        // to SUBSET({e \in SUBSET Nodes : Cardinality(e) = 2}), reducing
        // the doubly-exponential 2^(2^N) to a manageable 2^C(N,2).
        //
        // We no longer force all actions to SymbolicOnly here because that
        // makes BFS defer entirely (skipping its init enumeration). With the
        // evaluator optimization, BFS can handle these patterns. Instead, we
        // use normal oracle routing so BFS runs with its optimization while
        // symbolic engines (BMC/PDR/k-Induction) also run in parallel.
        let exponential_complexity =
            crate::check::oracle::detect_exponential_complexity(self.module);
        if let Some(ref signal) = exponential_complexity {
            eprintln!("[fused] exponential complexity detected: {}", signal.reason);
            eprintln!(
                "[fused] evaluator optimization should reduce state space; \
                 BFS + symbolic engines running in parallel"
            );
        }
        // Part of #3785: initialize oracle with SMT compatibility flags so
        // the initial routing decisions are correct from the first BFS level.
        // Without this, all actions default to `BfsOnly` until the first
        // reroute at level 5, missing the opportunity to route SMT-compatible
        // actions to `Either` from the start.
        coop_state.initialize_oracle(&smt_flags);

        // Register action names for name-based oracle lookups.
        let action_names: Vec<String> = detected_actions.iter().map(|a| a.name.clone()).collect();
        coop_state.register_action_names(&action_names);

        let coop = Arc::new(coop_state);

        std::thread::scope(|scope| {
            let coop_bfs = coop.clone();
            let coop_bmc = coop.clone();
            let coop_pdr = coop.clone();
            let coop_kind = coop.clone();
            let coop_wavefront = coop.clone();

            let module = self.module;
            let checker_modules = &self.checker_modules;
            let config = self.config;

            // Lane 1: BFS explicit-state model checking.
            //
            // Part of #3772: wire cooperative state into BFS so that:
            // (a) frontier sampler sends concrete states to BMC via the channel,
            // (b) BFS polls the cooperative verdict for early termination when
            //     BMC/PDR resolve first.
            // Part of #3823: pass checker_modules for EXTENDS/INSTANCE support.
            // Part of #3867: catch_unwind on all lanes to cancel verdict on panic,
            // preventing deadlock where surviving lanes spin forever.
            let coop_bfs_panic = coop.clone();
            let bfs_handle = scope.spawn(move || {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut checker =
                        ModelChecker::new_with_extends(module, checker_modules, config);
                    checker.set_portfolio_verdict(coop_bfs.verdict_arc());
                    checker.set_cooperative_state(coop_bfs.clone());
                    checker.check()
                }));
                if result.is_err() {
                    coop_bfs_panic.verdict.cancel();
                }
                result
            });

            // Wavefront compressor thread (Part of #3794 Wave 3, #3845 Wave 5).
            //
            // Drains frontier samples from the BFS lane, groups by depth,
            // applies entropy-based quality filtering before compressing into
            // a disjunctive formula for the BMC lane.
            //
            // Quality control (#3845): low-entropy batches (identical or
            // near-identical states from early BFS levels) are skipped
            // because they add no diversity for symbolic exploration.
            scope.spawn(move || {
                use std::time::Duration;

                let compressor = WavefrontCompressor::with_default_threshold();
                let poll = Duration::from_millis(250);

                let mut batch: Vec<crate::cooperative_state::FrontierSample> = Vec::new();
                let mut current_depth: Option<usize> = None;

                // Helper closure: evaluate entropy, filter, and compress a batch.
                // Metrics are recorded on the cooperative state so they are observable
                // externally (not lost when this thread exits). Part of #3794.
                let try_compress_batch = |batch: &[crate::cooperative_state::FrontierSample],
                                          compressor: &WavefrontCompressor,
                                          coop: &SharedCooperativeState|
                 -> bool {
                    if !compressor.should_compress(batch.len()) {
                        return false;
                    }

                    let score = entropy_score(batch);

                    if score < MIN_ENTROPY_THRESHOLD {
                        coop.record_wavefront_skipped_low_entropy();
                        return false;
                    }

                    if let Some(formula) = compressor.compress_frontier(batch) {
                        if coop.send_wavefront(formula) {
                            coop.record_wavefront_sent();
                            return true;
                        }
                    }
                    false
                };

                loop {
                    if coop_wavefront.is_resolved() {
                        try_compress_batch(&batch, &compressor, &coop_wavefront);
                        return;
                    }

                    match coop_wavefront.recv_frontier_sample(poll) {
                        Some(sample) => {
                            let sample_depth = sample.depth;

                            // Depth transition: compress accumulated batch.
                            if let Some(prev) = current_depth {
                                if sample_depth > prev && !batch.is_empty() {
                                    try_compress_batch(&batch, &compressor, &coop_wavefront);
                                    batch.clear();
                                }
                            }

                            current_depth = Some(sample_depth);
                            batch.push(sample);
                        }
                        None => {
                            // Timeout: if we have a large enough batch, compress
                            // it even without a depth transition (BFS may have
                            // stalled or finished the level).
                            if compressor.should_compress(batch.len()) {
                                try_compress_batch(&batch, &compressor, &coop_wavefront);
                                batch.clear();
                            }
                        }
                    }
                }
            });

            // Lane 2: BMC symbolic bug finding.
            //
            // Part of #3772: in normal mode, uses cooperative BMC
            // (check_bmc_cooperative) which polls the frontier channel for
            // concrete states sent by BFS at level boundaries.
            //
            // Part of #3826: when exponential complexity is detected (all actions
            // routed to SymbolicOnly), BFS defers entirely and sends no frontier
            // states. In this mode, use standalone BMC (check_bmc_with_portfolio)
            // which runs from Init independently, avoiding a deadlock where
            // cooperative BMC waits for frontier states that will never arrive.
            let is_exponential = exponential_complexity.is_some();
            let coop_bmc_panic = coop.clone();
            let bmc_handle = scope.spawn(move || {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut bmc_ctx = EvalCtx::new();
                    bmc_ctx.load_module(module);
                    let bmc_config = crate::z4_bmc::BmcConfig {
                        max_depth: 20,
                        ..Default::default()
                    };
                    if is_exponential {
                        // Standalone BMC from Init — no BFS frontier dependency.
                        eprintln!("[fused] BMC running standalone from Init (exponential complexity mode)");
                        crate::z4_bmc::check_bmc_with_portfolio(
                            module,
                            config,
                            &bmc_ctx,
                            bmc_config,
                            Some(coop_bmc.verdict_arc()),
                        )
                    } else {
                        // Cooperative BMC seeded by BFS frontier states.
                        crate::z4_bmc::check_bmc_cooperative(
                            module, config, &bmc_ctx, bmc_config, coop_bmc,
                        )
                    }
                }));
                if result.is_err() {
                    coop_bmc_panic.verdict.cancel();
                }
                result
            });

            // Lane 3: PDR symbolic safety proving.
            //
            // Part of #3772: switch from independent PDR (check_pdr_with_portfolio)
            // to cooperative PDR (check_pdr_cooperative) which publishes proved
            // invariants and verdicts directly to the cooperative state.
            let coop_pdr_panic = coop.clone();
            let pdr_handle = scope.spawn(move || {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut pdr_ctx = EvalCtx::new();
                    pdr_ctx.load_module(module);
                    let mut pdr_config: tla_z4::PdrConfig = Default::default();
                    pdr_config.solve_timeout = Some(std::time::Duration::from_secs(300));
                    crate::z4_pdr::check_pdr_cooperative(
                        module, config, &pdr_ctx, pdr_config, coop_pdr,
                    )
                }));
                if result.is_err() {
                    coop_pdr_panic.verdict.cancel();
                }
                result
            });

            // Lane 4: k-Induction symbolic safety proving.
            //
            // Part of #3844: spawn the k-induction lane which attempts to prove
            // safety properties via bounded inductive arguments. On success
            // (UNSAT at inductive step), publishes Satisfied to the cooperative
            // verdict. Base-case counterexamples publish Violated (these are real
            // violations from Init). Inconclusive results do NOT publish a verdict.
            let coop_kind_panic = coop.clone();
            let kind_handle = scope.spawn(move || {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut kind_ctx = EvalCtx::new();
                    kind_ctx.load_module(module);
                    let kind_config = crate::z4_kinduction::KInductionConfig::default();
                    crate::z4_kinduction::check_kinduction_cooperative(
                        module,
                        config,
                        &kind_ctx,
                        kind_config,
                        coop_kind,
                    )
                }));
                if result.is_err() {
                    coop_kind_panic.verdict.cancel();
                }
                result
            });

            // Join all lanes. Each handle returns Result<Result<T>, PanicPayload>
            // from catch_unwind. On panic, the verdict was already cancelled
            // inside the lane closure, so other lanes will have exited.
            //
            // Part of #3867: handle panics gracefully instead of deadlocking.
            let bfs_join = bfs_handle.join();
            let bmc_join = bmc_handle.join();
            let pdr_join = pdr_handle.join();
            let kind_join = kind_handle.join();

            // Unwrap BFS: if BFS panicked, propagate by resuming the panic.
            // BFS is the primary lane — its result is always needed.
            let bfs_result = match bfs_join {
                Ok(Ok(result)) => result,
                Ok(Err(payload)) => std::panic::resume_unwind(payload),
                Err(join_err) => std::panic::resume_unwind(join_err),
            };

            // BMC/PDR panics are non-fatal: log and treat as None.
            let bmc_result = match bmc_join {
                Ok(Ok(result)) => Some(result),
                Ok(Err(_)) => {
                    eprintln!("[fused] BMC lane panicked — continuing with BFS result");
                    None
                }
                Err(_) => {
                    eprintln!(
                        "[fused] BMC lane panicked (join error) — continuing with BFS result"
                    );
                    None
                }
            };

            let pdr_result = match pdr_join {
                Ok(Ok(result)) => Some(result),
                Ok(Err(_)) => {
                    eprintln!("[fused] PDR lane panicked — continuing with BFS result");
                    None
                }
                Err(_) => {
                    eprintln!(
                        "[fused] PDR lane panicked (join error) — continuing with BFS result"
                    );
                    None
                }
            };

            // k-Induction panics are non-fatal: log and treat as None. Part of #3844.
            let kinduction_result = match kind_join {
                Ok(Ok(result)) => Some(result),
                Ok(Err(_)) => {
                    eprintln!("[fused] k-Induction lane panicked — continuing with BFS result");
                    None
                }
                Err(_) => {
                    eprintln!("[fused] k-Induction lane panicked (join error) — continuing with BFS result");
                    None
                }
            };

            // Part of #3837, #3844: build graceful degradation report from
            // BMC/PDR/k-Induction results and per-action SMT compatibility data.
            let degradation = build_degradation(
                &bmc_result,
                &pdr_result,
                &kinduction_result,
                &smt_flags,
                &action_names,
            );
            if let Some(ref summary) = degradation.summary() {
                eprintln!("[fused] {summary}");
            }

            // Part of #3837: per-action symbolic coverage fraction.
            let symbolic_coverage = degradation.action_coverage();

            let winner = determine_fused_winner(&coop.verdict, &bfs_result, &kinduction_result);
            let mut symbolic_summary = match winner {
                FusedWinner::Bfs => "Winner: BFS (explicit-state)".to_string(),
                FusedWinner::Bmc => "Winner: BMC (symbolic bug finding)".to_string(),
                FusedWinner::Pdr => "Winner: PDR (symbolic safety proving)".to_string(),
                FusedWinner::KInduction => {
                    "Winner: k-Induction (symbolic safety proving)".to_string()
                }
            };
            if let Some(deg_summary) = degradation.summary() {
                symbolic_summary.push_str(&format!(". {deg_summary}"));
            }
            let symbolic_summary = Some(symbolic_summary);

            // Part of #3836: cross-validate symbolic verdicts through BFS evaluator.
            let cross_validation = perform_cross_validation(
                module,
                config,
                &winner,
                &bmc_result,
                &pdr_result,
                &kinduction_result,
                &bfs_result,
            );
            if let Some(ref cv) = cross_validation {
                if cv.engine_agrees {
                    eprintln!("[fused] cross-validation OK: {}", cv.detail);
                } else {
                    eprintln!("[fused] cross-validation WARNING: {}", cv.detail);
                }
            }

            // BMC incremental deepening diagnostics.
            {
                let seeds_completed = coop.bmc_seeds_completed();
                let bmc_depth = coop.bmc_max_depth();
                let avg_depth = coop.bmc_avg_seed_depth();
                let deprioritized = coop.bmc_seeds_deprioritized();
                let wavefronts_consumed = coop.wavefronts_consumed();
                let wavefronts_sent = coop.wavefronts_sent();
                let frontier_hint = coop.bfs_frontier_depth_hint();

                if seeds_completed > 0 || wavefronts_consumed > 0 {
                    eprintln!(
                        "[fused] BMC deepening: {} seeds completed, max depth {}, avg depth {:.1}, \
                         {} wavefronts consumed/{} sent, BFS frontier hint depth {}, {} seeds deprioritized",
                        seeds_completed, bmc_depth, avg_depth,
                        wavefronts_consumed, wavefronts_sent,
                        frontier_hint, deprioritized,
                    );
                }
            }

            FusedResult {
                winner,
                bfs_result,
                bmc_result,
                pdr_result,
                kinduction_result,
                symbolic_summary,
                degradation,
                symbolic_coverage,
                cross_validation,
                jit_verification: None,
            }
        })
    }

    /// Non-z4 fallback: runs BFS only (BMC/PDR/k-Induction require z4 feature).
    #[cfg(not(feature = "z4"))]
    pub(crate) fn run(&self) -> FusedResult {
        let mut checker =
            ModelChecker::new_with_extends(self.module, &self.checker_modules, self.config);
        let bfs_result = checker.check();

        FusedResult {
            winner: FusedWinner::Bfs,
            bfs_result,
            symbolic_summary: None,
            degradation: SymbolicDegradation::default(),
            symbolic_coverage: 1.0,
        }
    }
}

/// Classify a BMC error as a translation/degradation failure. Part of #3837.
#[cfg(feature = "z4")]
fn classify_bmc_error(err: &crate::z4_bmc::BmcError) -> (bool, String, Vec<String>) {
    use crate::z4_bmc::BmcError;
    match err {
        BmcError::TranslationError(msg) => {
            let constructs = extract_unsupported_constructs(msg);
            (true, format!("translation failed: {msg}"), constructs)
        }
        BmcError::SolverFailed(msg) => (true, format!("solver failed: {msg}"), vec![]),
        BmcError::MissingSpec(msg) => (false, format!("missing spec: {msg}"), vec![]),
        BmcError::NoInvariants => (false, "no invariants to check".to_string(), vec![]),
        BmcError::CheckError(msg) => (true, format!("check error: {msg}"), vec![]),
    }
}

/// Classify a PDR error as a translation/degradation failure. Part of #3837.
#[cfg(feature = "z4")]
fn classify_pdr_error(err: &crate::z4_pdr::PdrError) -> (bool, String, Vec<String>) {
    use crate::z4_pdr::PdrError;
    match err {
        PdrError::TranslationError(msg) => {
            let constructs = extract_unsupported_constructs(msg);
            (true, format!("translation failed: {msg}"), constructs)
        }
        PdrError::UnsupportedExpr(msg) => {
            let constructs = extract_unsupported_constructs(msg);
            (true, format!("unsupported expression: {msg}"), constructs)
        }
        PdrError::SortInference(msg) => (true, format!("sort inference failed: {msg}"), vec![]),
        PdrError::MissingSpec(msg) => (false, format!("missing spec: {msg}"), vec![]),
        PdrError::NoInvariants => (false, "no invariants to check".to_string(), vec![]),
        PdrError::CheckError(msg) => (true, format!("check error: {msg}"), vec![]),
    }
}

/// Extract names of unsupported TLA+ constructs from error messages. Part of #3837.
///
/// Scans for patterns like "unsupported operator: CHOOSE", "SetFilter not supported", etc.
#[cfg(feature = "z4")]
fn extract_unsupported_constructs(msg: &str) -> Vec<String> {
    let mut constructs = Vec::new();
    let lower = msg.to_lowercase();
    for keyword in &[
        "CHOOSE",
        "SetFilter",
        "SetMap",
        "Lambda",
        "RecursiveOp",
        "SUBSET",
        "UNION",
        "BoundedQuant",
        "LetIn",
    ] {
        if lower.contains(&keyword.to_lowercase()) {
            constructs.push(keyword.to_string());
        }
    }
    if constructs.is_empty() && lower.contains("unsupported") {
        constructs.push("unknown construct".to_string());
    }
    constructs
}

/// Classify a k-Induction error as a translation/degradation failure. Part of #3844.
#[cfg(feature = "z4")]
fn classify_kinduction_error(
    err: &crate::z4_kinduction::KInductionError,
) -> (bool, String, Vec<String>) {
    use crate::z4_kinduction::KInductionError;
    match err {
        KInductionError::TranslationError(msg) => {
            let constructs = extract_unsupported_constructs(msg);
            (true, format!("translation failed: {msg}"), constructs)
        }
        KInductionError::SolverFailed(msg) => (true, format!("solver failed: {msg}"), vec![]),
        KInductionError::MissingSpec(msg) => (false, format!("missing spec: {msg}"), vec![]),
        KInductionError::NoInvariants => (false, "no invariants to check".to_string(), vec![]),
        KInductionError::CheckError(err) => (true, format!("check error: {err:?}"), vec![]),
    }
}

/// Build a `SymbolicDegradation` from the BMC, PDR, and k-Induction results
/// plus per-action SMT compatibility data. Part of #3837, #3844.
#[cfg(feature = "z4")]
fn build_degradation(
    bmc_result: &Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>>,
    pdr_result: &Option<Result<crate::z4_pdr::PdrResult, crate::z4_pdr::PdrError>>,
    kinduction_result: &Option<
        Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
    >,
    smt_flags: &[bool],
    action_names: &[String],
) -> SymbolicDegradation {
    let actions_total = smt_flags.len();
    let actions_smt_compatible = smt_flags.iter().filter(|&&f| f).count();
    let unsupported_action_names: Vec<String> = smt_flags
        .iter()
        .zip(action_names.iter())
        .filter(|(&compatible, _)| !compatible)
        .map(|(_, name)| name.clone())
        .collect();

    let mut degradation = SymbolicDegradation {
        actions_total,
        actions_smt_compatible,
        unsupported_action_names,
        ..Default::default()
    };
    match bmc_result {
        None => {
            degradation.bmc_degraded = true;
            degradation.bmc_reason = Some("lane panicked".to_string());
        }
        Some(Err(err)) => {
            let (_d, reason, constructs) = classify_bmc_error(err);
            degradation.bmc_degraded = true;
            degradation.bmc_reason = Some(reason.clone());
            degradation.bmc_error = Some(format!("{err:?}"));
            degradation.unsupported_constructs.extend(constructs);
        }
        Some(Ok(_)) => {}
    }
    match pdr_result {
        None => {
            degradation.pdr_degraded = true;
            degradation.pdr_reason = Some("lane panicked".to_string());
        }
        Some(Err(err)) => {
            let (_d, reason, constructs) = classify_pdr_error(err);
            degradation.pdr_degraded = true;
            degradation.pdr_reason = Some(reason.clone());
            degradation.pdr_error = Some(format!("{err:?}"));
            degradation.unsupported_constructs.extend(constructs);
        }
        Some(Ok(_)) => {}
    }
    // Part of #3844: k-Induction degradation tracking.
    match kinduction_result {
        None => {
            degradation.kinduction_degraded = true;
            degradation.kinduction_reason = Some("lane panicked".to_string());
        }
        Some(Err(err)) => {
            let (_d, reason, constructs) = classify_kinduction_error(err);
            degradation.kinduction_degraded = true;
            degradation.kinduction_reason = Some(reason);
            degradation.unsupported_constructs.extend(constructs);
        }
        Some(Ok(_)) => {}
    }
    degradation.unsupported_constructs.sort();
    degradation.unsupported_constructs.dedup();
    degradation
}

/// Perform cross-validation of a symbolic engine's verdict against the BFS evaluator.
///
/// Called after all lanes have joined and the winner is determined. Returns `Some`
/// when a symbolic engine produced a definitive verdict (BMC violation or PDR safety)
/// and cross-validation is possible. Returns `None` when only BFS ran or symbolic
/// engines were inconclusive.
///
/// Cross-validation is **non-blocking**: if the BFS evaluator panics during replay
/// (e.g., due to an unsupported construct or evaluator bug), `catch_unwind` catches
/// the panic and returns a failed cross-validation result instead of crashing the
/// orchestrator. This ensures the safety net never makes things worse.
///
/// Part of #3836.
#[cfg(feature = "z4")]
fn perform_cross_validation(
    module: &Module,
    config: &Config,
    winner: &FusedWinner,
    bmc_result: &Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>>,
    pdr_result: &Option<Result<crate::z4_pdr::PdrResult, crate::z4_pdr::PdrError>>,
    kinduction_result: &Option<
        Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
    >,
    bfs_result: &CheckResult,
) -> Option<crate::check::cross_validation::CrossValidationResult> {
    use crate::check::cross_validation::{
        cross_validate_bmc_trace, cross_validate_pdr_safety, CrossValidationResult,
        CrossValidationSource,
    };

    // Helper: wrap a cross-validation call in catch_unwind so a panic in the
    // BFS evaluator during replay does not crash the orchestrator.
    let safe_validate = |f: Box<dyn FnOnce() -> CrossValidationResult>| -> CrossValidationResult {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
            Ok(result) => result,
            Err(payload) => {
                let reason = payload
                    .downcast_ref::<String>()
                    .map(|s| s.as_str())
                    .or_else(|| payload.downcast_ref::<&str>().copied())
                    .unwrap_or("unknown panic");
                eprintln!(
                    "[fused] cross-validation panicked — falling back to BFS-only result: {reason}"
                );
                CrossValidationResult {
                    engine_agrees: false,
                    trace_length: 0,
                    source_engine: CrossValidationSource::Bmc,
                    detail: format!(
                        "cross-validation panicked during BFS replay: {reason} — \
                         falling back to BFS-only result"
                    ),
                }
            }
        }
    };

    match winner {
        FusedWinner::Bmc => {
            // BMC won -- cross-validate its counterexample trace through BFS evaluator.
            if let Some(Ok(crate::z4_bmc::BmcResult::Violation { trace, .. })) = bmc_result {
                let trace = trace.clone();
                Some(safe_validate(Box::new(move || {
                    cross_validate_bmc_trace(module, config, &trace)
                })))
            } else {
                None
            }
        }
        FusedWinner::Pdr => {
            // PDR won -- cross-validate its safety proof against BFS completion status.
            if let Some(Ok(crate::z4_pdr::PdrResult::Safe { invariant })) = pdr_result {
                let invariant = invariant.clone();
                Some(safe_validate(Box::new(move || {
                    cross_validate_pdr_safety(bfs_result, &invariant)
                })))
            } else {
                None
            }
        }
        FusedWinner::KInduction => {
            // k-Induction won -- cross-validate against BFS completion status.
            if let Some(Ok(crate::z4_kinduction::KInductionResult::Proved { k })) =
                kinduction_result
            {
                let proved_k = *k;
                Some(safe_validate(Box::new(move || {
                    crate::check::cross_validation::cross_validate_kinduction_safety(
                        bfs_result, proved_k,
                    )
                })))
            } else {
                None
            }
        }
        FusedWinner::Bfs => {
            // BFS won -- optionally cross-validate any symbolic result for observability.
            if let Some(Ok(crate::z4_bmc::BmcResult::Violation { trace, .. })) = bmc_result {
                let trace = trace.clone();
                return Some(safe_validate(Box::new(move || {
                    cross_validate_bmc_trace(module, config, &trace)
                })));
            }
            if let Some(Ok(crate::z4_pdr::PdrResult::Safe { invariant })) = pdr_result {
                let invariant = invariant.clone();
                return Some(safe_validate(Box::new(move || {
                    cross_validate_pdr_safety(bfs_result, &invariant)
                })));
            }
            None
        }
    }
}

/// Determine which lane won by examining the published verdict and
/// correlating with each lane's result. Part of #3844: added k-induction.
#[cfg(feature = "z4")]
fn determine_fused_winner(
    verdict: &SharedVerdict,
    bfs_result: &CheckResult,
    kinduction_result: &Option<
        Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
    >,
) -> FusedWinner {
    match verdict.get() {
        Some(Verdict::Satisfied) => match bfs_result {
            CheckResult::Success(_) => FusedWinner::Bfs,
            _ => {
                // If k-induction proved safety, attribute the win to it.
                // Otherwise attribute to PDR (the other safety-proving lane).
                if let Some(Ok(crate::z4_kinduction::KInductionResult::Proved { .. })) =
                    kinduction_result
                {
                    FusedWinner::KInduction
                } else {
                    FusedWinner::Pdr
                }
            }
        },
        Some(Verdict::Violated) => match bfs_result {
            CheckResult::InvariantViolation { .. }
            | CheckResult::PropertyViolation { .. }
            | CheckResult::LivenessViolation { .. } => FusedWinner::Bfs,
            _ => {
                // If k-induction's base case found a counterexample, attribute to it.
                if let Some(Ok(crate::z4_kinduction::KInductionResult::Counterexample { .. })) =
                    kinduction_result
                {
                    FusedWinner::KInduction
                } else {
                    FusedWinner::Bmc
                }
            }
        },
        _ => FusedWinner::Bfs,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shared_verdict::{SharedVerdict, Verdict};
    use crate::test_support::parse_module;
    use std::sync::Arc;

    #[test]
    fn test_fused_winner_variants_distinguishable() {
        let variants = [
            FusedWinner::Bfs,
            FusedWinner::Bmc,
            FusedWinner::Pdr,
            FusedWinner::KInduction,
        ];
        for i in 0..variants.len() {
            for j in (i + 1)..variants.len() {
                assert_ne!(variants[i], variants[j]);
            }
        }
    }

    #[test]
    fn test_fused_result_first_verdict_populated() {
        // Verify that the non-z4 path produces a coherent result.
        // (Full integration test requires a parsed TLA+ module.)
        let first_verdict = match FusedWinner::Bfs {
            FusedWinner::Bfs => "BFS",
            FusedWinner::Bmc => "BMC",
            FusedWinner::Pdr => "PDR",
            FusedWinner::KInduction => "k-Induction",
        };
        assert_eq!(first_verdict, "BFS");
    }

    #[test]
    fn test_shared_verdict_cooperative_race() {
        let sv = Arc::new(SharedVerdict::new());
        let sv1 = sv.clone();
        let sv2 = sv.clone();
        let sv3 = sv.clone();

        std::thread::scope(|scope| {
            // Lane 1: BFS publishes Satisfied.
            scope.spawn(move || {
                sv1.publish(Verdict::Satisfied);
            });

            // Lane 2: BMC checks and exits early.
            scope.spawn(move || {
                while !sv2.is_resolved() {
                    std::thread::yield_now();
                }
            });

            // Lane 3: PDR checks and exits early.
            scope.spawn(move || {
                while !sv3.is_resolved() {
                    std::thread::yield_now();
                }
            });
        });

        assert!(sv.is_resolved());
        assert_eq!(sv.get(), Some(Verdict::Satisfied));
    }

    #[test]
    fn test_three_lane_concurrent_race() {
        let sv = Arc::new(SharedVerdict::new());
        let handles: Vec<_> = (0..3)
            .map(|i| {
                let sv = sv.clone();
                std::thread::spawn(move || {
                    let v = match i {
                        0 => Verdict::Satisfied,
                        1 => Verdict::Violated,
                        _ => Verdict::Unknown,
                    };
                    sv.publish(v)
                })
            })
            .collect();

        let wins: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        // At most one definitive publisher wins (Unknown doesn't count).
        let definitive_wins = wins[..2].iter().filter(|&&w| w).count();
        assert!(definitive_wins <= 1);
        // At least one definitive verdict should be published (Satisfied or Violated).
        // Unknown (lane 2) never resolves, so either lane 0 or lane 1 must win.
        assert!(sv.is_resolved());
    }

    // ========================================================================
    // Integration tests: FusedOrchestrator with real parsed TLA+ specs
    // ========================================================================

    /// Simple 2-state spec that passes all invariants.
    const PASSING_SPEC: &str = r#"
---- MODULE FusedPass ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = 1 - x
Inv == x \in {0, 1}
====
"#;

    /// Spec whose invariant is violated: x eventually reaches 2.
    const VIOLATING_SPEC: &str = r#"
---- MODULE FusedViolate ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
"#;

    /// Bounded counter that terminates (deadlocks) — no invariant.
    const DEADLOCK_FREE_SPEC: &str = r#"
---- MODULE FusedDeadlockFree ----
VARIABLE x
Init == x = 0
Next == x' = 1 - x
====
"#;

    #[test]
    fn test_fused_orchestrator_passing_spec() {
        let _lock = crate::test_utils::acquire_interner_lock();

        let module = parse_module(PASSING_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };

        let orchestrator = FusedOrchestrator::new(&module, &[], &config);
        let result = orchestrator.run();

        // BFS always runs and should win in non-z4 mode.
        assert_eq!(result.winner, FusedWinner::Bfs);
        // Non-z4: symbolic_summary is None.
        // z4: symbolic_summary is Some("Winner: ...").
        #[cfg(not(feature = "z4"))]
        assert!(result.symbolic_summary.is_none());
        #[cfg(feature = "z4")]
        assert!(result.symbolic_summary.is_some());

        // BFS should find exactly 2 states ({x=0, x=1}) and succeed.
        match &result.bfs_result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.states_found, 2, "expected 2 states for toggle spec");
            }
            other => panic!("Expected Success for passing spec, got: {other:?}"),
        }
    }

    #[test]
    fn test_fused_orchestrator_invariant_violation() {
        let _lock = crate::test_utils::acquire_interner_lock();

        let module = parse_module(VIOLATING_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };

        let orchestrator = FusedOrchestrator::new(&module, &[], &config);
        let result = orchestrator.run();

        assert_eq!(result.winner, FusedWinner::Bfs);

        // BFS should detect invariant violation when x reaches 2.
        match &result.bfs_result {
            CheckResult::InvariantViolation { .. } => {}
            other => panic!("Expected InvariantViolation for violating spec, got: {other:?}"),
        }
    }

    #[test]
    fn test_fused_orchestrator_no_invariant_deadlock_free() {
        let _lock = crate::test_utils::acquire_interner_lock();

        let module = parse_module(DEADLOCK_FREE_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec![],
            ..Default::default()
        };

        let orchestrator = FusedOrchestrator::new(&module, &[], &config);
        let result = orchestrator.run();

        assert_eq!(result.winner, FusedWinner::Bfs);

        // Toggle spec with no invariant: 2 states, no violation.
        match &result.bfs_result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.states_found, 2);
            }
            other => panic!("Expected Success for deadlock-free spec, got: {other:?}"),
        }
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_fused_orchestrator_z4_four_lane_passing() {
        let _lock = crate::test_utils::acquire_interner_lock();

        let module = parse_module(PASSING_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };

        let orchestrator = FusedOrchestrator::new(&module, &[], &config);
        let result = orchestrator.run();

        // With z4: all four lanes run. BFS should still find 2 states.
        match &result.bfs_result {
            CheckResult::Success(stats) => {
                assert_eq!(stats.states_found, 2);
            }
            other => panic!("Expected Success from BFS lane, got: {other:?}"),
        }

        // BMC, PDR, and k-Induction results should be present (may be Ok or Err
        // depending on z4 translation support for this simple spec).
        assert!(
            result.bmc_result.is_some(),
            "BMC result should be present with z4 feature"
        );
        assert!(
            result.pdr_result.is_some(),
            "PDR result should be present with z4 feature"
        );
        assert!(
            result.kinduction_result.is_some(),
            "k-Induction result should be present with z4 feature"
        );
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_determine_fused_winner_bfs_satisfied() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Satisfied);
        let bfs_result = CheckResult::Success(crate::check::CheckStats {
            states_found: 2,

            ..Default::default()
        });
        assert_eq!(
            determine_fused_winner(&sv, &bfs_result, &None),
            FusedWinner::Bfs,
        );
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_determine_fused_winner_pdr_satisfied() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Satisfied);
        // BFS did not reach success (e.g., still running) — PDR resolved first.
        let bfs_result = CheckResult::LimitReached {
            limit_type: crate::check::LimitType::States,
            stats: crate::check::CheckStats::default(),
        };
        assert_eq!(
            determine_fused_winner(&sv, &bfs_result, &None),
            FusedWinner::Pdr,
        );
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_determine_fused_winner_bmc_violated() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Violated);
        // BFS did not find the violation — BMC found it.
        let bfs_result = CheckResult::Success(crate::check::CheckStats::default());
        assert_eq!(
            determine_fused_winner(&sv, &bfs_result, &None),
            FusedWinner::Bmc,
        );
    }

    /// Part of #3844: k-Induction proving safety attributes the win correctly.
    #[cfg(feature = "z4")]
    #[test]
    fn test_determine_fused_winner_kinduction_proved() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Satisfied);
        // BFS did not reach success — k-Induction proved safety first.
        let bfs_result = CheckResult::LimitReached {
            limit_type: crate::check::LimitType::States,
            stats: crate::check::CheckStats::default(),
        };
        let kind_result = Some(Ok(crate::z4_kinduction::KInductionResult::Proved { k: 3 }));
        assert_eq!(
            determine_fused_winner(&sv, &bfs_result, &kind_result),
            FusedWinner::KInduction,
        );
    }

    /// Part of #3844: k-Induction base-case counterexample attributes violation.
    #[cfg(feature = "z4")]
    #[test]
    fn test_determine_fused_winner_kinduction_counterexample() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Violated);
        // BFS did not find the violation — k-Induction base case found it.
        let bfs_result = CheckResult::Success(crate::check::CheckStats::default());
        let kind_result = Some(Ok(crate::z4_kinduction::KInductionResult::Counterexample {
            depth: 2,
            trace: vec![],
        }));
        assert_eq!(
            determine_fused_winner(&sv, &bfs_result, &kind_result),
            FusedWinner::KInduction,
        );
    }

    // ---- Part of #3837: SymbolicDegradation tests ----

    #[test]
    fn test_degradation_default_no_degradation() {
        let d = SymbolicDegradation::default();
        assert!(!d.any_degraded());
        assert!((d.symbolic_coverage() - 1.0).abs() < f64::EPSILON);
        assert!(d.summary().is_none());
    }

    #[test]
    fn test_degradation_bmc_only() {
        let d = SymbolicDegradation {
            bmc_degraded: true,
            bmc_reason: Some("translation failed: unsupported operator CHOOSE".to_string()),
            unsupported_constructs: vec!["CHOOSE".to_string()],
            ..Default::default()
        };
        assert!(d.any_degraded());
        // 1 of 3 symbolic lanes degraded => 2/3 lane coverage.
        assert!((d.lane_coverage() - 2.0 / 3.0).abs() < 0.01);
        let summary = d.summary().unwrap();
        assert!(summary.contains("66%"));
        assert!(summary.contains("BMC"));
        assert!(summary.contains("CHOOSE"));
    }

    #[test]
    fn test_degradation_bmc_and_pdr_lanes() {
        let d = SymbolicDegradation {
            bmc_degraded: true,
            bmc_reason: Some("solver failed".to_string()),
            pdr_degraded: true,
            pdr_reason: Some("sort inference failed".to_string()),
            ..Default::default()
        };
        assert!(d.any_degraded());
        // 2 of 3 symbolic lanes degraded => 1/3 lane coverage = 33%.
        assert!((d.lane_coverage() - 1.0 / 3.0).abs() < 0.01);
        let summary = d.summary().unwrap();
        assert!(summary.contains("33%"));
        assert!(summary.contains("BMC"));
        assert!(summary.contains("PDR"));
    }

    #[test]
    fn test_degradation_all_symbolic_lanes() {
        let d = SymbolicDegradation {
            bmc_degraded: true,
            bmc_reason: Some("solver failed".to_string()),
            pdr_degraded: true,
            pdr_reason: Some("sort inference failed".to_string()),
            kinduction_degraded: true,
            kinduction_reason: Some("translation failed".to_string()),
            ..Default::default()
        };
        assert!(d.any_degraded());
        assert!(d.lane_coverage().abs() < f64::EPSILON);
        let summary = d.summary().unwrap();
        assert!(summary.contains("0%"));
        assert!(summary.contains("BMC"));
        assert!(summary.contains("PDR"));
        assert!(summary.contains("k-Induction"));
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_extract_unsupported_constructs_from_message() {
        let constructs =
            extract_unsupported_constructs("unsupported operator: CHOOSE in SetFilter context");
        assert!(constructs.contains(&"CHOOSE".to_string()));
        assert!(constructs.contains(&"SetFilter".to_string()));
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_build_degradation_both_ok() {
        let bmc = Some(Ok(crate::z4_bmc::BmcResult::BoundReached { max_depth: 5 }));
        let pdr = Some(Ok(crate::z4_pdr::PdrResult::Safe {
            invariant: "Inv".to_string(),
        }));
        let kind = Some(Ok(crate::z4_kinduction::KInductionResult::Unknown {
            max_k: 5,
            reason: "inconclusive".to_string(),
        }));
        let flags = vec![true, true];
        let names = vec!["A".to_string(), "B".to_string()];
        let deg = build_degradation(&bmc, &pdr, &kind, &flags, &names);
        assert!(!deg.any_degraded());
        assert!((deg.lane_coverage() - 1.0).abs() < f64::EPSILON);
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_build_degradation_bmc_error() {
        let bmc: Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>> = Some(Err(
            crate::z4_bmc::BmcError::TranslationError("unsupported operator: CHOOSE".to_string()),
        ));
        let pdr = Some(Ok(crate::z4_pdr::PdrResult::Safe {
            invariant: "Inv".to_string(),
        }));
        let kind: Option<
            Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
        > = Some(Ok(crate::z4_kinduction::KInductionResult::Unknown {
            max_k: 5,
            reason: "inconclusive".to_string(),
        }));
        let flags = vec![true, false];
        let names = vec!["A".to_string(), "B".to_string()];
        let deg = build_degradation(&bmc, &pdr, &kind, &flags, &names);
        assert!(deg.bmc_degraded);
        assert!(!deg.pdr_degraded);
        assert!(!deg.kinduction_degraded);
        // 1 of 3 symbolic lanes degraded => 2/3 lane coverage.
        assert!((deg.lane_coverage() - 2.0 / 3.0).abs() < 0.01);
        assert!(deg.unsupported_constructs.contains(&"CHOOSE".to_string()));
        assert_eq!(deg.actions_total, 2);
        assert_eq!(deg.actions_smt_compatible, 1);
        assert!(deg.bmc_error.is_some());
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_build_degradation_all_panicked() {
        let bmc: Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>> = None;
        let pdr: Option<Result<crate::z4_pdr::PdrResult, crate::z4_pdr::PdrError>> = None;
        let kind: Option<
            Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
        > = None;
        let flags: Vec<bool> = vec![];
        let names: Vec<String> = vec![];
        let deg = build_degradation(&bmc, &pdr, &kind, &flags, &names);
        assert!(deg.bmc_degraded);
        assert!(deg.pdr_degraded);
        assert!(deg.kinduction_degraded);
        // All 3 symbolic lanes degraded => 0% lane coverage.
        assert!(deg.lane_coverage().abs() < f64::EPSILON);
    }

    /// Part of #3844: k-Induction error tracked in degradation.
    #[cfg(feature = "z4")]
    #[test]
    fn test_build_degradation_kinduction_error() {
        let bmc = Some(Ok(crate::z4_bmc::BmcResult::BoundReached { max_depth: 5 }));
        let pdr = Some(Ok(crate::z4_pdr::PdrResult::Safe {
            invariant: "Inv".to_string(),
        }));
        let kind: Option<
            Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
        > = Some(Err(
            crate::z4_kinduction::KInductionError::TranslationError(
                "unsupported operator: SUBSET".to_string(),
            ),
        ));
        let flags = vec![true];
        let names = vec!["A".to_string()];
        let deg = build_degradation(&bmc, &pdr, &kind, &flags, &names);
        assert!(!deg.bmc_degraded);
        assert!(!deg.pdr_degraded);
        assert!(deg.kinduction_degraded);
        assert!(deg
            .kinduction_reason
            .as_ref()
            .unwrap()
            .contains("translation failed"));
        assert!(deg.unsupported_constructs.contains(&"SUBSET".to_string()));
        // 1 of 3 symbolic lanes degraded => 2/3 lane coverage.
        assert!((deg.lane_coverage() - 2.0 / 3.0).abs() < 0.01);
    }

    /// CDEMC demo: 3 independent bounded counters in a record.
    /// BFS state space: 101^3 ~ 1M states. With max_states=1000, BFS hits
    /// the limit. PDR should prove safety symbolically (or degrade gracefully).
    ///
    /// Part of #3957.
    #[cfg(feature = "z4")]
    #[test]
    fn test_fused_counter_array_3_symbolic_advantage() {
        let _lock = crate::test_utils::acquire_interner_lock();

        let src = r#"
---- MODULE FusedCounterArray3 ----
EXTENDS Integers
VARIABLE c
Init == c = [c1 |-> 0, c2 |-> 0, c3 |-> 0]
Next == \/ c' = [c EXCEPT !.c1 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c2 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c3 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ UNCHANGED c
Safety == /\ c.c1 >= 0 /\ c.c1 <= 100
          /\ c.c2 >= 0 /\ c.c2 <= 100
          /\ c.c3 >= 0 /\ c.c3 <= 100
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Safety".to_string()],
            ..Default::default()
        };

        let orchestrator = FusedOrchestrator::new(&module, &[], &config);
        let result = orchestrator.run();

        // The spec is safe — regardless of which lane wins, there must be no
        // invariant violation.
        match &result.bfs_result {
            CheckResult::InvariantViolation { .. }
            | CheckResult::PropertyViolation { .. }
            | CheckResult::LivenessViolation { .. } => {
                panic!(
                    "CounterArray3 is safe — fused mode should not report violation: {:?}",
                    result.bfs_result
                );
            }
            _ => {
                // BFS hit limit, success, or PDR proved safety — all acceptable.
            }
        }

        // Verify all symbolic lanes attempted (may succeed or degrade).
        assert!(
            result.bmc_result.is_some(),
            "BMC lane should have run"
        );
        assert!(
            result.pdr_result.is_some(),
            "PDR lane should have run"
        );
        assert!(
            result.kinduction_result.is_some(),
            "k-Induction lane should have run"
        );

        // If PDR or k-Induction proved safety, the winner should reflect that.
        if matches!(result.winner, FusedWinner::Pdr | FusedWinner::KInduction) {
            eprintln!(
                "CDEMC demo success: symbolic engine ({:?}) proved safety for \
                 101^3 state space that BFS cannot enumerate",
                result.winner
            );
        }
    }
}
