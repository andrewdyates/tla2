// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine dispatch and SingleLoop fallback helpers.
//!
//! Extracted from portfolio mod.rs — these free functions run individual CHC
//! engines with SingleLoop multi-predicate fallback and back-translation.

use crate::bmc::BmcSolver;
use crate::cegar::CegarEngine;
use crate::dar::DarSolver;
use crate::decomposition::DecompositionSolver;
use crate::engine_result::ChcEngineResult;
use crate::imc::ImcSolver;
use crate::kind::{KindConfig, KindSolver};
use crate::lawi::LawiSolver;
use crate::pdkind::{PdkindConfig, PdkindSolver};
use crate::pdr::{InvariantModel, PdrSolver};
use crate::single_loop::SingleLoopTransformation;
use crate::tpa::{TpaConfig, TpaResult, TpaSolver};
use crate::transition_system::TransitionSystem;
use crate::trl::{TrlConfig, TrlSolver};
use crate::{ChcProblem, ChcVar};
use std::time::Duration;
use z4_sat::TlaTraceable;

use super::{EngineConfig, EngineResult};

/// Back-translate a `ChcEngineResult` from a SingleLoop-encoded engine run.
///
/// Shared back-translation path for Kind and TRL when they solve
/// multi-predicate problems via SingleLoop encoding (#7946):
/// - **Safe**: extract witness via `SingleLoopSafeWitness::from_trl`, then
///   translate to per-predicate interpretations.
/// - **Unsafe**: suppressed (no back-translation implemented).
/// - **Unknown/NotApplicable**: passed through unchanged.
fn translate_singleloop_result(
    result: ChcEngineResult,
    problem: &ChcProblem,
    tx: &SingleLoopTransformation,
    state_vars: &[ChcVar],
    engine_name: &str,
    idx: usize,
    verbose: bool,
) -> ChcEngineResult {
    match result {
        ChcEngineResult::Safe(ref model) => {
            match super::singleloop_safe::SingleLoopSafeWitness::from_trl(model, state_vars) {
                Some(witness) => {
                    match super::singleloop_safe::translate_singleloop_safe(problem, tx, &witness) {
                        Some(multi_model) => {
                            if verbose {
                                safe_eprintln!(
                                    "Portfolio: Engine {} ({}) SingleLoop Safe back-translated",
                                    idx,
                                    engine_name
                                );
                            }
                            ChcEngineResult::Safe(multi_model)
                        }
                        None => {
                            if verbose {
                                safe_eprintln!(
                                    "Portfolio: Engine {} ({}) SingleLoop back-translation failed",
                                    idx,
                                    engine_name
                                );
                            }
                            ChcEngineResult::Unknown
                        }
                    }
                }
                None => {
                    if verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) SingleLoop witness extraction failed",
                            idx,
                            engine_name
                        );
                    }
                    ChcEngineResult::Unknown
                }
            }
        }
        ChcEngineResult::Unsafe(_) => {
            if verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} ({}) SingleLoop Unsafe suppressed (no back-translation)",
                    idx,
                    engine_name
                );
            }
            ChcEngineResult::Unknown
        }
        other => other,
    }
}

/// Run PDKind with SingleLoop fallback for multi-predicate problems.
///
/// For single-predicate problems, runs PDKind directly. For multi-predicate
/// problems, PDKind's internal SingleLoop fallback (via
/// `extract_transition_system_with_singleloop_fallback`) handles the encoding
/// with Int location variables that pass the interpolation sort guard.
pub(super) fn run_pdkind_with_singleloop(
    problem: &ChcProblem,
    config: PdkindConfig,
    verbose: bool,
) -> ChcEngineResult {
    if verbose && problem.predicates().len() > 1 {
        safe_eprintln!(
            "Portfolio: PDKIND: multi-predicate ({} preds), using SingleLoop encoding",
            problem.predicates().len()
        );
    }
    PdkindSolver::new(problem.clone(), config).solve()
}

/// Run Kind with SingleLoop fallback for multi-predicate problems.
///
/// For single-predicate problems, runs Kind directly. For multi-predicate
/// linear problems, applies SingleLoopTransformation to produce a synthetic
/// single-predicate ChcProblem, runs Kind on that, and back-translates
/// Safe results to per-predicate interpretations.
///
/// Unlike PDKind, Kind does NOT use interpolation during solving (only for
/// optional k-to-1 conversion), so Bool location variables from SingleLoop
/// are acceptable. This makes Kind a viable multi-predicate engine where
/// PDKind fails due to the Bool sort guard (#6500).
pub(super) fn run_kind_with_singleloop_fallback(
    problem: ChcProblem,
    mut config: KindConfig,
    idx: usize,
    verbose: bool,
) -> ChcEngineResult {
    if verbose {
        config.base.verbose = true;
    }

    if problem.predicates().len() <= 1 {
        let mut solver = KindSolver::new(problem, config);
        solver.maybe_enable_tla_trace_from_env();
        return solver.solve();
    }

    // Multi-predicate: apply SingleLoop encoding.
    let mut tx = SingleLoopTransformation::new(problem.clone());
    let sys = match tx.transform() {
        Some(sys) => sys,
        None => {
            if verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} (Kind) SingleLoop transform failed (non-linear)",
                    idx
                );
            }
            return ChcEngineResult::Unknown;
        }
    };

    if verbose {
        safe_eprintln!(
            "Portfolio: Engine {} (Kind) using SingleLoop encoding ({} state vars)",
            idx,
            sys.state_vars.len()
        );
    }

    let synthetic_problem = sys.to_chc_problem();
    let state_vars = sys.state_vars.clone();

    let mut solver = KindSolver::new(synthetic_problem, config);
    solver.maybe_enable_tla_trace_from_env();
    let result = solver.solve();

    translate_singleloop_result(result, &problem, &tx, &state_vars, "Kind", idx, verbose)
}

/// Compatibility wrapper for test callers.
///
/// Delegates to `singleloop_safe::SingleLoopSafeWitness::from_trl` +
/// `singleloop_safe::translate_singleloop_safe`. Tests that call this
/// function exercise the same code path as the production TRL adapter.
pub(super) fn translate_trl_singleloop_safe_model(
    problem: &ChcProblem,
    tx: &SingleLoopTransformation,
    state_vars: &[ChcVar],
    model: &InvariantModel,
) -> Option<InvariantModel> {
    let witness = super::singleloop_safe::SingleLoopSafeWitness::from_trl(model, state_vars)?;
    super::singleloop_safe::translate_singleloop_safe(problem, tx, &witness)
}

/// Run TRL engine with SingleLoop fallback for multi-predicate problems.
///
/// Attempts direct TransitionSystem extraction. Falls back to SingleLoop
/// encoding for linear multi-predicate problems.
pub(super) fn run_trl_with_singleloop_fallback(
    problem: ChcProblem,
    config: TrlConfig,
    idx: usize,
    verbose: bool,
) -> ChcEngineResult {
    if problem.has_array_sorts() {
        if verbose {
            safe_eprintln!(
                "Portfolio: Engine {} (TRL) skipped: array-sorted CHC is unsupported",
                idx
            );
        }
        problem.iterative_drop();
        return ChcEngineResult::Unknown;
    }

    let (ts, single_loop_tx, single_loop_state_vars) =
        match TransitionSystem::from_chc_problem(&problem) {
            Ok(ts) => (Ok(ts), None, None),
            Err(_) => {
                let mut tx = SingleLoopTransformation::new(problem.clone());
                match tx.transform() {
                Some(sys) => {
                    let state_vars = sys.state_vars.clone();
                    (
                        Ok(TransitionSystem::new(
                        problem
                            .predicates()
                            .first()
                            .map_or(crate::PredicateId::new(0), |p| p.id),
                        sys.state_vars,
                        sys.init,
                        sys.transition,
                        sys.query,
                        )),
                        Some(tx),
                        Some(state_vars),
                    )
                }
                None => (
                    Err(
                        "Not a single-predicate TS and not linear (SingleLoop transform failed)"
                            .to_string(),
                    ),
                    None,
                    None,
                ),
            }
            }
        };

    let result = match ts {
        Ok(ts) => {
            let mut solver = TrlSolver::new(ts, config);
            let result = solver.solve();
            if let (Some(tx), Some(state_vars)) =
                (single_loop_tx.as_ref(), single_loop_state_vars.as_ref())
            {
                translate_singleloop_result(result, &problem, tx, state_vars, "TRL", idx, verbose)
            } else {
                result
            }
        }
        Err(err) => {
            if verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} (TRL) TS extraction failed: {}",
                    idx,
                    err
                );
            }
            ChcEngineResult::Unknown
        }
    };

    problem.iterative_drop();
    result
}

/// Run TPA engine with SingleLoop fallback for multi-predicate problems.
///
/// For single-predicate problems, runs TPA directly (returns `EngineResult::Tpa`).
/// For multi-predicate linear problems, applies SingleLoopTransformation to produce
/// a synthetic single-predicate transition system, runs TPA on that, and
/// back-translates Safe invariants to per-predicate interpretations.
///
/// Mirrors `run_trl_with_singleloop_fallback` and `run_pdkind_with_singleloop`.
/// Golem's TPA engine handles multi-predicate CHC via the same encoding.
pub(super) fn run_tpa_with_singleloop_fallback(
    problem: &ChcProblem,
    config: TpaConfig,
    verbose: bool,
) -> EngineResult {
    // Single-predicate: run directly, returning TpaResult for native conversion.
    if problem.predicates().len() <= 1 {
        return EngineResult::Tpa(TpaSolver::new(problem.clone(), config).solve());
    }

    // Multi-predicate: apply SingleLoop encoding.
    let mut tx = SingleLoopTransformation::new(problem.clone());
    let sys = match tx.transform() {
        Some(sys) => sys,
        None => {
            if verbose {
                safe_eprintln!("Portfolio: TPA: SingleLoop transform failed (non-linear)");
            }
            return EngineResult::Tpa(TpaResult::Unknown);
        }
    };

    // Build synthetic problem (borrows sys) then consume sys for TransitionSystem.
    let synthetic_problem = sys.to_chc_problem();
    // Save state_vars for back-translation before partially consuming sys.
    let state_vars = sys.state_vars.clone();
    let pred_id = problem
        .predicates()
        .first()
        .map_or(crate::PredicateId::new(0), |p| p.id);
    let ts = TransitionSystem::new(pred_id, sys.state_vars, sys.init, sys.transition, sys.query);

    // Set per-power timeout to 10s for SingleLoop encodings.
    // The previous 2s override was too tight: SingleLoop formulas are larger
    // (location + argument variables) so SMT queries need more time per power
    // level.  With a 2s timeout, every query returns Unknown and TPA learns
    // nothing.  The default 30s is too generous — TPA can only check ~1 power
    // level per 30s budget.  10s allows queries to complete while permitting
    // multiple power levels within typical portfolio budgets (#4751).
    let mut sl_config = config;
    sl_config.timeout_per_power = Duration::from_secs(10);
    sl_config.verbose_level = u8::from(verbose);

    let tpa_result = TpaSolver::new(synthetic_problem, sl_config)
        .with_transition_system(ts)
        .solve();

    // Back-translate multi-predicate results via shared adapter.
    match tpa_result {
        TpaResult::Safe { invariant, .. } => {
            if let Some(inv_expr) = invariant {
                let witness =
                    super::singleloop_safe::SingleLoopSafeWitness::from_tpa(&inv_expr, &state_vars);
                let engine_result =
                    super::singleloop_safe::translate_singleloop_safe(problem, &tx, &witness)
                        .map_or(ChcEngineResult::Unknown, ChcEngineResult::Safe);
                EngineResult::Unified(engine_result, "TPA")
            } else {
                // Safe but no invariant formula — return as Safe with empty model.
                EngineResult::Unified(ChcEngineResult::Safe(InvariantModel::new()), "TPA")
            }
        }
        TpaResult::Unsafe { .. } => {
            // SingleLoop Unsafe cannot be validated for multi-predicate problems.
            if verbose {
                safe_eprintln!(
                    "Portfolio: TPA SingleLoop Unsafe suppressed (multi-pred validation unsupported)"
                );
            }
            EngineResult::Unified(ChcEngineResult::Unknown, "TPA")
        }
        TpaResult::Unknown => EngineResult::Unified(ChcEngineResult::Unknown, "TPA"),
    }
}

/// Run a single CHC engine on a problem and return its result.
///
/// Centralizes the engine dispatch logic previously duplicated across
/// `solve_parallel()`, `solve_sequential()` (threaded), and
/// `solve_sequential()` (inline). Each engine is constructed, invoked,
/// and its result wrapped in the appropriate `EngineResult` variant.
pub(super) fn run_engine(
    engine_config: EngineConfig,
    problem: ChcProblem,
    idx: usize,
    verbose: bool,
) -> EngineResult {
    let name = engine_config.name();
    if verbose {
        safe_eprintln!("Portfolio: Engine {} ({}) starting", idx, name);
    }

    let result = match engine_config {
        EngineConfig::Pdr(config) => {
            // Propagate Z4_TRACE_FILE for TLA trace support (#2585).
            let config = config.with_tla_trace_from_env();
            EngineResult::Unified(PdrSolver::solve_problem(&problem, config), "PDR")
        }
        EngineConfig::Bmc(mut config) => {
            // Propagate portfolio verbose flag to BMC engine (#5848: diagnosis)
            if verbose {
                config.base.verbose = true;
            }
            EngineResult::Unified(BmcSolver::new(problem, config).solve(), "BMC")
        }
        EngineConfig::Pdkind(config) => EngineResult::Unified(
            run_pdkind_with_singleloop(&problem, config, verbose),
            "PDKIND",
        ),
        EngineConfig::Imc(config) => {
            EngineResult::Unified(ImcSolver::new(problem, config).solve(), "IMC")
        }
        EngineConfig::Lawi(config) => {
            EngineResult::Unified(LawiSolver::new(problem, config).solve(), "LAWI")
        }
        EngineConfig::Dar(config) => {
            EngineResult::Unified(DarSolver::new(problem, config).solve(), "DAR")
        }
        EngineConfig::Tpa(config) => run_tpa_with_singleloop_fallback(&problem, config, verbose),
        EngineConfig::Trl(config) => EngineResult::Unified(
            run_trl_with_singleloop_fallback(problem, config, idx, verbose),
            "TRL",
        ),
        EngineConfig::Kind(config) => EngineResult::Unified(
            run_kind_with_singleloop_fallback(problem, config, idx, verbose),
            "Kind",
        ),
        EngineConfig::Decomposition(config) => EngineResult::Unified(
            DecompositionSolver::new(problem, config).solve(),
            "Decomposition",
        ),
        EngineConfig::Cegar(config) => {
            EngineResult::Cegar(CegarEngine::new(problem, config).solve())
        }
    };

    if verbose {
        safe_eprintln!(
            "Portfolio: Engine {} ({}) finished: {}",
            idx,
            name,
            result.summary()
        );
    }

    result
}
