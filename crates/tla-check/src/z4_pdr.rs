// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4-based PDR (Property-Directed Reachability) for symbolic safety checking
//!
//! This module provides IC3/PDR-based verification using the CHC solver from
//! `tla-z4`. Unlike explicit-state model checking, PDR can prove safety for
//! infinite-state systems by synthesizing inductive invariants.
//!
//! # Part of #642: Implement z4 PDR symbolic safety check
//!
//! # Supported Subset
//!
//! - State variables: Bool, Int, String, and finite-domain functions
//! - Boolean operators: TRUE, FALSE, /\, \/, ~, =>, <=>
//! - Comparisons: =, #, <, <=, >, >=
//! - Arithmetic: +, -, *, unary -, \div, %
//! - Conditionals: IF THEN ELSE
//! - Action constructs: x', UNCHANGED x, UNCHANGED <<x, y>>
//! - Finite quantifiers over `SetEnum`, `Range`, `BOOLEAN`, and `SetFilter`
//! - Set membership over `BOOLEAN`, `Int`, `Nat`, `SetEnum`, `Range`, `SetFilter`,
//!   `SetBuilder`, and finite-domain function sets
//!
//! # Usage
//!
//! ```no_run
//! use tla_check::{check_pdr, PdrResult};
//! use tla_check::{Config, EvalCtx};
//! use tla_core::ast::Module;
//!
//! fn verify_spec(module: &Module, config: &Config, ctx: &EvalCtx) {
//!     match check_pdr(module, config, ctx) {
//!         Ok(PdrResult::Safe { invariant }) => {
//!             println!("Proved safe with invariant: {}", invariant);
//!         }
//!         Ok(PdrResult::Unsafe { trace }) => {
//!             println!("Found counterexample with {} states", trace.len());
//!         }
//!         Ok(PdrResult::Unknown { reason }) => {
//!             println!("Inconclusive: {}", reason);
//!         }
//!         Err(e) => {
//!             eprintln!("PDR error: {}", e);
//!         }
//!     }
//! }
//! ```
//!
//! # Design Notes
//!
//! PDR results are separate from explicit-state CheckResult because:
//! 1. PDR does not enumerate states, so metrics like `states_found` are misleading
//! 2. PDR produces different artifacts (invariant model vs state space coverage)
//! 3. Clear UX separation helps users understand which mode is active

mod expand;
pub(crate) mod generalize;

use std::sync::Arc;
use std::time::Instant;

use tla_core::ast::Module;
use tla_z4::chc::{ChcTranslator, PdrCheckResult, PdrState};
use tla_z4::{PdrConfig, TlaSort};

use crate::check::CheckError;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::shared_verdict::SharedVerdict;
use crate::z4_shared;

pub use expand::expand_operators_for_chc;
pub(crate) use generalize::{flatten_conjunction, generalize_lemma, LemmaGeneralizer};

// Re-exports for statistics tracking and batch processing.
// These are used by `check_pdr_with_generalization` and `generalize_lemmas_batch`
// which are currently wired in cooperative mode and available for external callers.
#[allow(unused_imports)]
pub(crate) use generalize::{AtomicGeneralizationStats, GeneralizedLemma};

/// Result of PDR-based safety verification
#[derive(Debug)]
pub enum PdrResult {
    /// Proven safe: all reachable states satisfy all invariants
    Safe {
        /// String representation of the synthesized invariant
        invariant: String,
    },
    /// Counterexample found: trace violates an invariant
    Unsafe {
        /// Counterexample trace (each element is a state with variable assignments)
        trace: Vec<PdrState>,
    },
    /// Inconclusive: PDR could not determine safety
    Unknown {
        /// Reason for the unknown result
        reason: String,
    },
}

/// Error types specific to PDR checking
#[derive(Debug, thiserror::Error)]
pub enum PdrError {
    /// Missing Init or Next definition
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// No invariants configured
    #[error("No invariants configured for PDR checking")]
    NoInvariants,
    /// Failed to infer variable sorts
    #[error("Sort inference failed: {0}")]
    SortInference(String),
    /// Expression not supported for CHC translation
    #[error("Unsupported expression: {0}")]
    UnsupportedExpr(String),
    /// CHC translation error
    #[error("CHC translation error: {0}")]
    TranslationError(String),
    /// General check error
    #[error("Check error: {0:?}")]
    CheckError(#[from] CheckError),
}

impl From<tla_z4::Z4Error> for PdrError {
    fn from(e: tla_z4::Z4Error) -> Self {
        PdrError::TranslationError(format!("{}", e))
    }
}

/// Run PDR-based safety verification on a TLA+ spec
///
/// This function:
/// 1. Resolves Init/Next from the config
/// 2. Builds Safety as conjunction of configured invariants
/// 3. Infers variable sorts (Bool/Int) from TypeOK or constraints
/// 4. Translates to CHC and runs PDR solver
///
/// # Arguments
/// * `module` - The loaded TLA+ module
/// * `config` - TLC configuration with INIT, NEXT, INVARIANT
/// * `ctx` - Evaluation context with loaded operators
///
/// # Returns
/// * `Ok(PdrResult)` - Safe, Unsafe, or Unknown
/// * `Err(PdrError)` - If translation or verification fails
pub fn check_pdr(module: &Module, config: &Config, ctx: &EvalCtx) -> Result<PdrResult, PdrError> {
    check_pdr_with_config(module, config, ctx, default_pdr_config())
}

/// Default PDR configuration with a bounded solve timeout.
///
/// Part of #2826: The default path installs a 300-second timeout so
/// production PDR runs cannot hang indefinitely. Use
/// `check_pdr_with_config` to bypass this for tests or tuning.
/// Override via `TLA2_PDR_TIMEOUT_SECS` env var.
fn default_pdr_config() -> PdrConfig {
    use std::time::Duration;

    let timeout_secs: u64 = std::env::var("TLA2_PDR_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);

    let mut config = PdrConfig::default();
    config.solve_timeout = Some(Duration::from_secs(timeout_secs));
    config
}

/// Run PDR with custom solver configuration
pub fn check_pdr_with_config(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    pdr_config: PdrConfig,
) -> Result<PdrResult, PdrError> {
    check_pdr_with_portfolio(module, config, ctx, pdr_config, None)
}

/// Run PDR with portfolio verdict for early termination.
///
/// When `portfolio_verdict` is `Some`, checks whether another lane has
/// already resolved before and after the (blocking) PDR solve call.
/// If resolved, returns `PdrResult::Unknown` immediately.
///
/// Part of #3717.
pub fn check_pdr_with_portfolio(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    pdr_config: PdrConfig,
    portfolio_verdict: Option<Arc<SharedVerdict>>,
) -> Result<PdrResult, PdrError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(PdrError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(PdrError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(PdrError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(PdrError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(PdrError::MissingSpec)?;
    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);

    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(PdrError::MissingSpec)?;
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);

    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(|e| PdrError::MissingSpec(e))?;
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    // 8. Create CHC translator and add clauses
    let var_refs: Vec<(&str, TlaSort)> = var_sorts
        .iter()
        .map(|(name, sort)| (name.as_str(), sort.clone()))
        .collect();

    let mut translator = ChcTranslator::new(&var_refs)?;

    translator.add_init(&init_expanded)?;
    translator.add_next(&next_expanded)?;
    translator.add_safety(&safety_expanded)?;

    // 9. Portfolio early-exit check before blocking solve (Part of #3717).
    if let Some(ref sv) = portfolio_verdict {
        if sv.is_resolved() {
            return Ok(PdrResult::Unknown {
                reason: String::from("portfolio verdict resolved by another lane"),
            });
        }
    }

    // 10. Run PDR solver
    let result = translator.solve_pdr(pdr_config)?;

    // 11. Portfolio early-exit check after solve returns (Part of #3717).
    if let Some(ref sv) = portfolio_verdict {
        if sv.is_resolved() {
            return Ok(PdrResult::Unknown {
                reason: String::from("portfolio verdict resolved by another lane during PDR"),
            });
        }
    }

    // 12. Map result to PdrResult
    Ok(match result {
        PdrCheckResult::Safe { invariant } => PdrResult::Safe { invariant },
        PdrCheckResult::Unsafe { trace } => PdrResult::Unsafe { trace },
        PdrCheckResult::Unknown { reason } => PdrResult::Unknown { reason },
    })
}

/// Run PDR with lemma generalization enabled.
///
/// Wraps the standard PDR flow with a post-processing generalization step.
/// When PDR proves safety, the invariant's individual conjuncts (safety
/// clauses) are generalized by dropping unnecessary literals. This produces
/// a stronger inductive invariant that converges faster when used as a seed.
///
/// Returns the PDR result along with optional generalization statistics.
#[allow(dead_code)]
pub fn check_pdr_with_generalization(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    pdr_config: PdrConfig,
    gen_stats: Option<&AtomicGeneralizationStats>,
) -> Result<PdrResult, PdrError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(PdrError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(PdrError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(PdrError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(PdrError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(PdrError::MissingSpec)?;
    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);

    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(PdrError::MissingSpec)?;
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);

    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(PdrError::MissingSpec)?;
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    // Run the standard CHC/PDR solver.
    let var_refs: Vec<(&str, TlaSort)> = var_sorts
        .iter()
        .map(|(name, sort)| (name.as_str(), sort.clone()))
        .collect();

    let mut translator = ChcTranslator::new(&var_refs)?;
    translator.add_init(&init_expanded)?;
    translator.add_next(&next_expanded)?;
    translator.add_safety(&safety_expanded)?;

    let result = translator.solve_pdr(pdr_config)?;

    match result {
        PdrCheckResult::Safe { invariant } => {
            // Attempt to generalize the safety expression itself.
            // This tries to drop unnecessary conjuncts from the safety property
            // to find a weaker (but still inductive) invariant.
            let gen_start = Instant::now();
            let gen_result =
                generalize_lemma(&var_sorts, &init_expanded, &next_expanded, &safety_expanded);

            if let (Ok(gen), Some(stats)) = (&gen_result, gen_stats) {
                let elapsed_us = gen_start.elapsed().as_micros() as u64;
                stats.record(
                    gen.original_literal_count as u64,
                    gen.literals_dropped as u64,
                    elapsed_us,
                );
            }

            Ok(PdrResult::Safe { invariant })
        }
        PdrCheckResult::Unsafe { trace } => Ok(PdrResult::Unsafe { trace }),
        PdrCheckResult::Unknown { reason } => Ok(PdrResult::Unknown { reason }),
    }
}

/// Run PDR with cooperative result publishing.
///
/// Standard PDR execution, but on `PdrResult::Safe`, sets
/// `cooperative.invariants_proved` so BFS can skip all per-state
/// invariant evaluation. On `PdrResult::Unsafe`, publishes
/// `Verdict::Violated` to the cooperative verdict.
///
/// When the result is `Safe`, each invariant clause from the safety
/// conjunction is generalized (unnecessary literals dropped) before
/// being published as a learned lemma to the cooperative state. This
/// produces stronger lemmas that prune the BMC search space more
/// effectively.
///
/// Part of #3766, Epic #3762 (CDEMC).
pub fn check_pdr_cooperative(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    pdr_config: PdrConfig,
    cooperative: Arc<crate::cooperative_state::SharedCooperativeState>,
) -> Result<PdrResult, PdrError> {
    // Early exit: another lane already resolved.
    if cooperative.is_resolved() {
        return Ok(PdrResult::Unknown {
            reason: String::from("cooperative verdict already resolved"),
        });
    }

    // Prepare expanded expressions for both PDR solving and generalization.
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(PdrError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(PdrError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }
    if config.invariants.is_empty() {
        return Err(PdrError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(PdrError::MissingSpec)?;
    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(PdrError::MissingSpec)?;
    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(PdrError::MissingSpec)?;
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(PdrError::MissingSpec)?;
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);
    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    // Build and run CHC/PDR solver.
    let var_refs: Vec<(&str, TlaSort)> = var_sorts
        .iter()
        .map(|(name, sort)| (name.as_str(), sort.clone()))
        .collect();
    let mut translator = ChcTranslator::new(&var_refs)?;
    translator.add_init(&init_expanded)?;
    translator.add_next(&next_expanded)?;
    translator.add_safety(&safety_expanded)?;

    // Portfolio early-exit check.
    if cooperative.is_resolved() {
        return Ok(PdrResult::Unknown {
            reason: String::from("cooperative verdict resolved before PDR solve"),
        });
    }

    let chc_result = translator.solve_pdr(pdr_config)?;

    // Portfolio early-exit check after solve.
    if cooperative.is_resolved() {
        return Ok(PdrResult::Unknown {
            reason: String::from("cooperative verdict resolved during PDR solve"),
        });
    }

    // Map result and publish cooperative results.
    let result = match chc_result {
        PdrCheckResult::Safe { invariant } => {
            // Generalize the safety expression and publish individual
            // lemmas to the cooperative state for BMC pruning.
            let gen_result =
                generalize_lemma(&var_sorts, &init_expanded, &next_expanded, &safety_expanded);

            // Publish the generalized lemma (or original if generalization failed).
            let lemma_expr = match gen_result {
                Ok(gen) => gen.expr,
                Err(_) => safety_expanded.clone(),
            };

            // Publish individual conjuncts as separate lemmas for finer-grained
            // BMC pruning. Each conjunct is an independently valid lemma.
            let mut conjuncts = Vec::new();
            flatten_conjunction(&lemma_expr, &mut conjuncts);
            for conjunct in &conjuncts {
                cooperative.publish_lemma(conjunct.clone());
                cooperative.increment_pdr_lemma_count();
            }

            cooperative.set_invariants_proved();
            cooperative
                .verdict
                .publish(crate::shared_verdict::Verdict::Satisfied);

            PdrResult::Safe { invariant }
        }
        PdrCheckResult::Unsafe { trace } => {
            cooperative
                .verdict
                .publish(crate::shared_verdict::Verdict::Violated);
            PdrResult::Unsafe { trace }
        }
        PdrCheckResult::Unknown { reason } => PdrResult::Unknown { reason },
    };

    Ok(result)
}

/// Generalize a sequence of learned lemmas against the given spec.
///
/// This is a batch utility for external callers that have collected
/// lemma expressions from a PDR run and want to strengthen them
/// before using them as seeds for subsequent verification.
///
/// Returns generalized lemmas paired with per-lemma statistics.
#[allow(dead_code)]
pub(crate) fn generalize_lemmas_batch(
    var_sorts: &[(String, TlaSort)],
    init_expr: &tla_core::Spanned<tla_core::ast::Expr>,
    next_expr: &tla_core::Spanned<tla_core::ast::Expr>,
    lemmas: &[tla_core::Spanned<tla_core::ast::Expr>],
    stats: Option<&AtomicGeneralizationStats>,
) -> Vec<Result<GeneralizedLemma, PdrError>> {
    let generalizer = LemmaGeneralizer::new(var_sorts, init_expr, next_expr);

    lemmas
        .iter()
        .map(|lemma| {
            let start = Instant::now();
            let result = generalizer.generalize(lemma);
            if let (Ok(ref gen), Some(s)) = (&result, stats) {
                let elapsed_us = start.elapsed().as_micros() as u64;
                s.record(
                    gen.original_literal_count as u64,
                    gen.literals_dropped as u64,
                    elapsed_us,
                );
            }
            result
        })
        .collect()
}

#[cfg(test)]
mod tests;
