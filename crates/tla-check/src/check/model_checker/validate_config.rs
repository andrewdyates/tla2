// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Config-time operator validation for model checker setup.
//!
//! Mirrors TLC `SpecProcessor.processConfigInvariants/Properties/Constraints/
//! ActionConstraints` (SpecProcessor.java). Validates existence, arity, and
//! expression level for all config-referenced operators before BFS begins.
//!
//! Part of #2573 (sequential) and #2675 (parallel parity).
//!
//! Standalone free functions take `&EvalCtx` + config slices so both the
//! sequential `ModelChecker` and `ParallelChecker` can share validation logic
//! without duplication. The `ModelChecker` methods delegate to these functions.

use super::super::api::CheckResult;
use super::super::check_error::CheckError;
use super::mc_struct::ModelChecker;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::ConfigCheckError;
use tla_core::expr_contains_temporal_v;

// ---------------------------------------------------------------------------
// Standalone validation functions (shared by sequential + parallel)
// ---------------------------------------------------------------------------

/// Validate all config operators: existence, arity, and level checks.
///
/// Standalone version callable from both sequential and parallel checker setup.
/// Returns `Err(CheckError)` on the first validation failure. Callers wrap
/// into `CheckResult` with their own stats.
///
/// Part of #2699: also validates that variables are declared, centralizing
/// the `NoVariables` check previously duplicated in sequential and parallel setup.
pub(crate) fn validate_all_config_ops(
    ctx: &EvalCtx,
    config: &Config,
    num_vars: usize,
) -> Result<(), CheckError> {
    if num_vars == 0 {
        return Err(ConfigCheckError::NoVariables.into());
    }

    validate_invariants(ctx, &config.invariants)?;
    validate_properties(ctx, &config.properties)?;

    for name in &config.constraints {
        validate_config_op_arity(ctx, name, "CONSTRAINT")?;
    }
    for name in &config.action_constraints {
        validate_config_op_arity(ctx, name, "ACTION_CONSTRAINT")?;
    }
    if let Some(ref name) = config.init {
        validate_config_op_arity(ctx, name, "INIT")?;
    }
    if let Some(ref name) = config.next {
        validate_config_op_arity(ctx, name, "NEXT")?;
    }

    Ok(())
}

/// Validate invariants: existence + arity + state-level.
///
/// TLC reference: `SpecProcessor.java:997-1040` (processConfigInvariants).
pub(crate) fn validate_invariants(ctx: &EvalCtx, invariants: &[String]) -> Result<(), CheckError> {
    for inv_name in invariants {
        let def = match ctx.get_op(inv_name) {
            Some(d) => d.clone(),
            None => {
                return Err(ConfigCheckError::MissingInvariant(inv_name.clone()).into());
            }
        };

        if !def.params.is_empty() {
            return Err(ConfigCheckError::OpRequiresNoArgs {
                op_name: inv_name.clone(),
                kind: "INVARIANT".to_string(),
                arity: def.params.len(),
            }
            .into());
        }

        // Level check (TLC: SpecProcessor.java:1017-1027).
        // Invariants must be state-level: no primed variables, no temporal operators.
        let has_prime = def.contains_prime;
        let has_temporal = expr_contains_temporal_v(&def.body.node);
        if has_prime || has_temporal {
            return Err(ConfigCheckError::InvariantNotStateLevel {
                name: inv_name.clone(),
                has_prime,
                has_temporal,
            }
            .into());
        }
    }
    Ok(())
}

/// Validate properties: existence + arity.
///
/// TLC reference: `SpecProcessor.java:804` (processConfigProps).
pub(crate) fn validate_properties(ctx: &EvalCtx, properties: &[String]) -> Result<(), CheckError> {
    for prop_name in properties {
        let def = match ctx.get_op(prop_name) {
            Some(d) => d.clone(),
            None => {
                return Err(ConfigCheckError::MissingProperty(prop_name.clone()).into());
            }
        };
        if !def.params.is_empty() {
            return Err(ConfigCheckError::OpRequiresNoArgs {
                op_name: prop_name.clone(),
                kind: "PROPERTY".to_string(),
                arity: def.params.len(),
            }
            .into());
        }
    }
    Ok(())
}

/// Validate that a config operator exists and has zero arity.
///
/// Missing ops for INIT/NEXT are caught elsewhere (MissingInit/MissingNext).
/// Missing CONSTRAINT/ACTION_CONSTRAINT ops are silently skipped (TLC pattern).
pub(crate) fn validate_config_op_arity(
    ctx: &EvalCtx,
    name: &str,
    kind: &str,
) -> Result<(), CheckError> {
    if let Some(def) = ctx.get_op(name) {
        if !def.params.is_empty() {
            return Err(ConfigCheckError::OpRequiresNoArgs {
                op_name: name.to_string(),
                kind: kind.to_string(),
                arity: def.params.len(),
            }
            .into());
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// ModelChecker delegation methods (sequential path)
// ---------------------------------------------------------------------------

impl<'a> ModelChecker<'a> {
    /// Validate all config operators: existence, arity, and level checks.
    #[allow(clippy::result_large_err)]
    pub(super) fn validate_config_ops(&self) -> Result<(), CheckResult> {
        validate_all_config_ops(&self.ctx, self.config, self.module.vars.len())
            .map_err(|error| CheckResult::from_error(error, self.stats.clone()))
    }
}
