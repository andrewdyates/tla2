// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Vec-based init-state solving: `solve_predicate_for_states` and simulation fallback.

use super::super::super::{
    enumerate_states_from_constraint_branches, Arc, CheckError, ModelChecker, State, Value,
};
use super::Constraint;
use crate::init_strategy::analyze_init_predicate;
use crate::{ConfigCheckError, EvalCheckError};

impl<'a> ModelChecker<'a> {
    /// Solve a predicate to find satisfying states.
    pub(in crate::check::model_checker) fn solve_predicate_for_states(
        &mut self,
        pred_name: &str,
    ) -> Result<Vec<State>, CheckError> {
        let resolved = self.resolve_init_predicate(pred_name)?;
        let def = &self.module.op_defs[&resolved.resolved_name];

        // Analyze for debug logging and z4 strategy recommendation.
        let analysis = analyze_init_predicate(
            &def.body,
            &self.module.vars,
            resolved.constraint_extraction_succeeded,
            &resolved.unconstrained_vars,
        );
        #[cfg(debug_assertions)]
        {
            use super::super::super::debug::debug_init;
            debug_block!(analysis.needs_z4() && debug_init(), {
                eprintln!(
                    "[init-strategy] Recommended: {} (complexity: {})",
                    analysis.strategy, analysis.complexity_score
                );
                for reason in &analysis.reasons {
                    eprintln!("[init-strategy]   - {}", reason);
                }
            });
        }

        // Try z4 enumeration first.
        #[cfg(feature = "z4")]
        if let Some(states) = self.try_z4_init_states(&resolved, true) {
            return Ok(states);
        }

        // Direct constraint enumeration (all variables constrained).
        if let Some(branches) = &resolved.extracted_branches {
            if resolved.unconstrained_vars.is_empty() {
                return match enumerate_states_from_constraint_branches(
                    Some(&self.ctx),
                    &self.module.vars,
                    branches,
                ) {
                    Ok(Some(states)) => Ok(states),
                    Ok(None) => Err(ConfigCheckError::InitCannotEnumerate(
                        "failed to enumerate states from constraints".to_string(),
                    )
                    .into()),
                    Err(e) => Err(EvalCheckError::Eval(e).into()),
                };
            }
        }

        // Fallback: enumerate from a type predicate, filter by full Init.
        let pred_body = &self.module.op_defs[&resolved.resolved_name].body;
        let candidates = self.find_type_candidates(pred_name);
        for cand_name in candidates {
            let Some(branches) = self.candidate_branches(&cand_name) else {
                continue;
            };
            let base_states = match enumerate_states_from_constraint_branches(
                Some(&self.ctx),
                &self.module.vars,
                &branches,
            ) {
                Ok(Some(states)) => states,
                Ok(None) => continue,
                Err(e) => return Err(EvalCheckError::Eval(e).into()),
            };

            let mut filtered: Vec<State> = Vec::new();
            for state in base_states {
                let _scope_guard = self.ctx.scope_guard();
                for (name, value) in state.vars() {
                    self.ctx.bind_mut(Arc::clone(name), value.clone());
                }
                let keep = match crate::eval::eval_entry(&self.ctx, pred_body) {
                    Ok(Value::Bool(b)) => b,
                    Ok(_) => return Err(EvalCheckError::InitNotBoolean.into()),
                    Err(e) => return Err(EvalCheckError::Eval(e).into()),
                };
                drop(_scope_guard);
                if keep {
                    filtered.push(state);
                }
            }
            return Ok(filtered);
        }

        // Build error hint with strategy recommendation.
        let direct_hint = if resolved.extracted_branches.is_some() {
            format!(
                "variable(s) {} have no constraints",
                resolved.unconstrained_vars.join(", ")
            )
        } else {
            "Init predicate contains unsupported expressions (only equality, set membership, \
             conjunction, disjunction, and TRUE/FALSE are supported)"
                .to_string()
        };
        let error_hint = if analysis.needs_z4() {
            let reasons_str = analysis
                .reasons
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ");
            format!(
                "{} (z4-smt strategy recommended: {})",
                direct_hint, reasons_str
            )
        } else {
            direct_hint
        };
        Err(ConfigCheckError::InitCannotEnumerate(error_hint).into())
    }

    /// Simulation-mode fallback for Init with unconstrained variables.
    ///
    /// Part of #3079: TLC's `-generate` mode handles unconstrained Init variables
    /// by assigning default values. This method replicates that behavior for TLA2's
    /// simulation mode. When `generate_initial_states` fails because some variables
    /// lack constraints, this fallback:
    /// 1. Extracts constraints for the variables that ARE constrained
    /// 2. Defaults unconstrained variables to `0` (integer)
    /// 3. Enumerates states from the augmented constraints
    /// 4. Filters results against the full Init predicate
    pub(in crate::check::model_checker) fn generate_initial_states_simulation_fallback(
        &mut self,
        init_name: &str,
    ) -> Result<Vec<State>, CheckError> {
        // First try the normal path.
        match self.solve_predicate_for_states(init_name) {
            Ok(states) => return Ok(states),
            Err(CheckError::Config(ConfigCheckError::InitCannotEnumerate(_))) => {
                // Fall through to simulation-specific fallback.
            }
            Err(e) => return Err(e),
        }

        let resolved = self.resolve_init_predicate(init_name)?;
        let Some(mut branches) = resolved.extracted_branches else {
            return Err(ConfigCheckError::InitCannotEnumerate(
                "simulation fallback: cannot extract constraints from Init".to_string(),
            )
            .into());
        };

        if resolved.unconstrained_vars.is_empty() {
            return Err(ConfigCheckError::InitCannotEnumerate(
                "simulation fallback: all variables constrained but enumeration failed".to_string(),
            )
            .into());
        }

        // Add default value (integer 0) for each unconstrained variable.
        // This matches TLC's -generate behavior where unconstrained variables
        // receive type-appropriate defaults.
        for var_name in &resolved.unconstrained_vars {
            for branch in &mut branches {
                branch.push(Constraint::Eq(var_name.clone(), Value::int(0)));
            }
        }

        // Enumerate states with augmented constraints.
        let candidate_states = match enumerate_states_from_constraint_branches(
            Some(&self.ctx),
            &self.module.vars,
            &branches,
        ) {
            Ok(Some(states)) => states,
            Ok(None) => {
                return Err(ConfigCheckError::InitCannotEnumerate(
                    "simulation fallback: enumeration with defaults failed".to_string(),
                )
                .into());
            }
            Err(e) => return Err(EvalCheckError::Eval(e).into()),
        };

        // Filter candidates against the full Init predicate.
        let pred_body = &self.module.op_defs[&resolved.resolved_name].body;
        let mut filtered = Vec::new();
        for state in candidate_states {
            let _scope_guard = self.ctx.scope_guard();
            for (name, value) in state.vars() {
                self.ctx.bind_mut(Arc::clone(name), value.clone());
            }
            if let Ok(Value::Bool(true)) = crate::eval::eval_entry(&self.ctx, pred_body) {
                filtered.push(state);
            }
        }

        Ok(filtered)
    }
}
