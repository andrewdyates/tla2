// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::super::debug::debug_liveness_formula;
use super::super::{check_error_to_result, AstToLive, CheckResult, LiveExpr, ModelChecker};
use crate::checker_ops::is_trivially_unsatisfiable;
use crate::LivenessCheckError;

impl<'a> ModelChecker<'a> {
    /// Pre-exploration tautology check for liveness properties (TLC EC 2253).
    ///
    /// TLC detects liveness formula tautologies before state exploration begins.
    /// A property like `<>TRUE` negates to `[]FALSE`, which is trivially unsatisfiable,
    /// meaning the property can never be violated — it's a tautology.
    ///
    /// This check runs early (before BFS) so it works regardless of `store_full_states`
    /// and matches TLC's behavior of rejecting tautologies without exploring any states.
    pub(in crate::check) fn check_properties_for_tautologies(&self) -> Option<CheckResult> {
        if self.config.properties.is_empty() {
            return None;
        }

        let converter = AstToLive::new().with_location_module_name(self.module.root_name.as_str());

        for prop_name in &self.config.properties {
            let def = match self.module.op_defs.get(prop_name) {
                Some(d) => d.clone(),
                None => continue, // Missing property errors are reported later
            };

            // Extract the liveness portion of the property
            let (_safety_parts, liveness_expr) =
                self.separate_safety_liveness_parts(prop_name, &def.body)?;

            let liveness_expr = match liveness_expr {
                Some(expr) => expr,
                None => continue, // No liveness part — purely safety, skip
            };

            // Convert to LiveExpr for tautology analysis
            let prop_live = match converter.convert(&self.ctx, &liveness_expr) {
                Ok(live) => live,
                Err(_e) => {
                    // Part of #2793: Log conversion errors instead of silently skipping.
                    // The actual error is re-reported during liveness checking, but logging
                    // here makes the tautology-skip visible for debugging.
                    debug_block!(debug_liveness_formula(), {
                        eprintln!(
                            "[liveness-tautology] skipping property '{}': conversion error: {}",
                            prop_name, _e
                        );
                    });
                    continue;
                }
            };

            let negated_prop = LiveExpr::not(prop_live).push_negation();
            if is_trivially_unsatisfiable(&negated_prop) {
                return Some(check_error_to_result(
                    LivenessCheckError::FormulaTautology {
                        property: prop_name.clone(),
                    }
                    .into(),
                    &self.stats,
                ));
            }
        }

        None
    }
}
