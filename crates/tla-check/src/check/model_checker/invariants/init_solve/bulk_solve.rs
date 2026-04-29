// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Streaming bulk init-state solving: `solve_predicate_for_states_to_bulk`.

use super::super::super::{BulkStateStorage, CheckError, ModelChecker};
use super::{BulkInitStates, EvalCheckError};
#[cfg(feature = "z4")]
use crate::enumerate::BulkConstraintEnumerationStats;
use crate::enumerate::{enumerate_constraints_to_bulk_with_stats, eval_filter_expr};

impl<'a> ModelChecker<'a> {
    /// Solve a predicate and stream results directly to BulkStateStorage.
    ///
    /// Memory-efficient alternative to `solve_predicate_for_states` — avoids intermediate
    /// `State` (OrdMap) objects. For MCBakery ISpec with 655K states this eliminates 655K
    /// OrdMap allocations.
    ///
    /// Returns `Ok(None)` when streaming is not possible (caller falls back to Vec path).
    pub(in crate::check::model_checker) fn solve_predicate_for_states_to_bulk(
        &mut self,
        pred_name: &str,
    ) -> Result<Option<BulkInitStates>, CheckError> {
        let resolved = self.resolve_init_predicate(pred_name)?;

        // Try z4 enumeration first (skip analysis overhead in BruteForce mode).
        #[cfg(feature = "z4")]
        if let Some(states) = self.try_z4_init_states(&resolved, false) {
            let registry = self.ctx.var_registry();
            let mut storage = BulkStateStorage::new(registry.len(), states.len());
            for state in states {
                storage.push_state_iter(Vec::from(state.to_values(registry)));
            }
            let distinct = storage.len();
            return Ok(Some(BulkInitStates {
                storage,
                enumeration: BulkConstraintEnumerationStats {
                    generated: distinct,
                    added: distinct,
                },
            }));
        }

        // Direct constraint enumeration to bulk.
        if let Some(branches) = &resolved.extracted_branches {
            if resolved.unconstrained_vars.is_empty() {
                let vars_len = self.ctx.var_registry().len();
                let mut storage = BulkStateStorage::new(vars_len, 1000);
                let count = enumerate_constraints_to_bulk_with_stats(
                    &mut self.ctx,
                    &self.module.vars,
                    branches,
                    &mut storage,
                    |_values, _ctx| Ok(true),
                );
                return match count {
                    Ok(Some(stats)) => Ok(Some(BulkInitStates {
                        storage,
                        enumeration: stats,
                    })),
                    Ok(None) => Ok(None),
                    Err(e) => Err(EvalCheckError::Eval(e).into()),
                };
            }
        }

        // Fallback: stream from a type predicate with canonical AST filtering.
        let pred_body = &self.module.op_defs[&resolved.resolved_name].body;
        let candidates = self.find_type_candidates(pred_name);
        for cand_name in candidates {
            let Some(branches) = self.candidate_branches(&cand_name) else {
                continue;
            };
            let filter_expr = self.candidate_remainder_filter_expr(pred_body, &cand_name);

            let vars_len = self.ctx.var_registry().len();
            let mut storage = BulkStateStorage::new(vars_len, 1000);
            let count = enumerate_constraints_to_bulk_with_stats(
                &mut self.ctx,
                &self.module.vars,
                &branches,
                &mut storage,
                |_values, ctx| match filter_expr.as_ref() {
                    Some(expr) => eval_filter_expr(ctx, expr),
                    None => Ok(true),
                },
            );
            match count {
                Ok(Some(stats)) => {
                    return Ok(Some(BulkInitStates {
                        storage,
                        enumeration: stats,
                    }));
                }
                Ok(None) => {}
                Err(e) => return Err(EvalCheckError::Eval(e).into()),
            }
        }

        Ok(None)
    }
}
