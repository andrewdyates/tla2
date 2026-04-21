// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel checker initial-state generation helpers.

use super::*;
use crate::eval::eval_entry;
use crate::{ConfigCheckError, EvalCheckError};

fn collect_fallback_candidates(
    ctx: &EvalCtx,
    init_name: &str,
    invariants: &[String],
) -> Vec<(String, String)> {
    let resolved_init_name = ctx.resolve_op_name(init_name).to_string();
    let mut candidates = Vec::new();
    let mut seen_resolved: std::collections::HashSet<String> = std::collections::HashSet::new();

    for raw_name in ["TypeOK", "TypeOk"] {
        let resolved_name = ctx.resolve_op_name(raw_name).to_string();
        if resolved_name == resolved_init_name || !seen_resolved.insert(resolved_name.clone()) {
            continue;
        }
        candidates.push((raw_name.to_string(), resolved_name));
    }

    for raw_name in invariants {
        let resolved_name = ctx.resolve_op_name(raw_name).to_string();
        if resolved_name == resolved_init_name || !seen_resolved.insert(resolved_name.clone()) {
            continue;
        }
        candidates.push((raw_name.clone(), resolved_name));
    }

    candidates
}

fn fallback_filter_expr(
    ctx: &EvalCtx,
    init_body: &tla_core::Spanned<tla_core::ast::Expr>,
    raw_candidate_name: &str,
    resolved_candidate_name: &str,
) -> Option<tla_core::Spanned<tla_core::ast::Expr>> {
    let filter_expr = extract_conjunction_remainder(ctx, init_body, raw_candidate_name)
        .or_else(|| {
            (raw_candidate_name != resolved_candidate_name)
                .then(|| extract_conjunction_remainder(ctx, init_body, resolved_candidate_name))
                .flatten()
        })
        .unwrap_or_else(|| init_body.clone());

    (!matches!(filter_expr.node, tla_core::ast::Expr::Bool(true))).then_some(filter_expr)
}

impl ParallelChecker {
    pub(super) fn generate_initial_states_to_bulk(
        &self,
        ctx: &mut EvalCtx,
        init_name: &str,
    ) -> Result<Option<BulkStateStorage>, CheckError> {
        let init_name = ctx.resolve_op_name(init_name).to_string();
        let def = self
            .op_defs
            .get(&init_name)
            .ok_or(ConfigCheckError::MissingInit)?;
        let init_body = def.body.clone();

        // Try direct constraint extraction from Init predicate first.
        if let Some(branches) = extract_init_constraints(ctx, &init_body, &self.vars, None) {
            let unconstrained = find_unconstrained_vars(&self.vars, &branches);
            if unconstrained.is_empty() {
                let vars_len = ctx.var_registry().len();
                let mut storage = BulkStateStorage::new(vars_len, 1000);

                let count = enumerate_constraints_to_bulk(
                    ctx,
                    &self.vars,
                    &branches,
                    &mut storage,
                    |_values, _ctx| Ok(true),
                );

                return match count {
                    Ok(Some(_)) => Ok(Some(storage)),
                    Ok(None) => Ok(None),
                    Err(e) => Err(EvalCheckError::Eval(e).into()),
                };
            }
        }

        // Fallback: enumerate from a bounded type predicate, then filter by the remainder
        // of Init (to avoid re-evaluating the candidate).
        let candidates = collect_fallback_candidates(ctx, &init_name, &self.config.invariants);

        for (raw_cand_name, resolved_cand_name) in candidates {
            let Some(cand_def) = self.op_defs.get(&resolved_cand_name) else {
                continue;
            };
            let Some(branches) = extract_init_constraints(ctx, &cand_def.body, &self.vars, None)
            else {
                continue;
            };

            let unconstrained = find_unconstrained_vars(&self.vars, &branches);
            if !unconstrained.is_empty() {
                continue;
            }

            let filter_expr =
                fallback_filter_expr(ctx, &init_body, &raw_cand_name, &resolved_cand_name);

            let vars_len = ctx.var_registry().len();
            let mut storage = BulkStateStorage::new(vars_len, 1000);

            let count = enumerate_constraints_to_bulk(
                ctx,
                &self.vars,
                &branches,
                &mut storage,
                |_values, ctx| match filter_expr.as_ref() {
                    Some(expr) => crate::enumerate::eval_filter_expr(ctx, expr),
                    None => Ok(true),
                },
            );

            match count {
                Ok(Some(_)) => return Ok(Some(storage)),
                Ok(None) => {}
                Err(e) => return Err(EvalCheckError::Eval(e).into()),
            }
        }

        Ok(None)
    }

    /// Generate initial states
    ///
    /// First attempts direct constraint extraction from the Init predicate.
    /// If that fails (unsupported expressions or missing per-variable constraints),
    /// falls back to enumerating states from a type constraint (usually TypeOK)
    /// and filtering by evaluating the full Init predicate.
    pub(super) fn generate_initial_states(
        &self,
        ctx: &EvalCtx,
        init_name: &str,
    ) -> Result<Vec<State>, CheckError> {
        let init_name = ctx.resolve_op_name(init_name).to_string();
        let def = self
            .op_defs
            .get(&init_name)
            .ok_or(ConfigCheckError::MissingInit)?;
        let init_body = def.body.clone();

        // Try to extract constraints directly from the Init predicate
        let direct_hint = if let Some(branches) =
            extract_init_constraints(ctx, &init_body, &self.vars, None)
        {
            let unconstrained = find_unconstrained_vars(&self.vars, &branches);
            if unconstrained.is_empty() {
                return match enumerate_states_from_constraint_branches(
                    Some(ctx),
                    &self.vars,
                    &branches,
                ) {
                    Ok(Some(states)) => Ok(states),
                    Ok(None) => Err(ConfigCheckError::InitCannotEnumerate(
                        "failed to enumerate states from constraints".to_string(),
                    )
                    .into()),
                    Err(e) => Err(EvalCheckError::Eval(e).into()),
                };
            }
            format!(
                "variable(s) {} have no constraints",
                unconstrained.join(", ")
            )
        } else {
            "Init predicate contains unsupported expressions (only equality, set membership, conjunction, disjunction, and TRUE/FALSE are supported)".to_string()
        };

        // Fallback: enumerate from a bounded type predicate, then filter by the full Init.
        let candidates = collect_fallback_candidates(ctx, &init_name, &self.config.invariants);

        for (_raw_cand_name, resolved_cand_name) in candidates {
            let Some(cand_def) = self.op_defs.get(&resolved_cand_name) else {
                continue;
            };
            let cand_body = cand_def.body.clone();

            let Some(branches) = extract_init_constraints(ctx, &cand_body, &self.vars, None) else {
                continue;
            };

            let unconstrained = find_unconstrained_vars(&self.vars, &branches);
            if !unconstrained.is_empty() {
                continue;
            }

            let base_states =
                match enumerate_states_from_constraint_branches(Some(ctx), &self.vars, &branches) {
                    Ok(Some(states)) => states,
                    Ok(None) => continue,
                    Err(e) => return Err(EvalCheckError::Eval(e).into()),
                };

            // Filter base states by the original Init predicate
            let mut filtered: Vec<State> = Vec::new();
            for state in base_states {
                let mut eval_ctx = ctx.clone();
                for (name, value) in state.vars() {
                    eval_ctx.bind_mut(Arc::clone(name), value.clone());
                }
                let keep = match eval_entry(&eval_ctx, &init_body) {
                    Ok(Value::Bool(b)) => b,
                    Ok(_) => {
                        return Err(EvalCheckError::InitNotBoolean.into());
                    }
                    Err(e) => {
                        return Err(EvalCheckError::Eval(e).into());
                    }
                };

                if keep {
                    filtered.push(state);
                }
            }

            return Ok(filtered);
        }

        Err(ConfigCheckError::InitCannotEnumerate(direct_hint).into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;
    use crate::{ConstantValue, Value};

    fn sorted_x_values_from_bulk(storage: &BulkStateStorage) -> Vec<Value> {
        let mut values: Vec<Value> = (0..storage.len())
            .map(|idx| storage.get_state(idx as u32)[0].clone())
            .collect();
        values.sort();
        values
    }

    fn sorted_x_values_from_states(states: Vec<State>) -> Vec<Value> {
        let mut values: Vec<Value> = states
            .into_iter()
            .map(|state| {
                state
                    .get("x")
                    .cloned()
                    .expect("state should bind x in regression test")
            })
            .collect();
        values.sort();
        values
    }

    /// Regression for replacement-routed TypeOK fallback in the parallel init solver.
    ///
    /// When direct Init constraint extraction fails, the parallel path must resolve
    /// fallback candidate operators through config replacements before enumerating
    /// their constraints. The sequential solver already does this via
    /// `candidate_branches`.
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn parallel_init_fallback_resolves_replaced_typeok_candidate() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let src = r"
---- MODULE ParallelInitFallbackReplacement ----
VARIABLE x
Init == TypeOK /\ x > 0
TypeOK == x \in {99}
MCTypeOK == x \in {0, 1, 2}
Next == x' = x
====
";
        let module = parse_module(src);

        let mut config = crate::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["TypeOK".to_string()],
            ..Default::default()
        };
        config.constants.insert(
            "TypeOK".to_string(),
            ConstantValue::Replacement("MCTypeOK".to_string()),
        );

        let checker = ParallelChecker::new(&module, &config, 2);

        let mut bulk_ctx = checker
            .prepare_base_ctx()
            .expect("parallel init fallback bulk replay should prepare ctx");
        let bulk = checker
            .generate_initial_states_to_bulk(&mut bulk_ctx, "Init")
            .expect("bulk fallback should not error")
            .expect("bulk fallback should enumerate initial states");
        assert_eq!(
            sorted_x_values_from_bulk(&bulk),
            vec![Value::int(1), Value::int(2)],
            "bulk init fallback should use replacement-routed TypeOK candidate"
        );

        let vec_ctx = checker
            .prepare_base_ctx()
            .expect("parallel init fallback Vec replay should prepare ctx");
        let states = checker
            .generate_initial_states(&vec_ctx, "Init")
            .expect("Vec fallback should not error");
        assert_eq!(
            sorted_x_values_from_states(states),
            vec![Value::int(1), Value::int(2)],
            "Vec init fallback should use replacement-routed TypeOK candidate"
        );
    }
}
