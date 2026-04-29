// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::eval::EvalCtx;
use crate::Value;
use std::sync::Arc;
use std::time::Duration;
use tla_core::ast::OperatorDef;
use tla_core::name_intern::{intern_name, NameId};

pub(super) struct ConstantPrecomputeReport {
    pub(super) precomputed: im::HashMap<NameId, Value>,
    pub(super) skipped_slow: Vec<(String, Duration)>,
    pub(super) errors: Vec<(String, String)>,
    pub(super) panicked: Vec<String>,
}

pub(super) fn collect_precomputed_constants(ctx: &mut EvalCtx) -> ConstantPrecomputeReport {
    // Collect candidate operators: zero-arity, no primes, not recursive, not config-overridden,
    // not from THEOREM/LEMMA declarations (TLC excludes theorems from processConstantDefns).
    // Part of #1105.
    let candidates: Vec<(String, Arc<OperatorDef>)> = ctx
        .ops()
        .iter()
        .filter(|(name, def)| {
            def.params.is_empty()
                && !def.contains_prime
                && !def.is_recursive
                && !ctx.is_config_constant(name)
                && !ctx.is_theorem_op(name)
        })
        .map(|(name, def): (&String, &Arc<OperatorDef>)| (name.clone(), Arc::clone(def)))
        .collect();

    if candidates.is_empty() {
        return ConstantPrecomputeReport {
            precomputed: im::HashMap::new(),
            skipped_slow: Vec::new(),
            errors: Vec::new(),
            panicked: Vec::new(),
        };
    }

    // Part of #3125: Use transitive semantic level classification to determine
    // if each candidate is truly constant-level. This follows operator references,
    // labels, module refs, and LET-bindings — matching TLC's getLevelBound().
    let level_analyzer = crate::liveness::AstToLive::new();

    let mut precomputed = im::HashMap::new();
    let mut skipped_slow = Vec::new();
    let mut errors = Vec::new();
    let mut panicked = Vec::new();
    for (name, def) in &candidates {
        if level_analyzer.get_level_with_ctx(ctx, &def.body.node)
            != crate::liveness::ExprLevel::Constant
        {
            continue;
        }

        // Evaluate in a clean context (no state, no INSTANCE scope).
        // Wrap in catch_unwind to handle stack overflows from deeply nested or
        // transitively recursive operators (TLC catches Throwable including
        // StackOverflowError in processConstantDefns). Part of #2793.
        let start = std::time::Instant::now();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::eval::eval_entry(ctx, &def.body)
        }));
        match result {
            Ok(Ok(value)) => {
                let elapsed = start.elapsed();
                if elapsed > Duration::from_millis(500) {
                    // Log slow precomputation but still store the result.
                    // TLC has no timeout cap in processConstantDefns().
                    skipped_slow.push((name.clone(), elapsed));
                }
                let name_id = intern_name(name);
                precomputed.insert(name_id, value);
            }
            Ok(Err(error)) => errors.push((name.clone(), error.to_string())),
            Err(_) => panicked.push(name.clone()),
        }
    }

    ConstantPrecomputeReport {
        precomputed,
        skipped_slow,
        errors,
        panicked,
    }
}

pub(super) fn collect_promotable_env_constants(ctx: &EvalCtx) -> Vec<(NameId, Value)> {
    let env = ctx.env();
    if env.is_empty() {
        return Vec::new();
    }

    // Collect entries to promote: env entries that are not state variables
    // and not already in precomputed_constants.
    let var_registry = ctx.var_registry();
    let precomputed_consts = ctx.precomputed_constants();
    env.iter()
        .filter_map(|(name, value): (&Arc<str>, &crate::value::Value)| {
            let name_id = intern_name(name.as_ref());
            // Skip state variables — they use state_env for O(1) array-indexed lookup
            if var_registry.get_by_name_id(name_id).is_some() {
                return None;
            }
            // Skip if already in precomputed_constants
            if precomputed_consts.get(&name_id).is_some() {
                return None;
            }
            Some((name_id, value.clone()))
        })
        .collect()
}
