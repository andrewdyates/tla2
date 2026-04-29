// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-evaluation of constant-level operators and promotion of env constants.
//!
//! Mirrors TLC's `SpecProcessor.processConstantDefns()`: evaluate all zero-arg
//! operators that don't reference state variables ONCE at startup, store results
//! for O(1) lookup during model checking.
//!
//! Extracted from `run_prepare.rs` (Part of #3472).

use super::debug::tla2_debug;
use crate::eval::{EvalCtx, IdentHint};
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::name_intern::{intern_name, interned_name_count};

/// Pre-evaluate zero-arity constant-level operators that don't reference state
/// variables. Stores results in `SharedCtx.precomputed_constants` for O(1) lookup
/// during BFS, matching TLC's `SpecProcessor.processConstantDefns()`.
///
/// Must be called after `resolve_state_vars_in_loaded_ops()` and constant binding.
///
/// Part of #3125: Uses semantic level classification (`AstToLive::get_level_with_ctx`)
/// instead of a shallow syntactic gate. The semantic check resolves identifiers,
/// labels, module references, and LET-bindings transitively — matching TLC's
/// `getLevelBound(...)` in `processConstantDefns`.
pub(crate) fn precompute_constant_operators(ctx: &mut EvalCtx) {
    // Collect candidates: zero-arity, no primes, not recursive, not config-overridden,
    // not from THEOREM/LEMMA (TLC excludes theorems from processConstantDefns). #1105.
    // Part of #4067: Also skip operators that have been replaced via config
    // (e.g., `Ballot <- MCBallot`). Precomputing the original body of a replaced
    // operator would cache the wrong value (e.g., `Nat` instead of `0..1`),
    // bypassing the op_replacement resolution in eval_ident.
    let op_replacements = ctx.op_replacements().clone();
    let candidates: Vec<(String, Arc<OperatorDef>)> = ctx
        .ops()
        .iter()
        .filter(|(name, def)| {
            def.params.is_empty()
                && !def.contains_prime
                && !def.is_recursive
                && !ctx.is_config_constant(name)
                && !ctx.is_theorem_op(name)
                && !op_replacements.contains_key(name.as_str())
        })
        .map(|(name, def): (&String, &Arc<OperatorDef>)| (name.clone(), Arc::clone(def)))
        .collect();

    if candidates.is_empty() {
        return;
    }

    // Part of #3125: Use transitive semantic level classification to determine
    // if each candidate is truly constant-level. This follows operator references,
    // labels, module refs, and LET-bindings — matching TLC's getLevelBound().
    let level_analyzer = crate::liveness::AstToLive::new();

    let mut precomputed = im::HashMap::new();
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
                if elapsed > std::time::Duration::from_millis(500) {
                    // Log slow precomputation but still store the result.
                    // TLC's processConstantDefns() has no timeout cap — it
                    // precomputes all constant-level operators regardless of
                    // cost. Discarding slow results forces per-state
                    // re-evaluation (O(states × eval_cost)) which is
                    // catastrophically worse than the one-time startup cost.
                    // Example: MCBinarySearch's SortedSeqs (488K-element
                    // filter) is referenced on every state via TypeOK.
                    debug_eprintln!(
                        tla2_debug(),
                        "[precompute] '{}': slow ({:?}) but cached",
                        name,
                        elapsed
                    );
                }
                let name_id = intern_name(name);
                precomputed.insert(name_id, value);
            }
            Ok(Err(_e)) => {
                // Skip (TLC compat: processConstantDefns try/catch). Part of #2793.
                debug_eprintln!(tla2_debug(), "[precompute] '{}' error: {}", name, _e);
            }
            Err(_) => {
                // Panic (stack overflow, etc.) — skip silently.
                debug_eprintln!(tla2_debug(), "[precompute] '{}' panicked", name);
            }
        }
    }

    if !precomputed.is_empty() {
        if tla2_debug() {
            eprintln!(
                "[precompute] Pre-evaluated {} constant operators",
                precomputed.len()
            );
        }
        *Arc::make_mut(ctx.shared_arc_mut()).precomputed_constants_mut() = precomputed;
    }
}

/// Part of #2895: Promote env constants (CONSTANT declarations from model config)
/// to precomputed_constants for NameId-keyed O(1) lookup in eval_ident.
///
/// After `bind_constants_from_config()`, the env contains CONSTANT values like
/// NumActors=3, model values like Server=model_value("Server"), etc. These are
/// accessed via `ctx.env.get(name)` which requires string hashing on every lookup.
/// By promoting them to precomputed_constants (NameId key, integer comparison),
/// eval_ident finds them via the precomputed_constants check BEFORE env.get().
///
/// Only promotes entries NOT in the var_registry (state variables stay in state_env).
pub(crate) fn promote_env_constants_to_precomputed(ctx: &mut EvalCtx) {
    use tla_core::name_intern::NameId;

    let env = ctx.env();
    if env.is_empty() {
        return;
    }

    // Collect entries to promote: env entries that are not state variables
    // and not already in precomputed_constants.
    let var_registry = ctx.var_registry();
    let precomputed_consts = ctx.precomputed_constants();
    let entries: Vec<(NameId, crate::value::Value)> = env
        .iter()
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
        .collect();

    if entries.is_empty() {
        return;
    }

    let promoted = entries.len();
    let precomputed = Arc::make_mut(ctx.shared_arc_mut()).precomputed_constants_mut();
    for (name_id, value) in entries {
        precomputed.insert(name_id, value);
    }

    if tla2_debug() && promoted > 0 {
        eprintln!("[precompute] Promoted {promoted} env constants to precomputed_constants");
    }
}

/// Zero-arg builtin names that eval_builtin recognizes without operator definitions.
/// These are the identifiers that resolve to built-in sets/values when referenced
/// without arguments (e.g., `x \in Nat`, `BOOLEAN`, `Int`).
const ZERO_ARG_BUILTINS: &[&str] = &["Nat", "Int", "Real", "Infinity", "BOOLEAN"];

/// Build the identifier resolution hint table for eval_ident fast-path dispatch.
///
/// Classifies every interned NameId into a resolution tier so that eval_ident can
/// skip the multi-tier lookup waterfall after BindingChain lookup. The hint table
/// is a Vec indexed by NameId.0, giving O(1) array access with no hashing.
///
/// Classification priority (first match wins):
/// 1. op_replacements -> OpReplacement (must go through slow path)
/// 2. state variables (var_registry) -> StateVar
/// 3. precomputed_constants -> PrecomputedConstant
/// 4. shared.ops (zero params) -> SharedZeroArgOp
/// 5. shared.ops (with params) -> SharedParamOp
/// 6. zero-arg builtins -> Builtin
/// 7. everything else -> Unknown (full waterfall)
///
/// Must be called after precompute_constant_operators() and
/// promote_env_constants_to_precomputed() so that all constant-level operators
/// are already in precomputed_constants.
///
/// Part of #3961.
pub(crate) fn build_ident_hints(ctx: &mut EvalCtx) {
    let num_names = interned_name_count();
    let mut hints = vec![IdentHint::Unknown; num_names];

    // Part of #3961: Build O(1) NameId-to-VarIndex lookup table alongside hints.
    // Indexed by NameId.0, stores VarIndex.0 or u16::MAX for non-state-vars.
    // Replaces the linear scan in VarRegistry::get_by_name_id() on the hot path.
    let mut var_idx_table: Vec<u16> = vec![u16::MAX; num_names];

    let shared = ctx.shared();

    // 1. Classify op_replacements (these force the slow path)
    for (name, _) in shared.op_replacements.iter() {
        let name_id = intern_name(name);
        if (name_id.0 as usize) < hints.len() {
            hints[name_id.0 as usize] = IdentHint::OpReplacement;
        }
    }

    // 2. Classify state variables and populate var_idx lookup table.
    // (Normally Expr::StateVar handles these, but shadowed Ident nodes may still
    // need to resolve via state_env in eval_ident.)
    for (idx, _name) in shared.var_registry.iter() {
        let name_id = shared.var_registry.name_id_at(idx);
        let nid = name_id.0 as usize;
        if nid < hints.len() {
            // Always populate the var_idx table, even for op_replacements
            var_idx_table[nid] = idx.0;
            if hints[nid] == IdentHint::Unknown {
                hints[nid] = IdentHint::StateVar;
            }
        }
    }

    // 3. Classify precomputed constants
    for (name_id, _) in shared.precomputed_constants.iter() {
        if (name_id.0 as usize) < hints.len() && hints[name_id.0 as usize] == IdentHint::Unknown {
            hints[name_id.0 as usize] = IdentHint::PrecomputedConstant;
        }
    }

    // Part of #3961: Build O(1) NameId-to-OperatorDef lookup table alongside hints.
    // Indexed by NameId.0, stores Arc<OperatorDef> for shared operators.
    // Replaces string-hashed ops.get(name) lookups on the eval_ident hot path.
    let mut ops_table: Vec<Option<Arc<OperatorDef>>> = vec![None; num_names];

    // 4. Classify shared operators and populate ops lookup table.
    for (name, def) in shared.ops.iter() {
        let name_id = intern_name(name);
        let nid = name_id.0 as usize;
        if nid < hints.len() {
            // Always populate the ops table, even for op_replacements.
            ops_table[nid] = Some(Arc::clone(def));
            if hints[nid] == IdentHint::Unknown {
                if def.params.is_empty() {
                    hints[nid] = IdentHint::SharedZeroArgOp;
                } else {
                    hints[nid] = IdentHint::SharedParamOp;
                }
            }
        }
    }

    // 5. Classify zero-arg builtins
    for builtin_name in ZERO_ARG_BUILTINS {
        let name_id = intern_name(builtin_name);
        if (name_id.0 as usize) < hints.len() && hints[name_id.0 as usize] == IdentHint::Unknown {
            hints[name_id.0 as usize] = IdentHint::Builtin;
        }
    }

    let classified = hints.iter().filter(|h| **h != IdentHint::Unknown).count();
    if tla2_debug() {
        eprintln!("[precompute] Built ident_hints: {classified}/{num_names} names classified");
    }

    let shared_mut = Arc::make_mut(ctx.shared_arc_mut());
    shared_mut.ident_hints = hints;
    shared_mut.var_idx_by_name_id = var_idx_table;
    shared_mut.ops_by_name_id = ops_table;
}
