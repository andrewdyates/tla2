// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symmetry permutation computation from SYMMETRY configuration.
//!
//! Evaluates the SYMMETRY operator, extracts generator permutations, and
//! computes group closure using TLC's incremental frontier algorithm.
//!
//! Extracted from `run_prepare.rs` (Part of #3472).

use super::super::check_error::CheckError;
#[cfg(debug_assertions)]
use super::debug::tla2_debug;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::{ConfigCheckError, EvalCheckError};

/// Compute symmetry permutations from the SYMMETRY configuration.
///
/// Evaluates the SYMMETRY operator (if configured) to get the set of permutation
/// functions. These are used during fingerprinting to identify symmetric states.
///
/// Part of #3011 Unit 3: TLC parity — symmetry configuration errors are hard failures
/// (TLC throws TLCRuntimeException via Assert.fail for all malformed SYMMETRY configs).
/// Previously silently degraded to no-symmetry, masking user configuration bugs.
///
/// Group closure uses TLC's incremental frontier algorithm (MVPerms.permutationSubgroup):
/// compose generators with newly discovered elements only, not all pairs.
/// No size cap — TLC has none. Group size is bounded by n! for n model values.
pub(crate) fn compute_symmetry_perms(
    ctx: &EvalCtx,
    config: &Config,
) -> Result<Vec<crate::value::FuncValue>, CheckError> {
    let symmetry_name = match &config.symmetry {
        Some(name) => name,
        None => return Ok(Vec::new()),
    };

    // TLC: Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, ...) if not found.
    let def = match ctx.get_op(symmetry_name) {
        Some(d) => d.clone(),
        None => {
            return Err(ConfigCheckError::Config(format!(
                "SYMMETRY operator '{symmetry_name}' is specified in the configuration but not defined"
            ))
            .into());
        }
    };

    // TLC: symmetry operator must have zero parameters.
    if !def.params.is_empty() {
        return Err(ConfigCheckError::OpRequiresNoArgs {
            kind: "SYMMETRY".to_string(),
            op_name: symmetry_name.clone(),
            arity: def.params.len(),
        }
        .into());
    }

    // Evaluate in the context (no state variables needed for symmetry definition).
    // TLC: Assert.fail if evaluation doesn't produce an enumerable set.
    let value = crate::eval::eval_entry(ctx, &def.body).map_err(EvalCheckError::Eval)?;

    if !value.is_set() || !value.is_finite_set() {
        return Err(ConfigCheckError::Config(format!(
            "SYMMETRY operator '{}' must specify a set of permutations, got: {}",
            symmetry_name,
            value.type_name()
        ))
        .into());
    }

    // Part of #1918: finite filtered permutation sets stay lazy (SetPred)
    // until iteration. Accept those by enumerating through eval_iter_set(),
    // but keep non-enumerable set-like values (Nat, STRING, AnySet, etc.)
    // on the existing config-error path above.
    let set = crate::eval::eval_iter_set(ctx, &value, Some(def.body.span))
        .map_err(EvalCheckError::Eval)?;

    // Extract function values from the set.
    // TLC: Assert.fail if values are not FcnRcdValue.
    let mut generators = Vec::new();
    for v in set {
        if let Some(func) = v.to_func_coerced() {
            generators.push(func);
        } else {
            return Err(ConfigCheckError::Config(format!(
                "SYMMETRY set contains non-function value: {}",
                v.type_name()
            ))
            .into());
        }
    }

    if generators.is_empty() {
        // TLC: single-element symmetry sets get a warning but continue
        // with symmetry disabled (returns null perms). Match this behavior.
        return Ok(Vec::new());
    }

    // Compute group closure using TLC's incremental frontier algorithm
    // (MVPerms.permutationSubgroup). Compose each generator with newly
    // discovered elements only, not all pairs. No size cap — TLC has none.
    //
    // Part of #3044: Uses Vec (stable indices) + BTreeSet (O(log n) dedup)
    // to match TLC's Vect + Set pattern (MVPerms.java:21-22). The previous
    // BTreeSet-only approach had unstable frontier indices — insertions
    // before frontier_end shifted element positions, causing the frontier
    // window (skip/take) to miss newly composed permutations.
    use std::collections::BTreeSet;
    #[allow(clippy::mutable_key_type)]
    let mut seen_set: BTreeSet<crate::value::FuncValue> = generators.iter().cloned().collect();
    let mut seen_vec: Vec<crate::value::FuncValue> = seen_set.iter().cloned().collect();
    let _base_count = seen_vec.len();

    // Move generators — no further use after seeding seen_set/seen_vec.
    let gen_list = generators;
    let mut frontier_start = 0;

    loop {
        let frontier_end = seen_vec.len();
        if frontier_start == frontier_end {
            break; // No new elements — closure complete.
        }
        // Iterate frontier by stable Vec indices (new elements only append).
        for idx in frontier_start..frontier_end {
            let elem = seen_vec[idx].clone();
            for gen in &gen_list {
                let composed = gen.compose_perm(&elem);
                if seen_set.insert(composed.clone()) {
                    seen_vec.push(composed);
                }
            }
        }
        frontier_start = frontier_end;
    }

    #[cfg(debug_assertions)]
    if tla2_debug() {
        let closure_count = seen_vec.len();
        if closure_count > _base_count {
            eprintln!(
                "Symmetry reduction enabled: {closure_count} permutation(s) (closure of {_base_count} base)"
            );
        } else {
            eprintln!("Symmetry reduction enabled: {closure_count} permutation(s)");
        }
    }

    Ok(seen_vec)
}
