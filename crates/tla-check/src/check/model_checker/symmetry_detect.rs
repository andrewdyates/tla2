// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Automatic symmetry detection from model value sets in TLC configuration.
//!
//! When a spec declares `CONSTANT Procs <- {p1, p2, p3}` (a `ModelValueSet`)
//! but no explicit `SYMMETRY` directive, the model values in that set are
//! candidates for symmetry reduction via `Permutations(Procs)`.
//!
//! This module detects such candidate sets and generates the corresponding
//! permutation groups, enabling symmetry reduction without manual configuration.
//!
//! Controlled by the `TLA2_AUTO_SYMMETRY` environment variable:
//! - `TLA2_AUTO_SYMMETRY=1`: enable auto-detection
//! - unset or `0`: disabled (default, matching TLC behavior)
//!
//! The auto-detection is conservative: it only applies to `ModelValueSet`
//! constants (not scalar `ModelValue` or `Value` constants).

use crate::config::{Config, ConstantValue};
use crate::eval::EvalCtx;
use crate::value::FuncValue;

/// Check if auto-symmetry detection is enabled via environment variable.
/// Cached via `OnceLock` (Part of #4114).
#[must_use]
pub(crate) fn auto_symmetry_enabled() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        matches!(
            std::env::var("TLA2_AUTO_SYMMETRY").as_deref(),
            Ok("1") | Ok("true")
        )
    })
}

/// Detect model value set constants that are candidates for automatic symmetry.
///
/// Returns a list of (constant_name, model_value_names) pairs for each
/// `ModelValueSet` constant in the config that has 2+ elements.
/// Single-element sets are excluded because their symmetry group is trivial.
#[must_use]
pub(crate) fn detect_symmetric_model_value_sets(config: &Config) -> Vec<(String, Vec<String>)> {
    let mut candidates = Vec::new();
    for (name, value) in &config.constants {
        if let ConstantValue::ModelValueSet(values) = value {
            if values.len() >= 2 {
                candidates.push((name.clone(), values.clone()));
            }
        }
    }
    // Sort by name for deterministic ordering.
    candidates.sort_by(|a, b| a.0.cmp(&b.0));
    candidates
}

/// Generate symmetry permutations for auto-detected model value sets.
///
/// For each candidate set, generates all permutations (the full symmetric
/// group S_n). Then computes the group closure of the union of all generators,
/// matching the behavior of `Permutations(A) \cup Permutations(B)`.
///
/// Returns `(permutations, group_names)` where `group_names` lists the
/// constant names that contributed symmetry groups.
pub(crate) fn auto_detect_symmetry_perms(
    ctx: &EvalCtx,
    config: &Config,
) -> (Vec<FuncValue>, Vec<String>) {
    if !auto_symmetry_enabled() {
        return (Vec::new(), Vec::new());
    }

    // Don't auto-detect if explicit SYMMETRY is configured.
    if config.symmetry.is_some() {
        return (Vec::new(), Vec::new());
    }

    let candidates = detect_symmetric_model_value_sets(config);
    if candidates.is_empty() {
        return (Vec::new(), Vec::new());
    }

    let mut all_generators = Vec::new();
    let mut group_names = Vec::new();

    for (const_name, _mv_names) in &candidates {
        // Look up the constant's value in the eval context to get the actual
        // model values (which have been registered with indices).
        let set_value = match ctx.lookup(const_name) {
            Some(v) => v,
            None => continue, // Constant not yet bound; skip.
        };

        // Generate transposition generators for S_n.
        // For {a, b, c}, generate: (a b), (b c) — these generate all of S_n.
        let elements: Vec<crate::Value> = match set_value.iter_set() {
            Some(iter) => iter.collect(),
            None => continue,
        };

        if elements.len() < 2 {
            continue;
        }

        // Generate adjacent transpositions: (e[0] e[1]), (e[1] e[2]), ...
        // These generate the full symmetric group S_n.
        for window in elements.windows(2) {
            let a = &window[0];
            let b = &window[1];
            // Build a function that swaps a <-> b and fixes everything else.
            let mut entries: Vec<(crate::Value, crate::Value)> = elements
                .iter()
                .map(|e| {
                    if e == a {
                        (e.clone(), b.clone())
                    } else if e == b {
                        (e.clone(), a.clone())
                    } else {
                        (e.clone(), e.clone())
                    }
                })
                .collect();
            entries.sort_by(|x, y| x.0.cmp(&y.0));
            all_generators.push(FuncValue::from_sorted_entries(entries));
        }

        group_names.push(const_name.clone());
    }

    if all_generators.is_empty() {
        return (Vec::new(), group_names);
    }

    // Compute group closure using the same frontier algorithm as symmetry_perms.rs.
    use std::collections::BTreeSet;
    #[allow(clippy::mutable_key_type)]
    let mut seen_set: BTreeSet<FuncValue> = all_generators.iter().cloned().collect();
    let mut seen_vec: Vec<FuncValue> = seen_set.iter().cloned().collect();
    let mut frontier_start = 0;

    loop {
        let frontier_end = seen_vec.len();
        if frontier_start == frontier_end {
            break;
        }
        for idx in frontier_start..frontier_end {
            let elem = seen_vec[idx].clone();
            for gen in &all_generators {
                let composed = gen.compose_perm(&elem);
                if seen_set.insert(composed.clone()) {
                    seen_vec.push(composed);
                }
            }
        }
        frontier_start = frontier_end;
    }

    (seen_vec, group_names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ConstantValue;

    #[test]
    fn test_detect_symmetric_model_value_sets_basic() {
        let mut config = Config::default();
        config.constants.insert(
            "Procs".to_string(),
            ConstantValue::ModelValueSet(vec![
                "p1".to_string(),
                "p2".to_string(),
                "p3".to_string(),
            ]),
        );
        config
            .constants
            .insert("N".to_string(), ConstantValue::Value("3".to_string()));

        let candidates = detect_symmetric_model_value_sets(&config);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].0, "Procs");
        assert_eq!(candidates[0].1.len(), 3);
    }

    #[test]
    fn test_detect_symmetric_excludes_small_sets() {
        let mut config = Config::default();
        config.constants.insert(
            "Single".to_string(),
            ConstantValue::ModelValueSet(vec!["s1".to_string()]),
        );

        let candidates = detect_symmetric_model_value_sets(&config);
        assert!(
            candidates.is_empty(),
            "single-element model value sets should be excluded"
        );
    }

    #[test]
    fn test_detect_symmetric_multiple_groups() {
        let mut config = Config::default();
        config.constants.insert(
            "Acceptors".to_string(),
            ConstantValue::ModelValueSet(vec![
                "a1".to_string(),
                "a2".to_string(),
                "a3".to_string(),
            ]),
        );
        config.constants.insert(
            "Values".to_string(),
            ConstantValue::ModelValueSet(vec!["v1".to_string(), "v2".to_string()]),
        );

        let candidates = detect_symmetric_model_value_sets(&config);
        assert_eq!(candidates.len(), 2);
        // Should be sorted by name.
        assert_eq!(candidates[0].0, "Acceptors");
        assert_eq!(candidates[1].0, "Values");
    }

    #[test]
    fn test_detect_symmetric_skips_when_explicit_symmetry() {
        let mut config = Config::default();
        config.symmetry = Some("Sym".to_string());
        config.constants.insert(
            "Procs".to_string(),
            ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
        );

        // When SYMMETRY is explicitly set, auto-detection should still find
        // candidates (the filtering happens at a higher level in the checker).
        // Here we verify the detection function itself returns the model value sets.
        let candidates = detect_symmetric_model_value_sets(&config);
        assert_eq!(
            candidates.len(),
            1,
            "should detect Procs as a symmetric model value set even with explicit SYMMETRY"
        );
        assert_eq!(candidates[0].0, "Procs");
    }
}
