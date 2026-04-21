// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern matching engine for E-matching.
//!
//! Standalone matching functions extracted from `mod.rs` for code health (#5970).

use z4_core::term::TermData;
use z4_core::{TermId, TermStore};

use super::pattern::{EMatchArg, EMatchPattern, EqualityClasses, TermIndex};
use super::MAX_MULTI_TRIGGER_BINDINGS;

/// Try to match a pattern against a ground term.
/// If `eqclasses` is provided, ground term comparisons use equivalence classes
/// instead of syntactic equality (#3325 Gap 1).
pub(super) fn match_pattern(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    num_vars: usize,
    eqclasses: Option<&EqualityClasses>,
) -> Option<Vec<TermId>> {
    let mut binding: Vec<Option<TermId>> = vec![None; num_vars];

    if !match_pattern_recursive(terms, pattern, ground_term, &mut binding, eqclasses) {
        return None;
    }

    // All variables must be bound
    let full: Vec<TermId> = binding.iter().filter_map(|&b| b).collect();
    if full.len() == num_vars {
        Some(full)
    } else {
        None
    }
}

/// Match a multi-trigger group: ALL patterns must match with consistent bindings.
///
/// For each pattern in the group, collects all candidate matches from the term index.
/// Joins bindings across patterns: a variable bound by pattern 1 must have the same
/// value when checked by pattern 2. Returns all complete, consistent bindings.
///
/// This is the fix for #3325 Gap 2: multi-trigger support.
pub(super) fn match_multi_trigger(
    terms: &TermStore,
    patterns: &[EMatchPattern],
    index: &TermIndex,
    num_vars: usize,
    eqclasses: Option<&EqualityClasses>,
) -> Vec<Vec<TermId>> {
    if patterns.is_empty() {
        return vec![];
    }

    // Start with a single empty binding
    let mut all_bindings: Vec<Vec<Option<TermId>>> = vec![vec![None; num_vars]];

    // For each pattern, extend all existing bindings with matches from the index
    for pattern in patterns {
        let candidates = index.get_by_symbol(pattern.symbol.name());
        let mut next_bindings = Vec::new();

        'join: for existing_binding in &all_bindings {
            for &ground_term in candidates {
                let mut binding = existing_binding.clone();
                if match_pattern_recursive(terms, pattern, ground_term, &mut binding, eqclasses) {
                    next_bindings.push(binding);
                    if next_bindings.len() >= MAX_MULTI_TRIGGER_BINDINGS {
                        break 'join;
                    }
                }
            }
        }

        all_bindings = next_bindings;
        if all_bindings.is_empty() {
            return vec![]; // No way to satisfy this trigger group
        }
    }

    // Filter: all variables must be bound
    all_bindings
        .into_iter()
        .filter_map(|binding| {
            let full: Vec<TermId> = binding.iter().filter_map(|&b| b).collect();
            if full.len() == num_vars {
                Some(full)
            } else {
                None
            }
        })
        .collect()
}

/// Recursively match a pattern against a ground term, accumulating bindings.
/// Returns true if the match succeeds, false otherwise.
///
/// When equality classes are provided and the direct structural match fails,
/// tries all equivalent terms in the same class (#3325 Gap 1).
fn match_pattern_recursive(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    binding: &mut [Option<TermId>],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    // Save binding state before the direct match attempt. The direct match
    // can partially fill binding slots before failing (e.g., pattern f(x,x)
    // against f(a,b) sets binding[0]=a then fails on the second x). Without
    // this save/restore, the equivalence class fallback loop would start from
    // dirty binding state and potentially miss valid alternative matches.
    let saved = binding.to_vec();

    // Try direct structural match first
    if match_pattern_recursive_direct(terms, pattern, ground_term, binding, eqclasses) {
        return true;
    }

    // Restore binding after failed direct match before trying equivalences
    binding.copy_from_slice(&saved);

    // Direct match failed. Try equivalent terms if equality classes available.
    if let Some(eq) = eqclasses {
        let members = eq.class_members(ground_term);
        for &member_id in members {
            let member = TermId(member_id);
            if member != ground_term {
                // Save binding state to restore on failure
                let saved = binding.to_vec();
                if match_pattern_recursive_direct(terms, pattern, member, binding, Some(eq)) {
                    return true;
                }
                // Restore binding on failure
                binding.copy_from_slice(&saved);
            }
        }
    }

    false
}

/// Direct structural match without equivalence class expansion.
fn match_pattern_recursive_direct(
    terms: &TermStore,
    pattern: &EMatchPattern,
    ground_term: TermId,
    binding: &mut [Option<TermId>],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    let (sym, args) = match terms.get(ground_term) {
        TermData::App(s, a) => (s, a),
        _ => return false,
    };

    if sym.name() != pattern.symbol.name() || args.len() != pattern.args.len() {
        return false;
    }

    for (pat_arg, &ground_arg) in pattern.args.iter().zip(args.iter()) {
        if !match_arg(terms, pat_arg, ground_arg, binding, eqclasses) {
            return false;
        }
    }

    true
}

/// Match a single pattern argument against a ground term argument.
/// When `eqclasses` is provided, ground term comparisons use equivalence
/// classes instead of syntactic equality (#3325 Gap 1).
fn match_arg(
    terms: &TermStore,
    pat_arg: &EMatchArg,
    ground_arg: TermId,
    binding: &mut [Option<TermId>],
    eqclasses: Option<&EqualityClasses>,
) -> bool {
    match pat_arg {
        EMatchArg::Var(var_idx) => {
            if let Some(existing) = binding[*var_idx] {
                // Variable already bound - must match (or be equivalent)
                if existing == ground_arg {
                    true
                } else if let Some(eq) = eqclasses {
                    eq.in_same_class(existing, ground_arg)
                } else {
                    false
                }
            } else {
                // Bind variable to this ground term
                binding[*var_idx] = Some(ground_arg);
                true
            }
        }
        EMatchArg::Ground(pat_subterm) => {
            // Ground pattern must match exactly (or be equivalent)
            if *pat_subterm == ground_arg {
                true
            } else if let Some(eq) = eqclasses {
                eq.in_same_class(*pat_subterm, ground_arg)
            } else {
                false
            }
        }
        EMatchArg::Nested(nested_pattern) => {
            // Recursively match nested pattern
            match_pattern_recursive(terms, nested_pattern, ground_arg, binding, eqclasses)
        }
    }
}
