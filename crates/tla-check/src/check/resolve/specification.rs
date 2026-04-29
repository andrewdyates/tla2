// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive `SPECIFICATION` resolution algorithm.
//!
//! Resolves `Init`, `Next`, and fairness from a `SPECIFICATION` operator
//! by pattern-matching the temporal formula and recursively following
//! operator references.

use super::scan::{
    collect_ident_candidates, contains_temporal_operators, find_op_body_in_any_tree,
};
use crate::check::{CheckError, ResolvedSpec, INLINE_NEXT_NAME};
use crate::spec_formula::{extract_all_fairness, extract_spec_formula, FairnessConstraint};
use crate::ConfigCheckError;
use rustc_hash::FxHashSet;
use tla_core::SyntaxNode;

/// Internal outcome for a candidate operator resolution attempt.
///
/// Separates "this candidate isn't a spec wrapper" (NoMatch) from
/// "resolution found a valid spec" (Resolved). Hard errors (cyclic
/// references) are represented as `Err(ResolutionFailure)` and
/// propagated to the caller.
enum CandidateResolution {
    Resolved(ResolvedSpec),
    NoMatch,
}

/// Internal error for non-recoverable resolution failures.
///
/// These must be propagated upward, never silently dropped.
struct ResolutionFailure(CheckError);

impl From<ResolutionFailure> for CheckError {
    fn from(f: ResolutionFailure) -> Self {
        f.0
    }
}

/// Resolve Init/Next from a SPECIFICATION temporal formula, searching multiple trees.
pub(in crate::check) fn resolve_from_specification_multi(
    spec_name: &str,
    syntax_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
) -> Result<ResolvedSpec, CheckError> {
    let mut visited = FxHashSet::default();
    resolve_from_specification_multi_rec(spec_name, syntax_tree, extended_trees, &mut visited)
}

fn resolve_from_specification_multi_rec(
    spec_name: &str,
    syntax_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
    visited: &mut FxHashSet<String>,
) -> Result<ResolvedSpec, CheckError> {
    if !visited.insert(spec_name.to_string()) {
        let msg = format!("cyclic SPECIFICATION reference involving '{spec_name}'");
        return Err(ConfigCheckError::Specification(msg).into());
    }

    // Find operator body in main module first, then extended modules.
    let Some(spec_body) = find_op_body_in_any_tree(syntax_tree, extended_trees, spec_name) else {
        return Err(
            ConfigCheckError::Specification(format!("operator '{spec_name}' not found")).into(),
        );
    };

    // Extract Init/Next from the temporal formula, if it matches a known pattern.
    if let Some(formula) = extract_spec_formula(&spec_body) {
        // Even when the core Init /\ [][Next]_vars pattern matches, the spec body can
        // still conjunct in fairness/liveness assumptions via referenced operators:
        //
        //   Spec == Init /\ [][Next]_vars /\ Liveness
        //
        // If we return immediately here, we'd miss fairness from `Liveness` and get
        // false-positive liveness violations (e.g., SchedulingAllocator).
        let mut fairness = formula.fairness;

        // Extract fairness from any referenced operators at this level.
        // Only include candidates that are actually defined operators.
        let candidates = collect_ident_candidates(&spec_body);

        for candidate in &candidates {
            // Skip core components of the spec formula.
            if candidate == &formula.init || candidate == &formula.next {
                continue;
            }
            if let Some(vars) = &formula.vars {
                if candidate == vars {
                    continue;
                }
            }

            let Some(body) = find_op_body_in_any_tree(syntax_tree, extended_trees, candidate)
            else {
                continue;
            };

            let candidate_fairness = extract_all_fairness(&body);
            if candidate_fairness.is_empty() {
                if contains_temporal_operators(&body) {
                    fairness.push(FairnessConstraint::TemporalRef {
                        op_name: candidate.clone(),
                    });
                }
            } else {
                fairness.extend(candidate_fairness);
            }
        }

        // When there's an inline NEXT expression, use a synthetic operator name
        // The actual operator will be created by ModelChecker::register_inline_next()
        let next_name = if formula.next_node.is_some() {
            INLINE_NEXT_NAME.to_string()
        } else {
            formula.next
        };

        return Ok(ResolvedSpec {
            init: formula.init,
            next: next_name,
            next_node: formula.next_node,
            fairness,
            stuttering_allowed: formula.stuttering_allowed,
        });
    }

    // Fallback: attempt to resolve SPECIFICATION operators that wrap the actual temporal
    // formula in conjunctions for side effects (e.g., `TestSpec == PrintT(R) /\\ Spec`).
    // Try any referenced operators in the body and accept the first one that yields Init/Next.
    //
    // IMPORTANT: Extract fairness constraints from THIS level before recursing.
    // For specs like `SpecWeakFair == Spec /\ WF_vars(Next)`, the fairness constraint
    // is at this level but Init/Next comes from the nested `Spec` reference.
    let local_fairness = extract_all_fairness(&spec_body);

    let candidates = collect_ident_candidates(&spec_body);

    // First pass: find Init/Next from candidates.
    //
    // Fix for #2445: classify recursive resolution outcomes as Resolved/NoMatch
    // instead of silently dropping all errors. Hard errors (cyclic references)
    // are propagated via `?`.
    //
    // Cycle detection: when ALL defined candidates are already in the visited
    // set, the operator's body references only ancestors in the resolution
    // chain — that's a cycle (e.g., `Bad == Bad`). We track this explicitly
    // so we can emit a proper cyclic error instead of "unsupported formula".
    let mut result: Option<ResolvedSpec> = None;
    let mut any_candidate_tried = false;
    let mut has_defined_visited_candidate = false;
    for candidate in &candidates {
        if visited.contains(candidate) {
            // Check if this visited candidate is actually a defined operator
            // (not just a variable or keyword). Back-references to defined
            // operators in visited indicate a cycle.
            if find_op_body_in_any_tree(syntax_tree, extended_trees, candidate).is_some() {
                has_defined_visited_candidate = true;
            }
            continue;
        }

        // Only attempt candidates that are actually defined operators in any tree.
        if find_op_body_in_any_tree(syntax_tree, extended_trees, candidate).is_none() {
            continue;
        }

        any_candidate_tried = true;
        match try_candidate_spec(candidate, syntax_tree, extended_trees, visited)? {
            CandidateResolution::Resolved(resolved) => {
                result = Some(resolved);
                break;
            }
            CandidateResolution::NoMatch => continue,
        }
    }

    // Second pass: extract fairness from ALL candidates that contain temporal formulas
    // This handles specs like `LISpec == ISpec /\ Liveness2` where:
    // - ISpec contains Init/Next (safety)
    // - Liveness2 contains fairness (temporal, e.g., \A p: WF_vars(Action(p)))
    let mut all_fairness = local_fairness;
    for candidate in &candidates {
        // Skip if we already visited this candidate during Init/Next resolution
        if visited.contains(candidate) {
            continue;
        }

        // Find the operator body in any tree
        if let Some(body) = find_op_body_in_any_tree(syntax_tree, extended_trees, candidate) {
            // Extract any fairness constraints from this candidate's body
            let candidate_fairness = extract_all_fairness(&body);
            if candidate_fairness.is_empty() {
                // No simple fairness found. Check if this contains temporal operators
                // (WF, SF, [], <>) which might be inside quantifiers like \A p: WF_vars(Action(p)).
                // If so, store a TemporalRef to convert the full operator at liveness check time.
                if contains_temporal_operators(&body) {
                    all_fairness.push(FairnessConstraint::TemporalRef {
                        op_name: candidate.clone(),
                    });
                }
            } else {
                all_fairness.extend(candidate_fairness);
            }
        }
    }

    if let Some(mut resolved) = result {
        // Merge fairness: collected fairness from all candidates comes first
        all_fairness.extend(resolved.fairness);
        resolved.fairness = all_fairness;
        return Ok(resolved);
    }

    // If no candidate resolved and ALL defined candidates were in visited
    // (with none even tried), the operator's body forms a cycle.
    if !any_candidate_tried && has_defined_visited_candidate {
        return Err(ConfigCheckError::Specification(format!(
            "cyclic SPECIFICATION reference involving '{spec_name}'"
        ))
        .into());
    }

    Err(ConfigCheckError::Specification(format!(
        "unsupported SPECIFICATION formula in operator '{spec_name}'"
    ))
    .into())
}

/// Attempt to resolve a single candidate operator as a SPECIFICATION wrapper.
///
/// Returns:
/// - `Ok(Resolved(spec))` if the candidate resolves to a valid spec
/// - `Ok(NoMatch)` if the candidate is defined but isn't a spec wrapper
/// - `Err(ResolutionFailure)` for hard errors (cyclic references) that must propagate
fn try_candidate_spec(
    candidate: &str,
    syntax_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
    visited: &mut FxHashSet<String>,
) -> Result<CandidateResolution, ResolutionFailure> {
    match resolve_from_specification_multi_rec(candidate, syntax_tree, extended_trees, visited) {
        Ok(resolved) => Ok(CandidateResolution::Resolved(resolved)),
        Err(CheckError::Config(ConfigCheckError::Specification(ref msg)))
            if msg.contains("not found") || msg.contains("unsupported SPECIFICATION") =>
        {
            // Candidate is defined (we checked above) but doesn't resolve to a spec.
            // This is a "no match" — keep searching other candidates.
            Ok(CandidateResolution::NoMatch)
        }
        Err(hard_error) => {
            // Cyclic references or other non-recoverable errors must propagate.
            Err(ResolutionFailure(hard_error))
        }
    }
}
