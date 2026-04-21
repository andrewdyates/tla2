// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tier 5: P-invariant implication fold.

use crate::formula_simplify::facts::BinaryInvariant;
use crate::formula_simplify::SimplificationContext;
use crate::property_xml::{IntExpr, StatePredicate};

/// Parsed single-place cardinality bound from an `IntLe` atom.
#[derive(Debug, Clone, Copy)]
enum BoundKind {
    /// `k <= tokens(p)` — lower bound on place p.
    Lower,
    /// `tokens(p) <= k` — upper bound on place p.
    Upper,
}

#[derive(Debug, Clone, Copy)]
struct PlaceBoundAtom {
    place: usize,
    kind: BoundKind,
    bound: u64,
}

/// Try to parse an `IntLe` predicate as a single-place cardinality bound.
///
/// Recognizes:
/// - `IntLe(Constant(k), TokensCount([name]))` → Lower(k) on the resolved place
/// - `IntLe(TokensCount([name]), Constant(k))` → Upper(k) on the resolved place
fn parse_place_bound(
    pred: &StatePredicate,
    ctx: &SimplificationContext<'_>,
) -> Option<PlaceBoundAtom> {
    let (lhs, rhs) = match pred {
        StatePredicate::IntLe(l, r) => (l, r),
        _ => return None,
    };

    match (lhs, rhs) {
        // k <= tokens(name) → Lower bound
        (IntExpr::Constant(k), IntExpr::TokensCount(names)) if names.len() == 1 => {
            let indices = ctx.aliases.resolve_places(&names[0])?;
            if indices.len() == 1 {
                Some(PlaceBoundAtom {
                    place: indices[0].0 as usize,
                    kind: BoundKind::Lower,
                    bound: *k,
                })
            } else {
                None
            }
        }
        // tokens(name) <= k → Upper bound
        (IntExpr::TokensCount(names), IntExpr::Constant(k)) if names.len() == 1 => {
            let indices = ctx.aliases.resolve_places(&names[0])?;
            if indices.len() == 1 {
                Some(PlaceBoundAtom {
                    place: indices[0].0 as usize,
                    kind: BoundKind::Upper,
                    bound: *k,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Derive a bound on the *other* place from a binary invariant and a known bound.
///
/// Given `a * p + b * q = c` and a bound on `p`, derive a bound on `q`.
fn derive_bound(inv: &BinaryInvariant, src: &PlaceBoundAtom) -> Option<PlaceBoundAtom> {
    // Identify which side of the invariant the source atom references.
    let (src_weight, dst_place, dst_weight) = if src.place == inv.lhs_place {
        (inv.lhs_weight, inv.rhs_place, inv.rhs_weight)
    } else if src.place == inv.rhs_place {
        (inv.rhs_weight, inv.lhs_place, inv.lhs_weight)
    } else {
        return None;
    };

    match src.kind {
        BoundKind::Lower => {
            // p >= L → a*L <= a*p → b*q <= c - a*L → q <= floor((c - a*L) / b)
            let used = src_weight.checked_mul(src.bound)?;
            let numerator = inv.constant.checked_sub(used)?;
            Some(PlaceBoundAtom {
                place: dst_place,
                kind: BoundKind::Upper,
                bound: numerator / dst_weight,
            })
        }
        BoundKind::Upper => {
            // p <= U → a*p <= a*U → b*q >= c - a*U → q >= ceil((c - a*U) / b)
            let used = src_weight.checked_mul(src.bound)?;
            let numerator = inv.constant.checked_sub(used)?;
            // ceil(n / d) = (n + d - 1) / d
            let ceil_div = numerator.checked_add(dst_weight - 1)? / dst_weight;
            Some(PlaceBoundAtom {
                place: dst_place,
                kind: BoundKind::Lower,
                bound: ceil_div,
            })
        }
    }
}

/// Check whether atom `a` implies atom `b` via any binary invariant.
///
/// Returns `true` if `a` being true guarantees `b` is true.
fn atom_implies(a: &PlaceBoundAtom, b: &PlaceBoundAtom, invariants: &[BinaryInvariant]) -> bool {
    for inv in invariants {
        if let Some(derived) = derive_bound(inv, a) {
            if derived.place == b.place {
                match (derived.kind, b.kind) {
                    // derived: q <= D, target: q <= B → implies if D <= B
                    (BoundKind::Upper, BoundKind::Upper) => {
                        if derived.bound <= b.bound {
                            return true;
                        }
                    }
                    // derived: q >= D, target: q >= B → implies if D >= B
                    (BoundKind::Lower, BoundKind::Lower) => {
                        if derived.bound >= b.bound {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    false
}

/// Check whether atom `a` contradicts atom `b` via any binary invariant.
///
/// Returns `true` if `a` being true guarantees `b` is false.
fn atom_contradicts(
    a: &PlaceBoundAtom,
    b: &PlaceBoundAtom,
    invariants: &[BinaryInvariant],
) -> bool {
    for inv in invariants {
        if let Some(derived) = derive_bound(inv, a) {
            if derived.place == b.place {
                match (derived.kind, b.kind) {
                    // derived: q <= D, target: q >= B → contradicts if D < B
                    (BoundKind::Upper, BoundKind::Lower) => {
                        if derived.bound < b.bound {
                            return true;
                        }
                    }
                    // derived: q >= D, target: q <= B → contradicts if D > B
                    (BoundKind::Lower, BoundKind::Upper) => {
                        if derived.bound > b.bound {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    false
}

/// Tier 5: P-invariant implication fold.
///
/// For `And(children)`:
/// - if child A contradicts child B → False
/// - if child A implies child B → drop B (redundant)
///
/// For `Or(children)`:
/// - if child A implies child B → drop A (subsumed)
pub(super) fn implication_fold(
    pred: &StatePredicate,
    ctx: &SimplificationContext<'_>,
) -> StatePredicate {
    let invariants = &ctx.facts.binary_invariants;
    if invariants.is_empty() {
        return pred.clone();
    }

    match pred {
        StatePredicate::And(children) => {
            let parsed: Vec<Option<PlaceBoundAtom>> =
                children.iter().map(|c| parse_place_bound(c, ctx)).collect();

            // Check for contradictions first.
            for i in 0..children.len() {
                if let Some(a) = &parsed[i] {
                    for j in (i + 1)..children.len() {
                        if let Some(b) = &parsed[j] {
                            if atom_contradicts(a, b, invariants)
                                || atom_contradicts(b, a, invariants)
                            {
                                return StatePredicate::False;
                            }
                        }
                    }
                }
            }

            // Drop redundant children (A implies B → drop B).
            let mut keep = vec![true; children.len()];
            for i in 0..children.len() {
                if !keep[i] {
                    continue;
                }
                if let Some(a) = &parsed[i] {
                    for j in 0..children.len() {
                        if i == j || !keep[j] {
                            continue;
                        }
                        if let Some(b) = &parsed[j] {
                            if atom_implies(a, b, invariants) {
                                keep[j] = false;
                            }
                        }
                    }
                }
            }

            let filtered: Vec<_> = children
                .iter()
                .zip(keep.iter())
                .filter(|(_, &k)| k)
                .map(|(c, _)| c.clone())
                .collect();

            match filtered.len() {
                0 => StatePredicate::True,
                1 => filtered.into_iter().next().unwrap(),
                _ if filtered.len() == children.len() => pred.clone(),
                _ => StatePredicate::And(filtered),
            }
        }

        StatePredicate::Or(children) => {
            let parsed: Vec<Option<PlaceBoundAtom>> =
                children.iter().map(|c| parse_place_bound(c, ctx)).collect();

            // Drop subsumed children (A implies B → drop A).
            let mut keep = vec![true; children.len()];
            for i in 0..children.len() {
                if !keep[i] {
                    continue;
                }
                if let Some(a) = &parsed[i] {
                    for j in 0..children.len() {
                        if i == j || !keep[j] {
                            continue;
                        }
                        if let Some(b) = &parsed[j] {
                            if atom_implies(a, b, invariants) {
                                keep[i] = false;
                                break;
                            }
                        }
                    }
                }
            }

            let filtered: Vec<_> = children
                .iter()
                .zip(keep.iter())
                .filter(|(_, &k)| k)
                .map(|(c, _)| c.clone())
                .collect();

            match filtered.len() {
                0 => StatePredicate::False,
                1 => filtered.into_iter().next().unwrap(),
                _ if filtered.len() == children.len() => pred.clone(),
                _ => StatePredicate::Or(filtered),
            }
        }

        _ => pred.clone(),
    }
}
