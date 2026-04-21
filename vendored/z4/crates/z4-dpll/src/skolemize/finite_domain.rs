// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite domain quantifier expansion.
//!
//! Eliminates quantifiers over finite domains (Bool, small BitVec, bounded Int)
//! by enumerating all values and conjoining/disjoining the instantiated body.
//!
//! Extracted from `skolemize.rs` for code health (#5970).

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_bigint::BigInt;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::Symbol;
use z4_core::{Sort, TermData, TermId, TermStore};

use crate::ematching::subst_vars;

/// Maximum total combinations for finite domain expansion.
/// Beyond this threshold, fall back to E-matching to avoid exponential blowup.
const MAX_FINITE_DOMAIN_COMBOS: u64 = 256;

/// Info about a bounded integer quantifier: the variable's range and the
/// inner body with the guard stripped (for forall) or kept (for exists).
struct BoundedIntInfo {
    /// Lower bound (inclusive)
    lo: i64,
    /// Upper bound (inclusive)
    hi: i64,
    /// The body to instantiate. For forall, this is the inner body with the
    /// guard stripped. For exists, this is the full body (guard kept).
    body: TermId,
}

/// Check if a term is a reference to the named bound variable.
fn is_bound_var(terms: &TermStore, term: TermId, var_name: &str) -> bool {
    matches!(terms.get(term), TermData::Var(name, _) if name == var_name)
}

/// Extract integer bounds for a single quantified variable from a guard
/// conjunction. Returns `(lo, hi)` if tight bounds are found.
///
/// Recognizes these patterns (after `>=`/`>` normalization to `<=`/`<`):
/// - `(<= c x)` → lower bound `c`
/// - `(< c x)` → lower bound `c + 1`
/// - `(<= x c)` → upper bound `c`
/// - `(< x c)` → upper bound `c - 1`
fn extract_bounds_from_atoms(
    terms: &TermStore,
    atoms: &[TermId],
    var_name: &str,
) -> Option<(i64, i64)> {
    let mut lo: Option<i64> = None;
    let mut hi: Option<i64> = None;

    for &atom in atoms {
        match terms.get(atom).clone() {
            TermData::App(Symbol::Named(op), ref args) if args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];
                match op.as_str() {
                    "<=" => {
                        if is_bound_var(terms, rhs, var_name) {
                            // (<= c x) → x >= c → lower bound c
                            if let Some(c) = terms.extract_integer_constant(lhs) {
                                let c = i64::try_from(&c).ok()?;
                                lo = Some(lo.map_or(c, |prev: i64| prev.max(c)));
                            }
                        } else if is_bound_var(terms, lhs, var_name) {
                            // (<= x c) → upper bound c
                            if let Some(c) = terms.extract_integer_constant(rhs) {
                                let c = i64::try_from(&c).ok()?;
                                hi = Some(hi.map_or(c, |prev: i64| prev.min(c)));
                            }
                        }
                    }
                    "<" => {
                        if is_bound_var(terms, rhs, var_name) {
                            // (< c x) → x > c → lower bound c+1
                            if let Some(c) = terms.extract_integer_constant(lhs) {
                                let c = i64::try_from(&c).ok()?.checked_add(1)?;
                                lo = Some(lo.map_or(c, |prev: i64| prev.max(c)));
                            }
                        } else if is_bound_var(terms, lhs, var_name) {
                            // (< x c) → upper bound c-1
                            if let Some(c) = terms.extract_integer_constant(rhs) {
                                let c = i64::try_from(&c).ok()?.checked_sub(1)?;
                                hi = Some(hi.map_or(c, |prev: i64| prev.min(c)));
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    match (lo, hi) {
        (Some(l), Some(h)) if l <= h => Some((l, h)),
        _ => None,
    }
}

/// Collect the atoms from a conjunction, flattening nested `and` nodes.
fn collect_and_atoms(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term).clone() {
        TermData::App(Symbol::Named(op), args) if op == "and" => args
            .iter()
            .flat_map(|&a| collect_and_atoms(terms, a))
            .collect(),
        _ => vec![term],
    }
}

/// Try to extract bounded integer info from a forall body.
///
/// After De Morgan normalization, `(=> (and G1 G2) body)` becomes:
///   `(or (not G1) (not G2) body)`
/// So we look for negated comparison atoms in the Or that provide bounds
/// on the quantified variable. The remaining disjuncts form the inner body.
fn extract_bounded_int_forall(
    terms: &mut TermStore,
    body: TermId,
    var_name: &str,
) -> Option<BoundedIntInfo> {
    let or_args = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), args) if op == "or" => args,
        _ => return None,
    };

    if or_args.len() < 2 {
        return None;
    }

    // Collect negated atoms (guard candidates) and positive atoms (body parts).
    // A negated comparison like Not(<= 0 i) means the guard had (<= 0 i).
    let mut guard_atoms: Vec<TermId> = Vec::new();
    let mut body_parts: Vec<TermId> = Vec::new();

    for &arg in &or_args {
        if let TermData::Not(inner) = terms.get(arg).clone() {
            // Check if inner is a comparison involving the bound variable
            let is_bound_comparison = match terms.get(inner).clone() {
                TermData::App(Symbol::Named(op), ref args)
                    if (op == "<=" || op == "<") && args.len() == 2 =>
                {
                    is_bound_var(terms, args[0], var_name) || is_bound_var(terms, args[1], var_name)
                }
                _ => false,
            };
            if is_bound_comparison {
                guard_atoms.push(inner);
            } else {
                body_parts.push(arg);
            }
        } else {
            body_parts.push(arg);
        }
    }

    if guard_atoms.is_empty() {
        return None;
    }

    // Extract bounds from the guard atoms
    let (lo, hi) = extract_bounds_from_atoms(terms, &guard_atoms, var_name)?;
    let range = (hi - lo + 1) as u64;
    if range > MAX_FINITE_DOMAIN_COMBOS {
        return None;
    }

    // Reconstruct inner body from remaining parts
    let inner_body = if body_parts.len() == 1 {
        body_parts[0]
    } else if body_parts.len() > 1 {
        terms.mk_or(body_parts)
    } else {
        return None; // No body parts → degenerate case
    };

    Some(BoundedIntInfo {
        lo,
        hi,
        body: inner_body,
    })
}

/// Try to extract bounded integer info from an exists body.
///
/// Matches: `(and bound_atoms... body_parts...)` where some atoms
/// are bounds for the quantified variable.
fn extract_bounded_int_exists(
    terms: &TermStore,
    body: TermId,
    var_name: &str,
) -> Option<BoundedIntInfo> {
    let atoms = collect_and_atoms(terms, body);
    if let Some((lo, hi)) = extract_bounds_from_atoms(terms, &atoms, var_name) {
        let range = (hi - lo + 1) as u64;
        if range > MAX_FINITE_DOMAIN_COMBOS {
            return None;
        }
        // For exists, keep the full body (each disjunct must be independently satisfiable)
        return Some(BoundedIntInfo { lo, hi, body });
    }
    None
}

/// Expand a quantifier with finite-domain variables into a conjunction (forall)
/// or disjunction (exists) of ground instances (#5848).
///
/// For `(forall ((b Bool)) (P b))` → `(and (P true) (P false))`
/// For `(exists ((b Bool)) (P b))` → `(or (P true) (P false))`
///
/// Also handles bounded integer quantifiers (#5848):
/// - `(forall ((i Int)) (=> (and (<= 0 i) (< i 5)) (P i)))` → `(and (P 0) ... (P 4))`
/// - `(exists ((i Int)) (and (<= 0 i) (<= i 2) (P i)))` → `(or (and ...) ...)`
///
/// Finite sorts: `Sort::Bool` (2 values), `Sort::BitVec(w<=8)` (up to 256).
/// Bounded integers: range ≤ 256, single Int variable with guard pattern.
///
/// Returns `None` if the term is not a quantifier, has non-finite variables,
/// or the total combination count exceeds `MAX_FINITE_DOMAIN_COMBOS`.
pub(crate) fn finite_domain_expand(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    let (vars, body, is_forall) = match terms.get(term).clone() {
        TermData::Forall(v, b, _) => (v, b, true),
        TermData::Exists(v, b, _) => (v, b, false),
        _ => return None,
    };

    // Special case: single Int variable with bounded guard pattern (#5848)
    if vars.len() == 1 && vars[0].1 == Sort::Int {
        let (ref var_name, _) = vars[0];
        let bounded_info = if is_forall {
            extract_bounded_int_forall(terms, body, var_name)
        } else {
            extract_bounded_int_exists(terms, body, var_name)
        };
        if let Some(info) = bounded_info {
            let range = (info.hi - info.lo + 1) as usize;
            let mut instances: Vec<TermId> = Vec::with_capacity(range);
            for v in info.lo..=info.hi {
                let mut subst: HashMap<String, TermId> = Default::default();
                subst.insert(var_name.clone(), terms.mk_int(BigInt::from(v)));
                instances.push(subst_vars(terms, info.body, &subst));
            }
            return if is_forall {
                Some(terms.mk_and(instances))
            } else {
                Some(terms.mk_or(instances))
            };
        }
        return None; // Int without bounds → fall back to E-matching
    }

    // Check all vars have finite sorts and compute total combinations
    let mut domain_sizes: Vec<(String, Sort, u64)> = Vec::with_capacity(vars.len());
    let mut total_combos: u64 = 1;
    for (name, sort) in &vars {
        let size = match sort {
            Sort::Bool => 2u64,
            Sort::BitVec(bv) if bv.width <= 8 => 1u64 << bv.width,
            _ => return None, // Non-finite sort
        };
        total_combos = total_combos.saturating_mul(size);
        if total_combos > MAX_FINITE_DOMAIN_COMBOS {
            return None; // Too many combinations
        }
        domain_sizes.push((name.clone(), sort.clone(), size));
    }

    if total_combos == 0 {
        return None;
    }

    // Generate all combinations and instantiate
    let mut instances: Vec<TermId> = Vec::with_capacity(total_combos as usize);
    let mut combo_idx = 0u64;
    while combo_idx < total_combos {
        let mut subst: HashMap<String, TermId> = Default::default();
        let mut remaining = combo_idx;
        for (name, sort, size) in &domain_sizes {
            let val_idx = remaining % size;
            remaining /= size;
            let val_term = match sort {
                Sort::Bool => terms.mk_bool(val_idx != 0),
                Sort::BitVec(bv) => terms.mk_bitvec(BigInt::from(val_idx), bv.width),
                _ => unreachable!(),
            };
            subst.insert(name.clone(), val_term);
        }
        let instance = subst_vars(terms, body, &subst);
        instances.push(instance);
        combo_idx += 1;
    }

    // Combine: forall → and, exists → or
    if is_forall {
        Some(terms.mk_and(instances))
    } else {
        Some(terms.mk_or(instances))
    }
}
