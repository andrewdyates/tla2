// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PropagateValues preprocessing pass
//!
//! Eliminates ground equalities of the form `(= EXPR CONST)` by building a
//! substitution table and rewriting all occurrences of `EXPR` to `CONST`.
//!
//! This is critical for QF_UFLIA benchmarks that define UF functions via
//! exhaustive lookup tables (e.g., `(= (Succ 0) 1)`, `(= (Sum 3 4) 7)`).
//! Without this pass, all ground UF equalities survive preprocessing and
//! become theory atoms, causing combinatorial explosion in DPLL(T).
//!
//! # Reference
//! - Z3: `reference/z3/src/ast/simplifiers/propagate_values.cpp`
//! - Design: `designs/2026-02-25-issue-5081-propagate-values-preprocess.md`
//! - Issue: #5081

use super::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Symbol, TermData};
use z4_core::{TermId, TermStore};

/// Propagates ground equalities `(= EXPR CONST)` through assertions.
///
/// Phase 1: Scan assertions for `(= EXPR CONST)` where CONST is a concrete
/// constant and EXPR is any non-constant term (including function applications).
///
/// Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
/// The defining equalities themselves are preserved because EUF needs them
/// to compute congruence closure on non-ground applications like `Succ(x)`.
///
/// This is important for correctness: removing `(= (Succ 0) 1)` from the
/// formula makes `Succ` truly uninterpreted, which can change satisfiability.
pub(crate) struct PropagateValues {
    /// Substitution map: expression TermId -> constant TermId
    value_map: HashMap<TermId, TermId>,
    /// Set of defining equality assertions (TermIds) to skip during rewriting
    defining_equalities: hashbrown::HashSet<TermId>,
    /// Rewrite cache for the current iteration
    cache: HashMap<TermId, TermId>,
}

impl PropagateValues {
    pub(crate) fn new() -> Self {
        Self {
            value_map: HashMap::new(),
            defining_equalities: hashbrown::HashSet::new(),
            cache: HashMap::new(),
        }
    }

    /// Check if a term is a concrete constant.
    fn is_constant(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(_))
    }

    /// Check if a term is ground (contains no free variables).
    ///
    /// Ground terms consist only of constants and function applications over
    /// other ground terms. Variables make a term non-ground.
    fn is_ground(terms: &TermStore, term: TermId) -> bool {
        match terms.get(term) {
            TermData::Const(_) => true,
            TermData::Var(_, _) => false,
            TermData::App(_, args) => args.iter().all(|&a| Self::is_ground(terms, a)),
            TermData::Not(inner) => Self::is_ground(terms, *inner),
            TermData::Ite(c, t, e) => {
                Self::is_ground(terms, *c)
                    && Self::is_ground(terms, *t)
                    && Self::is_ground(terms, *e)
            }
            _ => false,
        }
    }

    /// Extract a value equality from an assertion: `(= EXPR CONST)` or `(= CONST EXPR)`.
    ///
    /// Returns `Some((expr, const))` if the assertion is a top-level equality
    /// where exactly one side is a concrete constant and the other is a ground
    /// (variable-free) non-constant term.
    fn extract_value_equality(terms: &TermStore, assertion: TermId) -> Option<(TermId, TermId)> {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_const = Self::is_constant(terms, lhs);
                let rhs_const = Self::is_constant(terms, rhs);
                match (lhs_const, rhs_const) {
                    (false, true) if Self::is_ground(terms, lhs) => Some((lhs, rhs)),
                    (true, false) if Self::is_ground(terms, rhs) => Some((rhs, lhs)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Rewrite a term by substituting known value mappings.
    ///
    /// Bottom-up: first rewrite all children, then check if the result
    /// matches a known value in `value_map`. Uses canonical constructors
    /// (mk_eq, mk_add, etc.) when rebuilding to trigger constant folding.
    fn rewrite(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        if let Some(&cached) = self.cache.get(&term) {
            return cached;
        }

        // Check direct substitution first
        if let Some(&value) = self.value_map.get(&term) {
            self.cache.insert(term, value);
            return value;
        }

        let result = match terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,

            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.rewrite(terms, a)).collect();

                if new_args == args {
                    term
                } else {
                    // Rebuild using canonical constructors for constant folding.
                    // BV and array constructors do constant folding when all
                    // arguments are constants, which is critical for QF_ABV
                    // benchmarks where PropagateValues substitutes array
                    // select results with concrete BV constants.
                    let rebuilt = match sym.name() {
                        // Boolean / arithmetic
                        "=" if new_args.len() == 2 => terms.mk_eq(new_args[0], new_args[1]),
                        "+" => terms.mk_add(new_args),
                        "-" => terms.mk_sub(new_args),
                        "*" => terms.mk_mul(new_args),
                        "<" if new_args.len() == 2 => terms.mk_lt(new_args[0], new_args[1]),
                        "<=" if new_args.len() == 2 => terms.mk_le(new_args[0], new_args[1]),
                        ">" if new_args.len() == 2 => terms.mk_gt(new_args[0], new_args[1]),
                        ">=" if new_args.len() == 2 => terms.mk_ge(new_args[0], new_args[1]),
                        "div" if new_args.len() == 2 => terms.mk_intdiv(new_args[0], new_args[1]),
                        "mod" if new_args.len() == 2 => terms.mk_mod(new_args[0], new_args[1]),
                        "abs" if new_args.len() == 1 => terms.mk_abs(new_args[0]),

                        // BV arithmetic (constant folding on all-constant args)
                        "bvadd" if new_args.len() == 2 => terms.mk_bvadd(new_args),
                        "bvsub" if new_args.len() == 2 => terms.mk_bvsub(new_args),
                        "bvmul" if new_args.len() == 2 => terms.mk_bvmul(new_args),

                        // BV bitwise
                        "bvand" if new_args.len() == 2 => terms.mk_bvand(new_args),
                        "bvor" if new_args.len() == 2 => terms.mk_bvor(new_args),
                        "bvxor" if new_args.len() == 2 => terms.mk_bvxor(new_args),
                        "bvnot" if new_args.len() == 1 => terms.mk_bvnot(new_args[0]),
                        "bvneg" if new_args.len() == 1 => terms.mk_bvneg(new_args[0]),
                        "bvnand" if new_args.len() == 2 => terms.mk_bvnand(new_args),
                        "bvnor" if new_args.len() == 2 => terms.mk_bvnor(new_args),
                        "bvxnor" if new_args.len() == 2 => terms.mk_bvxnor(new_args),

                        // BV shifts
                        "bvshl" if new_args.len() == 2 => terms.mk_bvshl(new_args),
                        "bvlshr" if new_args.len() == 2 => terms.mk_bvlshr(new_args),
                        "bvashr" if new_args.len() == 2 => terms.mk_bvashr(new_args),

                        // BV division
                        "bvudiv" if new_args.len() == 2 => terms.mk_bvudiv(new_args),
                        "bvurem" if new_args.len() == 2 => terms.mk_bvurem(new_args),
                        "bvsdiv" if new_args.len() == 2 => terms.mk_bvsdiv(new_args),
                        "bvsrem" if new_args.len() == 2 => terms.mk_bvsrem(new_args),
                        "bvsmod" if new_args.len() == 2 => terms.mk_bvsmod(new_args),

                        // BV comparisons
                        "bvult" if new_args.len() == 2 => terms.mk_bvult(new_args[0], new_args[1]),
                        "bvule" if new_args.len() == 2 => terms.mk_bvule(new_args[0], new_args[1]),
                        "bvugt" if new_args.len() == 2 => terms.mk_bvugt(new_args[0], new_args[1]),
                        "bvuge" if new_args.len() == 2 => terms.mk_bvuge(new_args[0], new_args[1]),
                        "bvslt" if new_args.len() == 2 => terms.mk_bvslt(new_args[0], new_args[1]),
                        "bvsle" if new_args.len() == 2 => terms.mk_bvsle(new_args[0], new_args[1]),
                        "bvsgt" if new_args.len() == 2 => terms.mk_bvsgt(new_args[0], new_args[1]),
                        "bvsge" if new_args.len() == 2 => terms.mk_bvsge(new_args[0], new_args[1]),
                        "bvcomp" if new_args.len() == 2 => {
                            terms.mk_bvcomp(new_args[0], new_args[1])
                        }

                        // BV concat/extract (extract uses indexed params)
                        "concat" if new_args.len() == 2 => terms.mk_bvconcat(new_args),

                        // Array operations (read-over-write simplification)
                        "select" if new_args.len() == 2 => {
                            terms.mk_select(new_args[0], new_args[1])
                        }
                        "store" if new_args.len() == 3 => {
                            terms.mk_store(new_args[0], new_args[1], new_args[2])
                        }

                        // Indexed BV operations: extract, zero_extend,
                        // sign_extend, repeat, rotate_left, rotate_right
                        "extract" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 2 {
                                    terms.mk_bvextract(indices[0], indices[1], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                        "zero_extend" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 1 {
                                    terms.mk_bvzero_extend(indices[0], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                        "sign_extend" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 1 {
                                    terms.mk_bvsign_extend(indices[0], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                        "repeat" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 1 {
                                    terms.mk_bvrepeat(indices[0], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                        "rotate_left" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 1 {
                                    terms.mk_bvrotate_left(indices[0], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                        "rotate_right" if new_args.len() == 1 => {
                            if let Symbol::Indexed(_, indices) = &sym {
                                if indices.len() == 1 {
                                    terms.mk_bvrotate_right(indices[0], new_args[0])
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            } else {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }

                        _ => {
                            let sort = terms.sort(term).clone();
                            terms.mk_app(sym.clone(), new_args, sort)
                        }
                    };
                    // Check if the rebuilt term is now in value_map
                    if let Some(&value) = self.value_map.get(&rebuilt) {
                        value
                    } else {
                        rebuilt
                    }
                }
            }

            TermData::Not(inner) => {
                let new_inner = self.rewrite(terms, inner);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }

            TermData::Ite(c, t, e) => {
                let nc = self.rewrite(terms, c);
                let nt = self.rewrite(terms, t);
                let ne = self.rewrite(terms, e);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }

            // Let, Forall, Exists — pass through (not needed for ground value propagation)
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => term,
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in rewrite(): {other:?}"),
        };

        self.cache.insert(term, result);
        result
    }
}

impl Default for PropagateValues {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for PropagateValues {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        // Phase 1: Scan assertions for ground equalities (= EXPR CONST)
        let mut new_entries = false;
        for &assertion in assertions.iter() {
            if let Some((expr, value)) = Self::extract_value_equality(terms, assertion) {
                // Only insert if not already known (avoid overwriting)
                if !self.value_map.contains_key(&expr) {
                    self.value_map.insert(expr, value);
                    self.defining_equalities.insert(assertion);
                    new_entries = true;
                }
            }
        }

        if self.value_map.is_empty() {
            return false;
        }

        // Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
        // Defining equalities like (= (Succ 0) 1) are preserved unchanged because
        // EUF needs them to compute congruence closure on non-ground applications.
        // Without them, Succ becomes truly uninterpreted and the formula changes.
        let mut modified = new_entries;
        for assertion in assertions.iter_mut() {
            if self.defining_equalities.contains(assertion) {
                continue;
            }
            let new = self.rewrite(terms, *assertion);
            if new != *assertion {
                *assertion = new;
                modified = true;
            }
        }

        // Note: We do NOT remove tautological assertions. The defining equalities
        // must remain for EUF correctness, and any tautological rewrites in
        // non-defining assertions are harmless (Tseitin encodes them trivially).

        modified
    }

    fn reset(&mut self) {
        // Clear rewrite cache between fixed-point iterations so new
        // substitutions from other passes can be picked up.
        self.cache.clear();
        // Preserve value_map and defining_equalities across iterations —
        // accumulated ground equalities remain valid.
    }
}

#[cfg(test)]
mod tests;
