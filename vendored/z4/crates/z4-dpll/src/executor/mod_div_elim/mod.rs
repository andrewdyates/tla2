// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocess `(mod t k)` / `(div t k)` where `k` is an Int constant.
//!
//! This module implements the standard "quotient + remainder" reduction used in
//! `z4-chc` (see `ChcExpr::eliminate_mod()`), but at the `TermId` level for the
//! main SMT executor.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_traits::Signed;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

/// Extract integer constant from a term, if it is one.
fn extract_int_constant(terms: &TermStore, term: TermId) -> Option<BigInt> {
    if let TermData::Const(Constant::Int(n)) = terms.get(term) {
        Some(n.clone())
    } else {
        None
    }
}

pub(super) struct ModDivElimResult {
    pub constraints: Vec<TermId>,
    pub rewritten: Vec<TermId>,
}

pub(super) fn eliminate_int_mod_div_by_constant(
    terms: &mut TermStore,
    formulas: &[TermId],
) -> ModDivElimResult {
    let mut state = ModDivElimState {
        constraints: Vec::new(),
        memo: HashMap::new(),
    };
    let rewritten: Vec<TermId> = formulas
        .iter()
        .map(|&term| state.rewrite_term(terms, term))
        .collect();

    // Output must have same number of formulas as input (#4661)
    debug_assert_eq!(
        rewritten.len(),
        formulas.len(),
        "BUG: mod/div elimination changed formula count from {} to {}",
        formulas.len(),
        rewritten.len()
    );

    ModDivElimResult {
        constraints: state.constraints,
        rewritten,
    }
}

pub(super) fn contains_int_mod_div_by_constant(terms: &TermStore, formulas: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = formulas.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && (name == "mod" || name == "div") =>
            {
                if extract_int_constant(terms, args[1]).is_some() {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!(
                "unhandled TermData variant in contains_int_mod_div_by_constant(): {other:?}"
            ),
        }
    }
    false
}

struct ModDivElimState {
    constraints: Vec<TermId>,
    memo: HashMap<TermId, TermId>,
}

impl ModDivElimState {
    fn rewrite_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        if let Some(&rewritten) = self.memo.get(&term) {
            return rewritten;
        }

        let sort = terms.sort(term).clone();
        let data = terms.get(term).clone();

        let rewritten = match data {
            TermData::Const(_) | TermData::Var(_, _) => term,

            TermData::Not(inner) => {
                let inner_rewritten = self.rewrite_term(terms, inner);
                if inner_rewritten == inner {
                    term
                } else {
                    terms.mk_not(inner_rewritten)
                }
            }

            TermData::Ite(cond, then_term, else_term) => {
                let cond_rewritten = self.rewrite_term(terms, cond);
                let then_rewritten = self.rewrite_term(terms, then_term);
                let else_rewritten = self.rewrite_term(terms, else_term);
                if cond_rewritten == cond
                    && then_rewritten == then_term
                    && else_rewritten == else_term
                {
                    term
                } else {
                    terms.mk_ite(cond_rewritten, then_rewritten, else_rewritten)
                }
            }

            // NOTE: Avoid introducing free vars across binders.
            // Quantified terms are handled separately by the executor; keep them unchanged here.
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => term,

            TermData::App(Symbol::Named(name), args) if name == "mod" && args.len() == 2 => {
                if let Some(k) = extract_int_constant(terms, args[1]) {
                    self.rewrite_mod(terms, args[0], k)
                } else {
                    let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                    if changed {
                        terms.mk_mod(rewritten_args[0], rewritten_args[1])
                    } else {
                        term
                    }
                }
            }

            TermData::App(Symbol::Named(name), args) if name == "div" && args.len() == 2 => {
                if let Some(k) = extract_int_constant(terms, args[1]) {
                    self.rewrite_div(terms, args[0], k)
                } else {
                    let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                    if changed {
                        terms.mk_intdiv(rewritten_args[0], rewritten_args[1])
                    } else {
                        term
                    }
                }
            }

            TermData::App(sym, args) => {
                let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                if changed {
                    terms.mk_app(sym, rewritten_args, sort)
                } else {
                    term
                }
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in rewrite_term(): {other:?}"),
        };

        self.memo.insert(term, rewritten);
        rewritten
    }

    fn rewrite_args(&mut self, terms: &mut TermStore, args: &[TermId]) -> (bool, Vec<TermId>) {
        let mut changed = false;
        let mut rewritten_args = Vec::with_capacity(args.len());
        for &arg in args {
            let rewritten = self.rewrite_term(terms, arg);
            changed |= rewritten != arg;
            rewritten_args.push(rewritten);
        }
        (changed, rewritten_args)
    }

    fn rewrite_mod(&mut self, terms: &mut TermStore, dividend: TermId, k: BigInt) -> TermId {
        // SMT-LIB total semantics (as used in z4-chc): (mod x 0) = x
        if k == BigInt::from(0) {
            return self.rewrite_term(terms, dividend);
        }

        let x = self.rewrite_term(terms, dividend);
        let q = terms.mk_fresh_var("_mod_q", Sort::Int);
        let r = terms.mk_fresh_var("_mod_r", Sort::Int);

        self.add_division_constraints(terms, x, k, q, r);
        r
    }

    fn rewrite_div(&mut self, terms: &mut TermStore, dividend: TermId, k: BigInt) -> TermId {
        // SMT-LIB total semantics (as used in z4-chc): (div x 0) = 0
        if k == BigInt::from(0) {
            return terms.mk_int(BigInt::from(0));
        }

        let x = self.rewrite_term(terms, dividend);
        let q = terms.mk_fresh_var("_div_q", Sort::Int);
        let r = terms.mk_fresh_var("_div_r", Sort::Int);

        self.add_division_constraints(terms, x, k, q, r);
        q
    }

    fn add_division_constraints(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        k: BigInt,
        q: TermId,
        r: TermId,
    ) {
        // Divisor must be non-zero (callers handle k==0 case before reaching here) (#4661)
        debug_assert!(
            k != BigInt::from(0),
            "BUG: add_division_constraints called with zero divisor"
        );

        let zero = terms.mk_int(BigInt::from(0));
        let k_term = terms.mk_int(k.clone());
        let k_abs_term = terms.mk_int(k.abs());

        // x = k*q + r
        let k_times_q = terms.mk_mul(vec![k_term, q]);
        let k_times_q_plus_r = terms.mk_add(vec![k_times_q, r]);
        let eq = terms.mk_eq(dividend, k_times_q_plus_r);

        // 0 <= r
        let r_ge_0 = terms.mk_ge(r, zero);

        // r < |k|
        let r_lt_k = terms.mk_lt(r, k_abs_term);

        self.constraints.push(eq);
        self.constraints.push(r_ge_0);
        self.constraints.push(r_lt_k);
    }
}
