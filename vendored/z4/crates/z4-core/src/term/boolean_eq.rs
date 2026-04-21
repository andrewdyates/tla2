// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality, ITE, and distinct term constructors.
//!
//! Boolean/logical connectives (not, and, or, implies, xor) are in `boolean`.

use super::*;

impl TermStore {
    /// Create if-then-else
    pub fn mk_ite(&mut self, cond: TermId, then_term: TermId, else_term: TermId) -> TermId {
        debug_assert!(
            self.sort(cond) == &Sort::Bool,
            "BUG: mk_ite condition must be Bool, got {:?}",
            self.sort(cond)
        );
        debug_assert!(
            self.sort(then_term) == self.sort(else_term),
            "BUG: mk_ite branches must have same sort, got {:?} vs {:?}",
            self.sort(then_term),
            self.sort(else_term)
        );
        // Constant condition simplification
        match self.get(cond) {
            TermData::Const(Constant::Bool(true)) => return then_term,
            TermData::Const(Constant::Bool(false)) => return else_term,
            _ => {}
        }

        // Negated condition normalization: (ite (not c) a b) -> (ite c b a)
        // This normalizes to positive conditions, reducing structural variations
        // and potentially enabling further simplifications after the swap.
        if let Some(inner_cond) = self.get_not_inner(cond) {
            return self.mk_ite(inner_cond, else_term, then_term);
        }

        // Same branches: (ite c x x) = x
        if then_term == else_term {
            return then_term;
        }

        // Boolean branch simplifications
        let true_term = self.true_term();
        let false_term = self.false_term();

        // (ite c true false) = c
        if then_term == true_term && else_term == false_term {
            return cond;
        }

        // (ite c false true) = (not c)
        if then_term == false_term && else_term == true_term {
            return self.mk_not(cond);
        }

        // Get the result sort to check if it's Bool
        let result_sort = self.sort(then_term).clone();

        // Boolean-specific simplifications (only when result is Bool)
        if result_sort == Sort::Bool {
            // (ite c c false) = c
            if then_term == cond && else_term == false_term {
                return cond;
            }
            // (ite c true c) = c
            if then_term == true_term && else_term == cond {
                return cond;
            }
            // (ite c x false) = (and c x)
            if else_term == false_term {
                return self.mk_and(vec![cond, then_term]);
            }
            // (ite c true x) = (or c x)
            if then_term == true_term {
                return self.mk_or(vec![cond, else_term]);
            }
            // (ite c false x) = (and (not c) x)
            if then_term == false_term {
                let not_cond = self.mk_not(cond);
                return self.mk_and(vec![not_cond, else_term]);
            }
            // (ite c x true) = (or (not c) x)
            if else_term == true_term {
                let not_cond = self.mk_not(cond);
                return self.mk_or(vec![not_cond, then_term]);
            }

            // Nested ite simplifications with same condition
            // (ite c (ite c x y) z) = (ite c x z)
            if let TermData::Ite(nested_cond, nested_then, _) = self.get(then_term).clone() {
                if nested_cond == cond {
                    return self.mk_ite(cond, nested_then, else_term);
                }
            }
            // (ite c x (ite c y z)) = (ite c x z)
            if let TermData::Ite(nested_cond, _, nested_else) = self.get(else_term).clone() {
                if nested_cond == cond {
                    return self.mk_ite(cond, then_term, nested_else);
                }
            }
        }

        self.intern(TermData::Ite(cond, then_term, else_term), result_sort)
    }

    /// Create equality with constant folding
    pub fn mk_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_eq expects same sort, got {:?} = {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Reflexive: x = x is true
        if lhs == rhs {
            return self.true_term();
        }

        // Constant folding: different constants are not equal
        // (Note: since we intern constants, if lhs != rhs and both are constants,
        // they must be different values)
        let lhs_is_const = matches!(self.get(lhs), TermData::Const(_));
        let rhs_is_const = matches!(self.get(rhs), TermData::Const(_));
        if lhs_is_const && rhs_is_const {
            return self.false_term();
        }

        // Boolean equality simplifications (iff-style)
        // (= x true) -> x
        // (= x false) -> (not x)
        let true_term = self.true_term();
        let false_term = self.false_term();

        if rhs == true_term && *self.sort(lhs) == Sort::Bool {
            return lhs;
        }
        if lhs == true_term && *self.sort(rhs) == Sort::Bool {
            return rhs;
        }
        if rhs == false_term && *self.sort(lhs) == Sort::Bool {
            return self.mk_not(lhs);
        }
        if lhs == false_term && *self.sort(rhs) == Sort::Bool {
            return self.mk_not(rhs);
        }

        // Boolean complement detection: (= x (not x)) -> false
        // Check if lhs is (not rhs) or rhs is (not lhs)
        if *self.sort(lhs) == Sort::Bool {
            if let Some(inner) = self.get_not_inner(lhs) {
                if inner == rhs {
                    return self.false_term();
                }
            }
            if let Some(inner) = self.get_not_inner(rhs) {
                if inner == lhs {
                    return self.false_term();
                }
            }

            // Negation lifting: (= (not x) (not y)) -> (= x y)
            if let (Some(lhs_inner), Some(rhs_inner)) =
                (self.get_not_inner(lhs), self.get_not_inner(rhs))
            {
                return self.mk_eq(lhs_inner, rhs_inner);
            }
        }

        // ITE-equality simplifications
        // (= (ite c a b) a) -> (or c (= b a))
        // (= (ite c a b) b) -> (or (not c) (= a b))
        // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))

        // Check if lhs is an ITE
        if let TermData::Ite(c, a, b) = self.get(lhs).clone() {
            // (= (ite c a b) a) -> (or c (= b a))
            if rhs == a {
                let eq_ba = self.mk_eq(b, a);
                return self.mk_or(vec![c, eq_ba]);
            }
            // (= (ite c a b) b) -> (or (not c) (= a b))
            if rhs == b {
                let not_c = self.mk_not(c);
                let eq_ab = self.mk_eq(a, b);
                return self.mk_or(vec![not_c, eq_ab]);
            }
            // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))
            if let TermData::Ite(c2, x, y) = self.get(rhs).clone() {
                if c == c2 {
                    let eq_ax = self.mk_eq(a, x);
                    let eq_by = self.mk_eq(b, y);
                    return self.mk_ite(c, eq_ax, eq_by);
                }
            }
        }

        // Check if rhs is an ITE (symmetric cases)
        if let TermData::Ite(c, a, b) = self.get(rhs).clone() {
            // (= a (ite c a b)) -> (or c (= b a))
            if lhs == a {
                let eq_ba = self.mk_eq(b, a);
                return self.mk_or(vec![c, eq_ba]);
            }
            // (= b (ite c a b)) -> (or (not c) (= a b))
            if lhs == b {
                let not_c = self.mk_not(c);
                let eq_ab = self.mk_eq(a, b);
                return self.mk_or(vec![not_c, eq_ab]);
            }
        }

        // General ITE expansion: (= (ite c a b) val) -> (ite c (= a val) (= b val))
        // This ensures theories can reason about each branch separately.
        // Only expand for non-Bool sorts since Bool ITE has its own simplifications.
        if let TermData::Ite(c, a, b) = self.get(lhs).clone() {
            if *self.sort(a) != Sort::Bool {
                let eq_a = self.mk_eq(a, rhs);
                let eq_b = self.mk_eq(b, rhs);
                return self.mk_ite(c, eq_a, eq_b);
            }
        }
        if let TermData::Ite(c, a, b) = self.get(rhs).clone() {
            if *self.sort(a) != Sort::Bool {
                let eq_a = self.mk_eq(lhs, a);
                let eq_b = self.mk_eq(lhs, b);
                return self.mk_ite(c, eq_a, eq_b);
            }
        }

        // Array store equality simplifications (#920, #4479)
        if let Some(result) = self.try_simplify_store_eq(lhs, rhs) {
            return result;
        }

        // #3421 previously normalized Bool-Bool equality to ite(a, b, not(b)).
        // Removed (#6869): the ITE decomposition destroys the equality term,
        // preventing EUF from seeing alias chains like (= b (= x y)) where
        // congruence closure needs the explicit equality. The Tseitin encoder
        // already handles Bool-Bool equalities with biconditional clauses
        // (tseitin.rs:encode_eq), so propositional semantics are preserved.

        // Canonical order
        let (a, b) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
        self.intern(TermData::App(Symbol::named("="), vec![a, b]), Sort::Bool)
    }

    /// Array store equality simplifications for `mk_eq`.
    ///
    /// Handles two patterns:
    /// - Self-store (#920): `(= (store a i v) a)` -> `(= (select a i) v)`
    /// - Store-store (#4479): `(= (store a i v1) (store a i v2))` -> `(= v1 v2)`
    ///   when base and index are syntactically identical (ROW1+ROW2 soundness).
    fn try_simplify_store_eq(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        // Extract store components from lhs
        let lhs_store = match self.get(lhs).clone() {
            TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                Some((args[0], args[1], args[2]))
            }
            _ => None,
        };
        // Extract store components from rhs
        let rhs_store = match self.get(rhs).clone() {
            TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                Some((args[0], args[1], args[2]))
            }
            _ => None,
        };

        // Self-store: (= (store a i v) a) -> (= (select a i) v)
        if let Some((base, idx, val)) = lhs_store {
            if rhs == base {
                let sel = self.mk_select(base, idx);
                return Some(self.mk_eq(sel, val));
            }
        }
        if let Some((base, idx, val)) = rhs_store {
            if lhs == base {
                let sel = self.mk_select(base, idx);
                return Some(self.mk_eq(sel, val));
            }
        }

        // Store-store: (= (store a i v1) (store a i v2)) -> (= v1 v2)
        if let (Some((base1, idx1, val1)), Some((base2, idx2, val2))) = (lhs_store, rhs_store) {
            if base1 == base2 && idx1 == idx2 {
                return Some(self.mk_eq(val1, val2));
            }
        }

        None
    }

    /// Create distinct with duplicate detection and constant folding
    ///
    /// N-ary distinct (>=3 args) is expanded to a conjunction of pairwise inequalities.
    /// This ensures all theory solvers (LIA, LRA, etc.) can reason about distinctness
    /// without needing special distinct handling. Fixes #301.
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_distinct(&mut self, args: Vec<TermId>) -> TermId {
        if args.len() <= 1 {
            return self.true_term();
        }

        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: mk_distinct expects same sort args"
        );

        // Duplicate detection: if any two terms are identical, result is false
        let mut sorted_args = args.clone();
        sorted_args.sort();
        for i in 1..sorted_args.len() {
            if sorted_args[i - 1] == sorted_args[i] {
                return self.false_term();
            }
        }

        // Binary distinct: normalize to NOT(eq) so Tseitin encoding assigns
        // related CNF variables, enabling contradiction detection
        if args.len() == 2 {
            let eq = self.mk_eq(args[0], args[1]);
            return self.mk_not(eq);
        }

        // N-ary distinct (>=3 args): expand to conjunction of pairwise inequalities
        // (distinct a b c d) => (and (not (= a b)) (not (= a c)) (not (= a d))
        //                            (not (= b c)) (not (= b d)) (not (= c d)))
        // This fixes #301: LIA/LRA solvers don't handle n-ary distinct directly
        let mut pairwise_neqs = Vec::new();
        for i in 0..args.len() {
            for j in (i + 1)..args.len() {
                let eq = self.mk_eq(args[i], args[j]);
                let neq = self.mk_not(eq);
                pairwise_neqs.push(neq);
            }
        }

        // Constant folding: if all args are distinct constants, result is true
        // (Since duplicates are detected above, if all args are constants, result is true)
        let all_consts = args
            .iter()
            .all(|&id| matches!(self.get(id), TermData::Const(_)));
        if all_consts {
            return self.true_term();
        }

        self.mk_and(pairwise_neqs)
    }
}
