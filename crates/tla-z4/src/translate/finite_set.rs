// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Finite set encoding as SMT arrays for TLA+ set operations.
//!
//! Encodes TLA+ finite sets as SMT arrays `(Array Int Bool)` where
//! `(select S x) = true` iff `x` is a member of set `S`.
//!
//! # Encoding
//!
//! | TLA+ Operation       | SMT Array Encoding                                       |
//! |----------------------|----------------------------------------------------------|
//! | `{e1, ..., en}`      | `(store (store (const false) e1 true) ... en true)`      |
//! | `x \in S`            | `(select S x)`                                           |
//! | `S \cup T`           | pointwise: `\A i : (select R i) = (or (sel S) (sel T))` |
//! | `S \cap T`           | pointwise: `\A i : (select R i) = (and (sel S) (sel T))`|
//! | `S \ T`              | pointwise: `(and (sel S) (not (sel T)))`                 |
//! | `S \subseteq T`      | `\A x \in S : x \in T` via finite expansion             |
//! | `Cardinality(S)`     | count of true entries for finite sets                    |
//!
//! The finite-expansion approach works because TLA+ model checking always
//! operates over finite domains. For a known universe `U = {u1, ..., un}`,
//! set operations are expanded pointwise over `U`.
//!
//! # Usage
//!
//! ```no_run
//! use tla_z4::translate::finite_set::FiniteSetEncoder;
//! use tla_z4::Z4Translator;
//!
//! let mut trans = Z4Translator::new_with_arrays();
//! let enc = FiniteSetEncoder::new();
//! // ... use enc methods to build set terms
//! ```
//!
//! Part of #3749

use z4_dpll::api::{Sort, Term};

use crate::error::Z4Result;

use super::Z4Translator;

/// Encoder for finite sets as SMT arrays.
///
/// Provides methods to build and manipulate set-as-array terms
/// within a [`Z4Translator`] context.
///
/// Sets are represented as `(Array Int Bool)`:
/// - The index sort is `Int` (elements are integers or interned values).
/// - The element sort is `Bool` (`true` = member, `false` = not member).
#[derive(Debug, Clone)]
pub struct FiniteSetEncoder {
    /// The index sort for array-based sets (always Int).
    index_sort: Sort,
}

impl Default for FiniteSetEncoder {
    fn default() -> Self {
        Self::new()
    }
}

impl FiniteSetEncoder {
    /// Create a new finite set encoder.
    ///
    /// Uses `Int` as the index sort for set membership arrays.
    #[must_use]
    pub fn new() -> Self {
        Self {
            index_sort: Sort::Int,
        }
    }

    /// Get the SMT sort for a set (Array Int Bool).
    #[must_use]
    pub fn set_sort(&self) -> Sort {
        Sort::array(self.index_sort.clone(), Sort::Bool)
    }

    /// Encode an empty set as a constant-false array.
    ///
    /// `{}` => `((as const (Array Int Bool)) false)`
    pub fn empty_set(&self, trans: &mut Z4Translator) -> Z4Result<Term> {
        let false_val = trans.solver_mut().bool_const(false);
        Ok(trans
            .solver_mut()
            .try_const_array(self.index_sort.clone(), false_val)?)
    }

    /// Encode a finite set enumeration `{e1, ..., en}` as an SMT array.
    ///
    /// Builds: `(store (store ... (store (const false) e1 true) ... en true)`
    ///
    /// Each element must be translatable to an Int term (the index sort).
    pub fn encode_set_enum(
        &self,
        trans: &mut Z4Translator,
        element_terms: &[Term],
    ) -> Z4Result<Term> {
        let true_val = trans.solver_mut().bool_const(true);
        let mut arr = self.empty_set(trans)?;

        for &elem in element_terms {
            arr = trans.solver_mut().try_store(arr, elem, true_val)?;
        }

        Ok(arr)
    }

    /// Encode set membership `x \in S` as `(select S x)`.
    ///
    /// Returns a Bool-sorted term that is true iff `x` is in `S`.
    pub fn encode_membership(
        &self,
        trans: &mut Z4Translator,
        element: Term,
        set: Term,
    ) -> Z4Result<Term> {
        Ok(trans.solver_mut().try_select(set, element)?)
    }

    /// Encode set union `S \cup T` for sets over a known finite universe.
    ///
    /// For each element `u` in `universe`: `(select result u) = (or (select S u) (select T u))`
    ///
    /// Returns the result set term and asserts the pointwise constraints.
    pub fn encode_union(
        &self,
        trans: &mut Z4Translator,
        set_s: Term,
        set_t: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        let result = self.declare_fresh_set(trans, "union")?;

        for &u in universe {
            let in_s = trans.solver_mut().try_select(set_s, u)?;
            let in_t = trans.solver_mut().try_select(set_t, u)?;
            let in_result = trans.solver_mut().try_select(result, u)?;
            let s_or_t = trans.solver_mut().try_or(in_s, in_t)?;
            let eq = trans.solver_mut().try_eq(in_result, s_or_t)?;
            trans.assert(eq);
        }

        Ok(result)
    }

    /// Encode set intersection `S \cap T` for sets over a known finite universe.
    ///
    /// For each element `u` in `universe`: `(select result u) = (and (select S u) (select T u))`
    pub fn encode_intersect(
        &self,
        trans: &mut Z4Translator,
        set_s: Term,
        set_t: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        let result = self.declare_fresh_set(trans, "intersect")?;

        for &u in universe {
            let in_s = trans.solver_mut().try_select(set_s, u)?;
            let in_t = trans.solver_mut().try_select(set_t, u)?;
            let in_result = trans.solver_mut().try_select(result, u)?;
            let s_and_t = trans.solver_mut().try_and(in_s, in_t)?;
            let eq = trans.solver_mut().try_eq(in_result, s_and_t)?;
            trans.assert(eq);
        }

        Ok(result)
    }

    /// Encode set difference `S \ T` for sets over a known finite universe.
    ///
    /// For each element `u` in `universe`: `(select result u) = (and (select S u) (not (select T u)))`
    pub fn encode_set_minus(
        &self,
        trans: &mut Z4Translator,
        set_s: Term,
        set_t: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        let result = self.declare_fresh_set(trans, "setminus")?;

        for &u in universe {
            let in_s = trans.solver_mut().try_select(set_s, u)?;
            let in_t = trans.solver_mut().try_select(set_t, u)?;
            let not_in_t = trans.solver_mut().try_not(in_t)?;
            let in_result = trans.solver_mut().try_select(result, u)?;
            let s_and_not_t = trans.solver_mut().try_and(in_s, not_in_t)?;
            let eq = trans.solver_mut().try_eq(in_result, s_and_not_t)?;
            trans.assert(eq);
        }

        Ok(result)
    }

    /// Encode subset check `S \subseteq T` over a known finite universe.
    ///
    /// `\A u \in universe : (select S u) => (select T u)`
    ///
    /// Returns a Bool-sorted term.
    pub fn encode_subseteq(
        &self,
        trans: &mut Z4Translator,
        set_s: Term,
        set_t: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        if universe.is_empty() {
            // Empty universe: vacuously true
            return Ok(trans.solver_mut().bool_const(true));
        }

        let mut conjuncts = Vec::with_capacity(universe.len());
        for &u in universe {
            let in_s = trans.solver_mut().try_select(set_s, u)?;
            let in_t = trans.solver_mut().try_select(set_t, u)?;
            let implication = trans.solver_mut().try_implies(in_s, in_t)?;
            conjuncts.push(implication);
        }

        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = trans.solver_mut().try_and(result, c)?;
        }
        Ok(result)
    }

    /// Encode set equality `S = T` over a known finite universe.
    ///
    /// `\A u \in universe : (select S u) <=> (select T u)`
    pub fn encode_set_eq(
        &self,
        trans: &mut Z4Translator,
        set_s: Term,
        set_t: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        if universe.is_empty() {
            return Ok(trans.solver_mut().bool_const(true));
        }

        let mut conjuncts = Vec::with_capacity(universe.len());
        for &u in universe {
            let in_s = trans.solver_mut().try_select(set_s, u)?;
            let in_t = trans.solver_mut().try_select(set_t, u)?;
            let eq = trans.solver_mut().try_eq(in_s, in_t)?;
            conjuncts.push(eq);
        }

        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = trans.solver_mut().try_and(result, c)?;
        }
        Ok(result)
    }

    /// Encode cardinality of a finite set over a known universe.
    ///
    /// `Cardinality(S)` = sum over universe of `IF (select S u) THEN 1 ELSE 0`
    ///
    /// Returns an Int-sorted term representing the count.
    pub fn encode_cardinality(
        &self,
        trans: &mut Z4Translator,
        set: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        let zero = trans.solver_mut().int_const(0);
        let one = trans.solver_mut().int_const(1);

        if universe.is_empty() {
            return Ok(zero);
        }

        // Build sum: IF (select S u1) THEN 1 ELSE 0 + IF (select S u2) ...
        let mut sum = zero;
        for &u in universe {
            let in_set = trans.solver_mut().try_select(set, u)?;
            let contribution = trans.solver_mut().try_ite(in_set, one, zero)?;
            sum = trans.solver_mut().try_add(sum, contribution)?;
        }

        Ok(sum)
    }

    /// Declare a fresh set variable (Array Int Bool) with a unique name.
    fn declare_fresh_set(&self, trans: &mut Z4Translator, prefix: &str) -> Z4Result<Term> {
        let name = trans.fresh_name(prefix);
        Ok(trans.solver_mut().declare_const(&name, self.set_sort()))
    }
}

impl Z4Translator {
    /// Mutable access to the underlying solver for array operations.
    ///
    /// This is `pub(crate)` to allow the `FiniteSetEncoder` to build
    /// array terms without exposing the full Solver API publicly.
    pub(crate) fn solver_mut(&mut self) -> &mut z4_dpll::api::Solver {
        &mut self.solver
    }

    /// Generate a fresh variable name with a given prefix.
    ///
    /// Uses an internal counter to avoid collisions.
    pub(crate) fn fresh_name(&mut self, prefix: &str) -> String {
        // Use the size of all var maps as a simple monotonic counter
        let id = self.vars.len()
            + self.func_vars.len()
            + self.tuple_vars.len()
            + self.record_vars.len()
            + self.seq_vars.len()
            + self.array_func_vars.len();
        format!("__z4_{prefix}_{id}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z4_dpll::api::SolveResult;

    /// Helper: create a translator with array logic support.
    fn array_translator() -> Z4Translator {
        Z4Translator::new_with_arrays()
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_set_membership_is_unsat() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // Declare x: Int
        let x = trans.solver_mut().declare_const("x", Sort::Int);

        // Build empty set {}
        let empty = enc.empty_set(&mut trans).unwrap();

        // Assert x \in {} (should be UNSAT)
        let member = enc.encode_membership(&mut trans, x, empty).unwrap();
        trans.assert(member);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_enum_membership_sat() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // Build set {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // Declare x, assert x \in {1, 2, 3}
        let x = trans.solver_mut().declare_const("x", Sort::Int);
        let member = enc.encode_membership(&mut trans, x, set).unwrap();
        trans.assert(member);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));

        // The model should assign x to one of {1, 2, 3}
        let model = trans.get_model().unwrap();
        let x_val = model.int_val("x").unwrap();
        let x_i64: i64 = x_val.try_into().unwrap();
        assert!(
            (1..=3).contains(&x_i64),
            "expected x in {{1, 2, 3}}, got {x_i64}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_enum_non_member_unsat() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // Build set {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // Assert 5 \in {1, 2, 3} (should be UNSAT)
        let five = trans.solver_mut().int_const(5);
        let member = enc.encode_membership(&mut trans, five, set).unwrap();
        trans.assert(member);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_union() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2, e3]).unwrap();

        // Universe = {1, 2, 3}
        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let union_set = enc
            .encode_union(&mut trans, set_s, set_t, &universe)
            .unwrap();

        // Assert 1 \in union (should be SAT, since 1 \in S)
        let one = trans.solver_mut().int_const(1);
        let in_union = enc.encode_membership(&mut trans, one, union_set).unwrap();
        trans.assert(in_union);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_intersect() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let inter_set = enc
            .encode_intersect(&mut trans, set_s, set_t, &universe)
            .unwrap();

        // Assert 1 \in intersect (should be UNSAT, since 1 \notin T)
        let one = trans.solver_mut().int_const(1);
        let in_inter = enc.encode_membership(&mut trans, one, inter_set).unwrap();
        trans.assert(in_inter);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_intersect_member() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {2, 3}, intersection should contain 2
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let inter_set = enc
            .encode_intersect(&mut trans, set_s, set_t, &universe)
            .unwrap();

        // Assert 2 \in intersect (should be SAT)
        let two = trans.solver_mut().int_const(2);
        let in_inter = enc.encode_membership(&mut trans, two, inter_set).unwrap();
        trans.assert(in_inter);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_minus() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2, 3}, T = {2}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let diff = enc
            .encode_set_minus(&mut trans, set_s, set_t, &universe)
            .unwrap();

        // 2 should NOT be in S \ T
        let two = trans.solver_mut().int_const(2);
        let in_diff = enc.encode_membership(&mut trans, two, diff).unwrap();
        trans.assert(in_diff);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_minus_retains_member() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2, 3}, T = {2}, S \ T should contain 1
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let diff = enc
            .encode_set_minus(&mut trans, set_s, set_t, &universe)
            .unwrap();

        // 1 should be in S \ T
        let one = trans.solver_mut().int_const(1);
        let in_diff = enc.encode_membership(&mut trans, one, diff).unwrap();
        trans.assert(in_diff);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subseteq_true() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {1, 2, 3}: S \subseteq T should be true
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let subset = enc
            .encode_subseteq(&mut trans, set_s, set_t, &universe)
            .unwrap();
        trans.assert(subset);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subseteq_false() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2, 3}, T = {1, 2}: S \subseteq T should be false
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2, e3]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let subset = enc
            .encode_subseteq(&mut trans, set_s, set_t, &universe)
            .unwrap();
        // Assert subset is true
        trans.assert(subset);

        // This should be UNSAT because {1,2,3} is NOT a subset of {1,2}
        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_equality() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {1, 2}: S = T should be true
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let eq = enc
            .encode_set_eq(&mut trans, set_s, set_t, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_equality_different_sets() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {1, 3}: S = T should be false
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e1, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let eq = enc
            .encode_set_eq(&mut trans, set_s, set_t, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cardinality_empty_set() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        let empty = enc.empty_set(&mut trans).unwrap();
        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let card = enc
            .encode_cardinality(&mut trans, empty, &universe)
            .unwrap();

        // Assert cardinality = 0
        let zero = trans.solver_mut().int_const(0);
        let eq = trans.solver_mut().try_eq(card, zero).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cardinality_nonempty_set() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 3} over universe {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e3 = trans.solver_mut().int_const(3);
        let set = enc.encode_set_enum(&mut trans, &[e1, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let card = enc.encode_cardinality(&mut trans, set, &universe).unwrap();

        // Assert cardinality = 2
        let two = trans.solver_mut().int_const(2);
        let eq = trans.solver_mut().try_eq(card, two).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cardinality_wrong_count_unsat() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 3} over universe {1, 2, 3}: cardinality is 2, not 3
        let e1 = trans.solver_mut().int_const(1);
        let e3 = trans.solver_mut().int_const(3);
        let set = enc.encode_set_enum(&mut trans, &[e1, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let card = enc.encode_cardinality(&mut trans, set, &universe).unwrap();

        // Assert cardinality = 3 (should be UNSAT)
        let three = trans.solver_mut().int_const(3);
        let eq = trans.solver_mut().try_eq(card, three).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_union_cardinality() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {1, 2}, T = {2, 3}: S \cup T = {1, 2, 3}, cardinality = 3
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let set_s = enc.encode_set_enum(&mut trans, &[e1, e2]).unwrap();
        let set_t = enc.encode_set_enum(&mut trans, &[e2, e3]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let union_set = enc
            .encode_union(&mut trans, set_s, set_t, &universe)
            .unwrap();
        let card = enc
            .encode_cardinality(&mut trans, union_set, &universe)
            .unwrap();

        // Assert cardinality = 3
        let three = trans.solver_mut().int_const(3);
        let eq = trans.solver_mut().try_eq(card, three).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_set_variable() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // Declare a symbolic set variable S
        let set_sort = enc.set_sort();
        let set_s = trans.solver_mut().declare_const("S", set_sort);

        // Assert: 1 \in S /\ 2 \in S /\ NOT(3 \in S)
        let one = trans.solver_mut().int_const(1);
        let two = trans.solver_mut().int_const(2);
        let three = trans.solver_mut().int_const(3);

        let in1 = enc.encode_membership(&mut trans, one, set_s).unwrap();
        let in2 = enc.encode_membership(&mut trans, two, set_s).unwrap();
        let in3 = enc.encode_membership(&mut trans, three, set_s).unwrap();
        let not_in3 = trans.solver_mut().try_not(in3).unwrap();

        trans.assert(in1);
        trans.assert(in2);
        trans.assert(not_in3);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_singleton_set() {
        let mut trans = array_translator();
        let enc = FiniteSetEncoder::new();

        // S = {42}
        let e42 = trans.solver_mut().int_const(42);
        let set = enc.encode_set_enum(&mut trans, &[e42]).unwrap();

        // x \in S constrains x to 42
        let x = trans.solver_mut().declare_const("x", Sort::Int);
        let member = enc.encode_membership(&mut trans, x, set).unwrap();
        trans.assert(member);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
        let model = trans.get_model().unwrap();
        let x_val = model.int_val("x").unwrap();
        let x_i64: i64 = x_val.try_into().unwrap();
        assert_eq!(x_i64, 42);
    }
}
