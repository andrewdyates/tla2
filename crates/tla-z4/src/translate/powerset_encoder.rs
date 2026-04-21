// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Powerset, generalized union, and cardinality encoding for TLA+ set operations.
//!
//! Extends the [`FiniteSetEncoder`] with higher-order set operations needed for
//! Apalache parity:
//!
//! | TLA+ Operation     | SMT Encoding                                                    |
//! |--------------------|-----------------------------------------------------------------|
//! | `SUBSET S`         | fresh set `sub` with `\A x : sub(x) => S(x)` (subset constraint)|
//! | `UNION S`          | for S = {T1, ..., Tk}: `result(x) = T1(x) \/ ... \/ Tk(x)`     |
//! | `Cardinality(S)`   | sum of `ite(S[d], 1, 0)` over bounded domain                    |
//!
//! # Powerset Encoding
//!
//! For a bounded base set S = {s1, ..., sn}, `SUBSET S` produces a *symbolic* subset
//! variable constrained to be a subset of S. This is used in quantification contexts:
//! `\E T \in SUBSET S : P(T)` becomes a fresh set variable `T` with the subset constraint
//! plus assertion P(T).
//!
//! For finite enumeration of SUBSET S (e.g., `x \in SUBSET {1, 2}`), we expand to
//! all 2^n subsets. This is only viable for small n (bounded by `MAX_POWERSET_SIZE`).
//!
//! # Generalized Union
//!
//! `UNION {T1, T2, T3}` produces a set whose membership is the pointwise OR of
//! all component sets over the universe.
//!
//! # Cardinality
//!
//! `Cardinality(S)` for a set over finite universe {d1, ..., dn} is encoded as
//! `ite(S[d1], 1, 0) + ite(S[d2], 1, 0) + ...`. This is delegated to
//! [`FiniteSetEncoder::encode_cardinality`].
//!
//! Part of Gap 1 Phase 6 from designs/2026-03-26-apalache-parity.md

use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::finite_set::FiniteSetEncoder;
use super::Z4Translator;

/// Maximum number of elements in a base set for powerset expansion.
///
/// SUBSET S generates 2^n subsets. For n > 16 this produces > 65K subsets,
/// which is impractical for SMT encoding. Beyond this limit, only symbolic
/// subset constraints are supported (not full enumeration).
pub const MAX_POWERSET_SIZE: usize = 16;

/// Encoder for powerset, generalized union, and cardinality operations.
///
/// Works in conjunction with [`FiniteSetEncoder`] for the underlying set-as-array
/// representation. The powerset encoder adds higher-order set operations on top.
#[derive(Debug, Clone)]
pub struct PowersetEncoder {
    /// The underlying finite set encoder for basic operations.
    set_encoder: FiniteSetEncoder,
}

impl Default for PowersetEncoder {
    fn default() -> Self {
        Self::new()
    }
}

impl PowersetEncoder {
    /// Create a new powerset encoder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            set_encoder: FiniteSetEncoder::new(),
        }
    }

    /// Access the underlying finite set encoder.
    #[must_use]
    pub fn set_encoder(&self) -> &FiniteSetEncoder {
        &self.set_encoder
    }

    /// Encode a symbolic subset constraint: `sub \subseteq S`.
    ///
    /// Creates a fresh set variable `sub` and asserts that for every element
    /// in the universe, membership in `sub` implies membership in `S`:
    ///
    /// ```text
    /// \A x \in universe : (select sub x) => (select S x)
    /// ```
    ///
    /// This is the building block for `\E T \in SUBSET S : P(T)` — the solver
    /// finds a satisfying assignment for `sub` that is a subset of `S` and
    /// satisfies P.
    ///
    /// Returns the fresh set variable term.
    pub fn encode_symbolic_subset(
        &self,
        trans: &mut Z4Translator,
        base_set: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        let name = trans.fresh_name("subset");
        let sub = trans
            .solver_mut()
            .declare_const(&name, self.set_encoder.set_sort());

        // Assert: \A u \in universe : sub(u) => base_set(u)
        for &u in universe {
            let in_sub = trans.solver_mut().try_select(sub, u)?;
            let in_base = trans.solver_mut().try_select(base_set, u)?;
            let implication = trans.solver_mut().try_implies(in_sub, in_base)?;
            trans.assert(implication);
        }

        // Assert: sub contains no elements outside the universe.
        // For elements not in universe, sub must be false.
        // This is implicitly handled by the array theory — elements not
        // constrained are unconstrained, but the subset constraint above
        // ensures only universe elements can be true (since base_set
        // should only be true for universe elements).

        Ok(sub)
    }

    /// Encode membership in a powerset: `x \in SUBSET S`.
    ///
    /// For a bounded base set S with known universe elements, this asserts
    /// that `x` is a subset of `S` (i.e., `x \subseteq S`).
    ///
    /// The set variable `x` must already be declared as an `(Array Int Bool)`.
    /// Returns a Bool term representing `x \subseteq S`.
    pub fn encode_powerset_membership(
        &self,
        trans: &mut Z4Translator,
        member_set: Term,
        base_set: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        // x \in SUBSET S <==> x \subseteq S
        self.set_encoder
            .encode_subseteq(trans, member_set, base_set, universe)
    }

    /// Encode generalized union: `UNION {T1, T2, ..., Tk}`.
    ///
    /// For a set-of-sets where each component set is known, the result set
    /// has membership defined pointwise:
    ///
    /// ```text
    /// result(x) = T1(x) \/ T2(x) \/ ... \/ Tk(x)
    /// ```
    ///
    /// Returns the result set term and asserts pointwise constraints.
    pub fn encode_generalized_union(
        &self,
        trans: &mut Z4Translator,
        component_sets: &[Term],
        universe: &[Term],
    ) -> Z4Result<Term> {
        if component_sets.is_empty() {
            // UNION {} = {}
            return self.set_encoder.empty_set(trans);
        }

        if component_sets.len() == 1 {
            // UNION {S} = S
            return Ok(component_sets[0]);
        }

        let result_name = trans.fresh_name("gunion");
        let result = trans
            .solver_mut()
            .declare_const(&result_name, self.set_encoder.set_sort());

        for &u in universe {
            // Build: T1(u) \/ T2(u) \/ ... \/ Tk(u)
            let mut disjunction = trans.solver_mut().try_select(component_sets[0], u)?;
            for &set in &component_sets[1..] {
                let in_set = trans.solver_mut().try_select(set, u)?;
                disjunction = trans.solver_mut().try_or(disjunction, in_set)?;
            }

            // Assert: result(u) <=> disjunction
            let in_result = trans.solver_mut().try_select(result, u)?;
            let eq = trans.solver_mut().try_eq(in_result, disjunction)?;
            trans.assert(eq);
        }

        Ok(result)
    }

    /// Encode cardinality of a finite set.
    ///
    /// Delegates to [`FiniteSetEncoder::encode_cardinality`].
    /// Returns an Int-sorted term.
    pub fn encode_cardinality(
        &self,
        trans: &mut Z4Translator,
        set: Term,
        universe: &[Term],
    ) -> Z4Result<Term> {
        self.set_encoder.encode_cardinality(trans, set, universe)
    }

    /// Enumerate all subsets of a finite set for powerset expansion.
    ///
    /// Given universe elements `[e1, ..., en]`, generates all 2^n subsets
    /// as array terms. Each subset is a specific combination of elements.
    ///
    /// Returns an error if `n > MAX_POWERSET_SIZE`.
    pub fn enumerate_powerset(
        &self,
        trans: &mut Z4Translator,
        universe_elements: &[Term],
    ) -> Z4Result<Vec<Term>> {
        let n = universe_elements.len();
        if n > MAX_POWERSET_SIZE {
            return Err(Z4Error::UnsupportedOp(format!(
                "SUBSET of set with {n} elements exceeds maximum ({MAX_POWERSET_SIZE}); \
                 would generate 2^{n} = {} subsets",
                1u64.checked_shl(n as u32).unwrap_or(u64::MAX)
            )));
        }

        let num_subsets = 1usize << n;
        let mut subsets = Vec::with_capacity(num_subsets);

        for mask in 0..num_subsets {
            // Build the subset for this bitmask
            let mut elements = Vec::new();
            for (i, &elem) in universe_elements.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    elements.push(elem);
                }
            }
            let subset_term = self.set_encoder.encode_set_enum(trans, &elements)?;
            subsets.push(subset_term);
        }

        Ok(subsets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z4_dpll::api::SolveResult;

    fn array_translator() -> Z4Translator {
        Z4Translator::new_with_arrays()
    }

    // === Symbolic Subset Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_subset_is_sat() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Base set S = {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        // Create symbolic subset
        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Assert that 1 is in the subset (to constrain it)
        let one = trans.solver_mut().int_const(1);
        let in_sub = trans.solver_mut().try_select(sub, one).unwrap();
        trans.assert(in_sub);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_subset_excludes_non_base_elements() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Base set S = {1, 2}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Assert that 3 is in the subset (should be UNSAT since 3 not in base)
        let three = trans.solver_mut().int_const(3);
        let in_sub = trans.solver_mut().try_select(sub, three).unwrap();
        trans.assert(in_sub);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_subset_empty_is_valid() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Base set S = {1, 2}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Assert that neither 1 nor 2 is in the subset (empty subset should be valid)
        let one = trans.solver_mut().int_const(1);
        let two = trans.solver_mut().int_const(2);
        let in_sub_1 = trans.solver_mut().try_select(sub, one).unwrap();
        let in_sub_2 = trans.solver_mut().try_select(sub, two).unwrap();
        let not_1 = trans.solver_mut().try_not(in_sub_1).unwrap();
        let not_2 = trans.solver_mut().try_not(in_sub_2).unwrap();
        trans.assert(not_1);
        trans.assert(not_2);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // === Powerset Membership Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_powerset_membership_subset_accepted() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Base = {1, 2, 3}, candidate = {1, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2, e3])
            .unwrap();
        let candidate = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let is_member = enc
            .encode_powerset_membership(&mut trans, candidate, base, &universe)
            .unwrap();
        trans.assert(is_member);

        // {1, 3} \in SUBSET {1, 2, 3} should be SAT
        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_powerset_membership_non_subset_rejected() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Base = {1, 2}, candidate = {1, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();
        let candidate = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let is_member = enc
            .encode_powerset_membership(&mut trans, candidate, base, &universe)
            .unwrap();
        trans.assert(is_member);

        // {1, 3} \in SUBSET {1, 2} should be UNSAT (3 not in base)
        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // === Generalized Union Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_generalized_union_basic() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // T1 = {1, 2}, T2 = {3, 4}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let e4 = trans.solver_mut().int_const(4);
        let t1 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();
        let t2 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e3, e4])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let u4 = trans.solver_mut().int_const(4);
        let universe = [u1, u2, u3, u4];

        let result = enc
            .encode_generalized_union(&mut trans, &[t1, t2], &universe)
            .unwrap();

        // All 4 elements should be in the result
        for val in [1, 2, 3, 4] {
            let elem = trans.solver_mut().int_const(val);
            let in_result = trans.solver_mut().try_select(result, elem).unwrap();
            trans.assert(in_result);
        }
        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_generalized_union_excludes_non_members() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // T1 = {1}, T2 = {2}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let t1 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1])
            .unwrap();
        let t2 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e2])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let result = enc
            .encode_generalized_union(&mut trans, &[t1, t2], &universe)
            .unwrap();

        // 3 should NOT be in UNION {{1}, {2}}
        let three = trans.solver_mut().int_const(3);
        let in_result = trans.solver_mut().try_select(result, three).unwrap();
        trans.assert(in_result);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_generalized_union_overlapping_sets() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // T1 = {1, 2}, T2 = {2, 3}: UNION = {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let t1 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();
        let t2 = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e2, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let result = enc
            .encode_generalized_union(&mut trans, &[t1, t2], &universe)
            .unwrap();

        // Cardinality of UNION should be 3
        let card = enc
            .encode_cardinality(&mut trans, result, &universe)
            .unwrap();
        let three = trans.solver_mut().int_const(3);
        let eq = trans.solver_mut().try_eq(card, three).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_generalized_union_empty() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // UNION {} = {}
        let result = enc.encode_generalized_union(&mut trans, &[], &[]).unwrap();

        // Any element should not be in the result
        let one = trans.solver_mut().int_const(1);
        let in_result = trans.solver_mut().try_select(result, one).unwrap();
        trans.assert(in_result);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_generalized_union_singleton() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // UNION {S} = S
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let s = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();

        let result = enc.encode_generalized_union(&mut trans, &[s], &[]).unwrap();

        // Should be the same term as s
        let one = trans.solver_mut().int_const(1);
        let in_result = trans.solver_mut().try_select(result, one).unwrap();
        trans.assert(in_result);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // === Cardinality Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cardinality_of_subset() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // S = {1, 2, 3}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        // Create symbolic subset of S
        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Assert cardinality = 2
        let card = enc.encode_cardinality(&mut trans, sub, &universe).unwrap();
        let two = trans.solver_mut().int_const(2);
        let eq = trans.solver_mut().try_eq(card, two).unwrap();
        trans.assert(eq);

        // Should be SAT (many 2-element subsets of {1,2,3})
        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cardinality_of_subset_too_large_unsat() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // S = {1, 2}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Assert cardinality = 3 (impossible: subset of 2-element set can't have 3)
        let card = enc.encode_cardinality(&mut trans, sub, &universe).unwrap();
        let three = trans.solver_mut().int_const(3);
        let eq = trans.solver_mut().try_eq(card, three).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // === Powerset Enumeration Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_enumerate_powerset_empty() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // SUBSET {} = {{}}
        let subsets = enc.enumerate_powerset(&mut trans, &[]).unwrap();
        assert_eq!(subsets.len(), 1); // Just the empty set
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_enumerate_powerset_two_elements() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // SUBSET {1, 2} = {{}, {1}, {2}, {1,2}}
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);

        let subsets = enc.enumerate_powerset(&mut trans, &[e1, e2]).unwrap();
        assert_eq!(subsets.len(), 4);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_enumerate_powerset_three_elements() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);

        let subsets = enc.enumerate_powerset(&mut trans, &[e1, e2, e3]).unwrap();
        assert_eq!(subsets.len(), 8); // 2^3
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_enumerate_powerset_membership_correct() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // SUBSET {10, 20}: verify {10} is one of the subsets
        let e10 = trans.solver_mut().int_const(10);
        let e20 = trans.solver_mut().int_const(20);

        let subsets = enc.enumerate_powerset(&mut trans, &[e10, e20]).unwrap();
        // subsets[0] = {}, [1] = {10}, [2] = {20}, [3] = {10, 20}

        // Check that subset[1] contains 10 but not 20
        let ten = trans.solver_mut().int_const(10);
        let twenty = trans.solver_mut().int_const(20);
        let in_10 = trans.solver_mut().try_select(subsets[1], ten).unwrap();
        let in_20 = trans.solver_mut().try_select(subsets[1], twenty).unwrap();
        let not_in_20 = trans.solver_mut().try_not(in_20).unwrap();
        trans.assert(in_10);
        trans.assert(not_in_20);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_enumerate_powerset_too_large() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // 17 elements exceeds MAX_POWERSET_SIZE
        let elems: Vec<Term> = (0..17).map(|i| trans.solver_mut().int_const(i)).collect();

        let result = enc.enumerate_powerset(&mut trans, &elems);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("exceeds maximum"));
    }

    // === Combined Tests ===

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subset_with_cardinality_constraint() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Find a subset of {1, 2, 3, 4} with exactly 2 elements that contains 1
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let e4 = trans.solver_mut().int_const(4);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2, e3, e4])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let u4 = trans.solver_mut().int_const(4);
        let universe = [u1, u2, u3, u4];

        let sub = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // Cardinality = 2
        let card = enc.encode_cardinality(&mut trans, sub, &universe).unwrap();
        let two = trans.solver_mut().int_const(2);
        let eq = trans.solver_mut().try_eq(card, two).unwrap();
        trans.assert(eq);

        // Must contain 1
        let one = trans.solver_mut().int_const(1);
        let contains_1 = trans.solver_mut().try_select(sub, one).unwrap();
        trans.assert(contains_1);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_union_of_subsets_covers_base() {
        let mut trans = array_translator();
        let enc = PowersetEncoder::new();

        // Two subsets of {1, 2, 3} whose union is the whole set
        // (without cardinality constraints - just covering)
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let base = enc
            .set_encoder()
            .encode_set_enum(&mut trans, &[e1, e2, e3])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let u3 = trans.solver_mut().int_const(3);
        let universe = [u1, u2, u3];

        let sub1 = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();
        let sub2 = enc
            .encode_symbolic_subset(&mut trans, base, &universe)
            .unwrap();

        // UNION {sub1, sub2}
        let union_set = enc
            .encode_generalized_union(&mut trans, &[sub1, sub2], &universe)
            .unwrap();

        // Assert union = base (all elements present)
        let set_eq = enc
            .set_encoder()
            .encode_set_eq(&mut trans, union_set, base, &universe)
            .unwrap();
        trans.assert(set_eq);

        // Should be SAT: e.g., sub1={1,2,3}, sub2={1,2,3} trivially covers
        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }
}
