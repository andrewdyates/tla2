// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function encoding as SMT arrays for TLA+ function operations.
//!
//! Encodes TLA+ functions as a pair: an SMT array `(Array DomSort RanSort)`
//! for the mapping, plus an SMT set `(Array DomSort Bool)` for the domain.
//! TLA+ functions are total over their domain.
//!
//! # Encoding
//!
//! | TLA+ Operation            | SMT Encoding                                          |
//! |---------------------------|-------------------------------------------------------|
//! | `[x \in S \|-> e]`        | domain = S (as set), mapping = constrained array      |
//! | `f[x]`                    | `(select mapping x)`                                  |
//! | `DOMAIN f`                | the domain set term                                   |
//! | `[f EXCEPT ![a] = b]`     | `(store mapping a b)`, same domain                    |
//! | `[S -> T]`                | constrain domain = S, range elements in T             |
//! | `f = g`                   | same domain AND `\A x \in dom : f[x] = g[x]`         |
//!
//! Unlike the per-variable expansion in `membership/`, this encoder uses
//! first-class SMT arrays for the mapping. This is more compositional:
//! intermediate function values (from EXCEPT, etc.) are first-class SMT
//! terms without requiring fresh variable declarations for each key.
//!
//! # Usage
//!
//! ```no_run
//! use tla_z4::translate::function_encoder::FunctionEncoder;
//! use tla_z4::Z4Translator;
//!
//! let mut trans = Z4Translator::new_with_arrays();
//! let enc = FunctionEncoder::new(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);
//! // ... use enc methods to build function terms
//! ```
//!
//! Part of #3749

use z4_dpll::api::{Sort, Term};

use crate::error::{Z4Error, Z4Result};
use crate::translate::finite_set::FiniteSetEncoder;

use super::Z4Translator;

/// A symbolic TLA+ function represented as an SMT domain set + mapping array.
///
/// This is returned by encoder methods so callers can thread both
/// the domain and mapping terms through further operations.
#[derive(Debug, Clone, Copy)]
pub struct FuncTerm {
    /// SMT set `(Array DomSort Bool)` representing the domain.
    pub domain: Term,
    /// SMT array `(Array DomSort RanSort)` holding the function mapping.
    pub mapping: Term,
}

/// Encoder for TLA+ functions as SMT arrays.
///
/// Provides methods to build and manipulate function terms
/// within a [`Z4Translator`] context.
///
/// Functions are represented as two arrays:
/// - **Domain:** `(Array DomSort Bool)` — set membership predicate.
/// - **Mapping:** `(Array DomSort RanSort)` — the function's value map.
///
/// The domain sort is typically `Int` (integers or interned values).
/// The range sort is configurable (typically `Int` or `Bool`).
#[derive(Debug, Clone)]
pub struct FunctionEncoder {
    /// The domain sort (index type for both domain set and mapping array).
    domain_sort: Sort,
    /// The range sort (value type for the mapping array).
    range_sort: Sort,
}

impl FunctionEncoder {
    /// Create a new function encoder for the given domain and range sorts.
    ///
    /// Common combinations:
    /// - `(Sort::Int, Sort::Int)` — integer-to-integer functions
    /// - `(Sort::Int, Sort::Bool)` — integer-to-boolean functions (predicates)
    #[must_use]
    pub fn new(domain_sort: Sort, range_sort: Sort) -> Self {
        Self {
            domain_sort,
            range_sort,
        }
    }

    /// Get the SMT sort for the domain set: `(Array DomSort Bool)`.
    #[must_use]
    pub fn domain_set_sort(&self) -> Sort {
        Sort::array(self.domain_sort.clone(), Sort::Bool)
    }

    /// Get the SMT sort for the mapping array: `(Array DomSort RanSort)`.
    #[must_use]
    pub fn mapping_sort(&self) -> Sort {
        Sort::array(self.domain_sort.clone(), self.range_sort.clone())
    }

    /// Get the domain sort.
    #[must_use]
    pub fn domain_sort(&self) -> &Sort {
        &self.domain_sort
    }

    /// Get the range sort.
    #[must_use]
    pub fn range_sort(&self) -> &Sort {
        &self.range_sort
    }

    // =========================================================================
    // Construction
    // =========================================================================

    /// Encode a function definition `[x \in S |-> e(x)]` given concrete
    /// domain elements and their corresponding range values.
    ///
    /// `domain_elements` are the concrete domain values (Int terms).
    /// `range_values` are the corresponding range values, one per domain element.
    ///
    /// Builds:
    /// - Domain set via `FiniteSetEncoder::encode_set_enum`
    /// - Mapping array via successive `store` operations
    ///
    /// # Errors
    ///
    /// Returns `Z4Error::UnsupportedOp` if `domain_elements` and `range_values`
    /// have different lengths.
    pub fn encode_func_def(
        &self,
        trans: &mut Z4Translator,
        domain_elements: &[Term],
        range_values: &[Term],
    ) -> Z4Result<FuncTerm> {
        if domain_elements.len() != range_values.len() {
            return Err(Z4Error::UnsupportedOp(format!(
                "function definition: {} domain elements but {} range values",
                domain_elements.len(),
                range_values.len()
            )));
        }

        // Build domain set using FiniteSetEncoder
        let set_enc = FiniteSetEncoder::new();
        let domain = set_enc.encode_set_enum(trans, domain_elements)?;

        // Build mapping array: start with a fresh array, then store each pair
        let mut mapping = self.declare_fresh_mapping(trans, "func_def")?;
        for (&dom_elem, &ran_val) in domain_elements.iter().zip(range_values.iter()) {
            mapping = trans.solver_mut().try_store(mapping, dom_elem, ran_val)?;
        }

        Ok(FuncTerm { domain, mapping })
    }

    /// Encode function application `f[x]` as `(select mapping x)`.
    ///
    /// Returns a term of the range sort. TLA+ requires `x \in DOMAIN f`
    /// for application to be defined; this method does NOT assert that guard.
    pub fn encode_func_apply(
        &self,
        trans: &mut Z4Translator,
        func: &FuncTerm,
        argument: Term,
    ) -> Z4Result<Term> {
        Ok(trans.solver_mut().try_select(func.mapping, argument)?)
    }

    /// Encode `DOMAIN f` — returns the domain set term.
    ///
    /// The returned term is an `(Array DomSort Bool)` that can be used
    /// with `FiniteSetEncoder` methods for set operations on the domain.
    #[must_use]
    pub fn encode_domain(&self, func: &FuncTerm) -> Term {
        func.domain
    }

    /// Encode `[f EXCEPT ![a] = b]` — create a new function with one updated mapping.
    ///
    /// The domain is unchanged; the mapping is updated via `(store mapping a b)`.
    /// This matches TLA+ semantics: EXCEPT produces a new function with the
    /// same domain and all values identical except at the specified argument.
    pub fn encode_except(
        &self,
        trans: &mut Z4Translator,
        func: &FuncTerm,
        argument: Term,
        new_value: Term,
    ) -> Z4Result<FuncTerm> {
        let new_mapping = trans
            .solver_mut()
            .try_store(func.mapping, argument, new_value)?;

        Ok(FuncTerm {
            domain: func.domain,
            mapping: new_mapping,
        })
    }

    /// Encode the function set `[S -> T]` for bounded finite domains.
    ///
    /// Given a domain set term `domain_set` and a known finite universe of
    /// domain elements, declares a fresh symbolic function and constrains:
    /// 1. The function's domain equals `domain_set`
    /// 2. For each `x` in `universe` where `x \in domain_set`,
    ///    the function's value `f(x)` satisfies the range constraint.
    ///
    /// `range_constraint` is a closure that, given a range-sorted term,
    /// produces a Bool constraint (e.g., `0 <= v <= 10` for `v \in 0..10`).
    ///
    /// Returns the symbolic function term.
    pub fn encode_func_set(
        &self,
        trans: &mut Z4Translator,
        domain_set: Term,
        universe: &[Term],
        range_constraint: impl Fn(&mut Z4Translator, Term) -> Z4Result<Term>,
    ) -> Z4Result<FuncTerm> {
        let mapping = self.declare_fresh_mapping(trans, "func_set")?;

        // Constrain: for each u in universe, if u \in domain_set, then f(u) \in range
        let set_enc = FiniteSetEncoder::new();
        for &u in universe {
            let in_domain = set_enc.encode_membership(trans, u, domain_set)?;
            let value = trans.solver_mut().try_select(mapping, u)?;
            let in_range = range_constraint(trans, value)?;
            let guarded = trans.solver_mut().try_implies(in_domain, in_range)?;
            trans.assert(guarded);
        }

        Ok(FuncTerm {
            domain: domain_set,
            mapping,
        })
    }

    /// Encode function equality `f = g` over a known finite universe.
    ///
    /// Two TLA+ functions are equal iff they have the same domain AND
    /// the same values at every domain element:
    ///
    /// ```text
    /// (DOMAIN f = DOMAIN g) /\ \A x \in DOMAIN f : f[x] = g[x]
    /// ```
    ///
    /// For finite universes, this is expanded pointwise.
    ///
    /// Returns a Bool-sorted term.
    pub fn encode_func_eq(
        &self,
        trans: &mut Z4Translator,
        func_f: &FuncTerm,
        func_g: &FuncTerm,
        universe: &[Term],
    ) -> Z4Result<Term> {
        // Domain equality: pointwise over universe
        let set_enc = FiniteSetEncoder::new();
        let domain_eq = set_enc.encode_set_eq(trans, func_f.domain, func_g.domain, universe)?;

        if universe.is_empty() {
            return Ok(domain_eq);
        }

        // Value equality: for each u in universe,
        //   (u \in DOMAIN f) => f[u] = g[u]
        let mut conjuncts = Vec::with_capacity(universe.len() + 1);
        conjuncts.push(domain_eq);

        for &u in universe {
            let in_dom = set_enc.encode_membership(trans, u, func_f.domain)?;
            let f_val = trans.solver_mut().try_select(func_f.mapping, u)?;
            let g_val = trans.solver_mut().try_select(func_g.mapping, u)?;
            let vals_eq = trans.solver_mut().try_eq(f_val, g_val)?;
            let guarded = trans.solver_mut().try_implies(in_dom, vals_eq)?;
            conjuncts.push(guarded);
        }

        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = trans.solver_mut().try_and(result, c)?;
        }
        Ok(result)
    }

    // =========================================================================
    // Multi-EXCEPT
    // =========================================================================

    /// Encode `[f EXCEPT ![a1] = b1, ![a2] = b2, ...]` — multiple updates.
    ///
    /// Applies successive `store` operations. TLA+ evaluates EXCEPT
    /// left to right, so later entries override earlier ones for the
    /// same key.
    pub fn encode_except_multi(
        &self,
        trans: &mut Z4Translator,
        func: &FuncTerm,
        updates: &[(Term, Term)],
    ) -> Z4Result<FuncTerm> {
        let mut current = *func;
        for &(arg, val) in updates {
            current = self.encode_except(trans, &current, arg, val)?;
        }
        Ok(current)
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /// Declare a fresh mapping array `(Array DomSort RanSort)` with a unique name.
    fn declare_fresh_mapping(&self, trans: &mut Z4Translator, prefix: &str) -> Z4Result<Term> {
        let name = trans.fresh_name(prefix);
        Ok(trans.solver_mut().declare_const(&name, self.mapping_sort()))
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

    // =========================================================================
    // Function definition tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_def_basic() {
        // [x \in {1, 2, 3} |-> x * 10]
        // f[1] = 10, f[2] = 20, f[3] = 30
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let d3 = trans.solver_mut().int_const(3);
        let r1 = trans.solver_mut().int_const(10);
        let r2 = trans.solver_mut().int_const(20);
        let r3 = trans.solver_mut().int_const(30);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2, d3], &[r1, r2, r3])
            .unwrap();

        // Assert f[2] = 20
        let arg = trans.solver_mut().int_const(2);
        let result = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
        let expected = trans.solver_mut().int_const(20);
        let eq = trans.solver_mut().try_eq(result, expected).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_def_wrong_value_unsat() {
        // [x \in {1, 2} |-> x * 10], assert f[1] = 99
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r1 = trans.solver_mut().int_const(10);
        let r2 = trans.solver_mut().int_const(20);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r1, r2])
            .unwrap();

        // Assert f[1] = 99 (should be UNSAT, since f[1] = 10)
        let arg = trans.solver_mut().int_const(1);
        let result = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
        let wrong = trans.solver_mut().int_const(99);
        let eq = trans.solver_mut().try_eq(result, wrong).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_def_mismatched_lengths() {
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let r1 = trans.solver_mut().int_const(10);
        let r2 = trans.solver_mut().int_const(20);

        let result = enc.encode_func_def(&mut trans, &[d1], &[r1, r2]);
        assert!(result.is_err());
    }

    // =========================================================================
    // Function application tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_apply_all_elements() {
        // f = [x \in {1, 2, 3} |-> x + 100]
        // Verify f[1]=101, f[2]=102, f[3]=103 are all satisfiable simultaneously
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let d3 = trans.solver_mut().int_const(3);
        let r1 = trans.solver_mut().int_const(101);
        let r2 = trans.solver_mut().int_const(102);
        let r3 = trans.solver_mut().int_const(103);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2, d3], &[r1, r2, r3])
            .unwrap();

        // Assert all three values simultaneously
        for (dom_val, expected_val) in [(1, 101), (2, 102), (3, 103)] {
            let arg = trans.solver_mut().int_const(dom_val);
            let result = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
            let expected = trans.solver_mut().int_const(expected_val);
            let eq = trans.solver_mut().try_eq(result, expected).unwrap();
            trans.assert(eq);
        }

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_apply_bool_range() {
        // f = [x \in {1, 2} |-> x = 1] (Bool-valued function)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Bool);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r1 = trans.solver_mut().bool_const(true);
        let r2 = trans.solver_mut().bool_const(false);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r1, r2])
            .unwrap();

        // f[1] should be true
        let arg1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_func_apply(&mut trans, &func, arg1).unwrap();
        trans.assert(val1);

        // f[2] should be false
        let arg2 = trans.solver_mut().int_const(2);
        let val2 = enc.encode_func_apply(&mut trans, &func, arg2).unwrap();
        let not_val2 = trans.solver_mut().try_not(val2).unwrap();
        trans.assert(not_val2);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // DOMAIN tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_domain_membership() {
        // f = [x \in {1, 2, 3} |-> 0], check 2 \in DOMAIN f
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
        let set_enc = FiniteSetEncoder::new();

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let d3 = trans.solver_mut().int_const(3);
        let r0 = trans.solver_mut().int_const(0);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2, d3], &[r0, r0, r0])
            .unwrap();

        let dom = enc.encode_domain(&func);
        let two = trans.solver_mut().int_const(2);
        let in_dom = set_enc.encode_membership(&mut trans, two, dom).unwrap();
        trans.assert(in_dom);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_domain_non_membership_unsat() {
        // f = [x \in {1, 2} |-> 0], check 5 \in DOMAIN f (should be UNSAT)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
        let set_enc = FiniteSetEncoder::new();

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r0 = trans.solver_mut().int_const(0);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r0, r0])
            .unwrap();

        let dom = enc.encode_domain(&func);
        let five = trans.solver_mut().int_const(5);
        let in_dom = set_enc.encode_membership(&mut trans, five, dom).unwrap();
        trans.assert(in_dom);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // EXCEPT tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_single_update() {
        // f = [x \in {1, 2, 3} |-> 0]
        // g = [f EXCEPT ![2] = 99]
        // g[2] should be 99, g[1] and g[3] should still be 0
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let d3 = trans.solver_mut().int_const(3);
        let r0 = trans.solver_mut().int_const(0);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2, d3], &[r0, r0, r0])
            .unwrap();

        let update_arg = trans.solver_mut().int_const(2);
        let update_val = trans.solver_mut().int_const(99);
        let updated = enc
            .encode_except(&mut trans, &func, update_arg, update_val)
            .unwrap();

        // g[2] = 99
        let arg2 = trans.solver_mut().int_const(2);
        let val2 = enc.encode_func_apply(&mut trans, &updated, arg2).unwrap();
        let expected_99 = trans.solver_mut().int_const(99);
        let eq2 = trans.solver_mut().try_eq(val2, expected_99).unwrap();
        trans.assert(eq2);

        // g[1] = 0 (unchanged)
        let arg1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_func_apply(&mut trans, &updated, arg1).unwrap();
        let expected_0 = trans.solver_mut().int_const(0);
        let eq1 = trans.solver_mut().try_eq(val1, expected_0).unwrap();
        trans.assert(eq1);

        // g[3] = 0 (unchanged)
        let arg3 = trans.solver_mut().int_const(3);
        let val3 = enc.encode_func_apply(&mut trans, &updated, arg3).unwrap();
        let expected_0b = trans.solver_mut().int_const(0);
        let eq3 = trans.solver_mut().try_eq(val3, expected_0b).unwrap();
        trans.assert(eq3);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_preserves_domain() {
        // [f EXCEPT ![a] = b] has the same domain as f
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
        let set_enc = FiniteSetEncoder::new();

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r1 = trans.solver_mut().int_const(10);
        let r2 = trans.solver_mut().int_const(20);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r1, r2])
            .unwrap();

        let update_arg = trans.solver_mut().int_const(1);
        let update_val = trans.solver_mut().int_const(99);
        let updated = enc
            .encode_except(&mut trans, &func, update_arg, update_val)
            .unwrap();

        // DOMAIN of original and updated should be the same object
        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let dom_eq = set_enc
            .encode_set_eq(
                &mut trans,
                enc.encode_domain(&func),
                enc.encode_domain(&updated),
                &universe,
            )
            .unwrap();
        trans.assert(dom_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_old_value_unsat() {
        // f = [x \in {1} |-> 10], g = [f EXCEPT ![1] = 20]
        // Assert g[1] = 10 (should be UNSAT, since g[1] = 20)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let r1 = trans.solver_mut().int_const(10);

        let func = enc.encode_func_def(&mut trans, &[d1], &[r1]).unwrap();

        let update_arg = trans.solver_mut().int_const(1);
        let update_val = trans.solver_mut().int_const(20);
        let updated = enc
            .encode_except(&mut trans, &func, update_arg, update_val)
            .unwrap();

        // Assert g[1] = 10 (should be UNSAT)
        let arg = trans.solver_mut().int_const(1);
        let val = enc.encode_func_apply(&mut trans, &updated, arg).unwrap();
        let old_expected = trans.solver_mut().int_const(10);
        let eq = trans.solver_mut().try_eq(val, old_expected).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Multi-EXCEPT tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_multi() {
        // f = [x \in {1, 2, 3} |-> 0]
        // g = [f EXCEPT ![1] = 11, ![3] = 33]
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let d3 = trans.solver_mut().int_const(3);
        let r0 = trans.solver_mut().int_const(0);

        let func = enc
            .encode_func_def(&mut trans, &[d1, d2, d3], &[r0, r0, r0])
            .unwrap();

        let a1 = trans.solver_mut().int_const(1);
        let v1 = trans.solver_mut().int_const(11);
        let a3 = trans.solver_mut().int_const(3);
        let v3 = trans.solver_mut().int_const(33);

        let updated = enc
            .encode_except_multi(&mut trans, &func, &[(a1, v1), (a3, v3)])
            .unwrap();

        // g[1] = 11
        let arg1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_func_apply(&mut trans, &updated, arg1).unwrap();
        let exp1 = trans.solver_mut().int_const(11);
        let eq1 = trans.solver_mut().try_eq(val1, exp1).unwrap();
        trans.assert(eq1);

        // g[2] = 0 (unchanged)
        let arg2 = trans.solver_mut().int_const(2);
        let val2 = enc.encode_func_apply(&mut trans, &updated, arg2).unwrap();
        let exp2 = trans.solver_mut().int_const(0);
        let eq2 = trans.solver_mut().try_eq(val2, exp2).unwrap();
        trans.assert(eq2);

        // g[3] = 33
        let arg3 = trans.solver_mut().int_const(3);
        let val3 = enc.encode_func_apply(&mut trans, &updated, arg3).unwrap();
        let exp3 = trans.solver_mut().int_const(33);
        let eq3 = trans.solver_mut().try_eq(val3, exp3).unwrap();
        trans.assert(eq3);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_multi_last_wins() {
        // TLA+ EXCEPT evaluates left to right: later overrides earlier.
        // f = [x \in {1} |-> 0]
        // g = [f EXCEPT ![1] = 10, ![1] = 20]
        // g[1] should be 20
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let r0 = trans.solver_mut().int_const(0);

        let func = enc.encode_func_def(&mut trans, &[d1], &[r0]).unwrap();

        let a1a = trans.solver_mut().int_const(1);
        let v1a = trans.solver_mut().int_const(10);
        let a1b = trans.solver_mut().int_const(1);
        let v1b = trans.solver_mut().int_const(20);

        let updated = enc
            .encode_except_multi(&mut trans, &func, &[(a1a, v1a), (a1b, v1b)])
            .unwrap();

        // g[1] = 20 (last write wins)
        let arg = trans.solver_mut().int_const(1);
        let val = enc.encode_func_apply(&mut trans, &updated, arg).unwrap();
        let exp = trans.solver_mut().int_const(20);
        let eq = trans.solver_mut().try_eq(val, exp).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Function set tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_set_range_constraint() {
        // f \in [{1, 2} -> 0..10]
        // All values of f should be between 0 and 10
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
        let set_enc = FiniteSetEncoder::new();

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let domain_set = set_enc.encode_set_enum(&mut trans, &[d1, d2]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let func = enc
            .encode_func_set(&mut trans, domain_set, &universe, |tr, val| {
                let zero = tr.solver_mut().int_const(0);
                let ten = tr.solver_mut().int_const(10);
                let ge = tr.solver_mut().try_ge(val, zero)?;
                let le = tr.solver_mut().try_le(val, ten)?;
                Ok(tr.solver_mut().try_and(ge, le)?)
            })
            .unwrap();

        // f[1] should be between 0 and 10 (SAT)
        let arg = trans.solver_mut().int_const(1);
        let val = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
        let zero = trans.solver_mut().int_const(0);
        let ten = trans.solver_mut().int_const(10);
        let ge = trans.solver_mut().try_ge(val, zero).unwrap();
        let le = trans.solver_mut().try_le(val, ten).unwrap();
        let in_range = trans.solver_mut().try_and(ge, le).unwrap();
        trans.assert(in_range);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_set_violates_range_unsat() {
        // f \in [{1} -> 0..5], assert f[1] = 99 (should be UNSAT)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
        let set_enc = FiniteSetEncoder::new();

        let d1 = trans.solver_mut().int_const(1);
        let domain_set = set_enc.encode_set_enum(&mut trans, &[d1]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let universe = [u1];

        let func = enc
            .encode_func_set(&mut trans, domain_set, &universe, |tr, val| {
                let zero = tr.solver_mut().int_const(0);
                let five = tr.solver_mut().int_const(5);
                let ge = tr.solver_mut().try_ge(val, zero)?;
                let le = tr.solver_mut().try_le(val, five)?;
                Ok(tr.solver_mut().try_and(ge, le)?)
            })
            .unwrap();

        // Assert f[1] = 99 (out of range, should be UNSAT)
        let arg = trans.solver_mut().int_const(1);
        let val = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
        let ninety_nine = trans.solver_mut().int_const(99);
        let eq = trans.solver_mut().try_eq(val, ninety_nine).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Function equality tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_eq_same_function() {
        // f = g = [x \in {1, 2} |-> x * 10]
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r1 = trans.solver_mut().int_const(10);
        let r2 = trans.solver_mut().int_const(20);

        let func_f = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r1, r2])
            .unwrap();

        let d1b = trans.solver_mut().int_const(1);
        let d2b = trans.solver_mut().int_const(2);
        let r1b = trans.solver_mut().int_const(10);
        let r2b = trans.solver_mut().int_const(20);

        let func_g = enc
            .encode_func_def(&mut trans, &[d1b, d2b], &[r1b, r2b])
            .unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_g, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_eq_different_values_unsat() {
        // f = [x \in {1} |-> 10], g = [x \in {1} |-> 20]
        // f = g should be UNSAT
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let r1 = trans.solver_mut().int_const(10);
        let func_f = enc.encode_func_def(&mut trans, &[d1], &[r1]).unwrap();

        let d1b = trans.solver_mut().int_const(1);
        let r1b = trans.solver_mut().int_const(20);
        let func_g = enc.encode_func_def(&mut trans, &[d1b], &[r1b]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let universe = [u1];

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_g, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_eq_different_domains_unsat() {
        // f = [x \in {1, 2} |-> 0], g = [x \in {1} |-> 0]
        // f = g should be UNSAT (different domains)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r0 = trans.solver_mut().int_const(0);
        let func_f = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r0, r0])
            .unwrap();

        let d1b = trans.solver_mut().int_const(1);
        let r0b = trans.solver_mut().int_const(0);
        let func_g = enc.encode_func_def(&mut trans, &[d1b], &[r0b]).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_g, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Integration: EXCEPT + equality
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_makes_functions_unequal() {
        // f = [x \in {1, 2} |-> 0]
        // g = [f EXCEPT ![1] = 99]
        // f = g should be UNSAT
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r0 = trans.solver_mut().int_const(0);

        let func_f = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r0, r0])
            .unwrap();

        let arg = trans.solver_mut().int_const(1);
        let val = trans.solver_mut().int_const(99);
        let func_g = enc.encode_except(&mut trans, &func_f, arg, val).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_g, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_except_restore_makes_equal() {
        // f = [x \in {1, 2} |-> 0]
        // g = [f EXCEPT ![1] = 99]
        // h = [g EXCEPT ![1] = 0]
        // f = h should be SAT (both map everything to 0)
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let r0 = trans.solver_mut().int_const(0);

        let func_f = enc
            .encode_func_def(&mut trans, &[d1, d2], &[r0, r0])
            .unwrap();

        // g = [f EXCEPT ![1] = 99]
        let arg1 = trans.solver_mut().int_const(1);
        let val1 = trans.solver_mut().int_const(99);
        let func_g = enc.encode_except(&mut trans, &func_f, arg1, val1).unwrap();

        // h = [g EXCEPT ![1] = 0] (restore to original)
        let arg2 = trans.solver_mut().int_const(1);
        let val2 = trans.solver_mut().int_const(0);
        let func_h = enc.encode_except(&mut trans, &func_g, arg2, val2).unwrap();

        let u1 = trans.solver_mut().int_const(1);
        let u2 = trans.solver_mut().int_const(2);
        let universe = [u1, u2];

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_h, &universe)
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_singleton_domain_function() {
        // f = [x \in {42} |-> 7]
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let d42 = trans.solver_mut().int_const(42);
        let r7 = trans.solver_mut().int_const(7);

        let func = enc.encode_func_def(&mut trans, &[d42], &[r7]).unwrap();

        let arg = trans.solver_mut().int_const(42);
        let val = enc.encode_func_apply(&mut trans, &func, arg).unwrap();
        let expected = trans.solver_mut().int_const(7);
        let eq = trans.solver_mut().try_eq(val, expected).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_domain_function() {
        // f = [x \in {} |-> 0] — domain is empty
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let func = enc.encode_func_def(&mut trans, &[], &[]).unwrap();

        // DOMAIN f should be empty: 1 \notin DOMAIN f
        let set_enc = FiniteSetEncoder::new();
        let dom = enc.encode_domain(&func);
        let one = trans.solver_mut().int_const(1);
        let in_dom = set_enc.encode_membership(&mut trans, one, dom).unwrap();
        trans.assert(in_dom);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_eq_empty_universe() {
        // With empty universe, function equality is vacuously true
        let mut trans = array_translator();
        let enc = FunctionEncoder::new(Sort::Int, Sort::Int);

        let func_f = enc.encode_func_def(&mut trans, &[], &[]).unwrap();
        let func_g = enc.encode_func_def(&mut trans, &[], &[]).unwrap();

        let eq = enc
            .encode_func_eq(&mut trans, &func_f, &func_g, &[])
            .unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }
}
