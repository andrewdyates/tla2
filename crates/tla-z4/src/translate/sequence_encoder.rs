// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence encoding as SMT arrays for TLA+ sequence operations.
//!
//! Encodes TLA+ sequences as a pair: an SMT array `(Array Int ElemSort)` for
//! indexed element storage, plus an `Int` variable tracking the length.
//! TLA+ sequences are 1-indexed, so `(select arr 1)` is the first element.
//!
//! # Encoding
//!
//! | TLA+ Operation          | SMT Encoding                                              |
//! |-------------------------|-----------------------------------------------------------|
//! | `<<e1, ..., en>>`       | `len = n`, `(store ... (store arr 1 e1) ... n en)`        |
//! | `Len(s)`                | read the length variable                                  |
//! | `Head(s)`               | `(select arr 1)` with `len >= 1` guard                    |
//! | `Tail(s)`               | new array with shifted indices, `len' = len - 1`          |
//! | `Append(s, e)`          | `(store arr (len+1) e)`, `len' = len + 1`                 |
//! | `s \o t`                | merge arrays, `len' = len_s + len_t`                      |
//! | `SubSeq(s, m, n)`       | offset array, `len' = max(0, n - m + 1)`                  |
//! | `Seq(S)` (bounded)      | symbolic sequences up to max_len                          |
//!
//! The array-based encoding is more compositional than per-variable expansion:
//! intermediate sequence values (from Tail, Append, etc.) are first-class
//! SMT terms without requiring fresh variable declarations for each position.
//!
//! # Usage
//!
//! ```no_run
//! use tla_z4::translate::sequence_encoder::SequenceEncoder;
//! use tla_z4::Z4Translator;
//!
//! let mut trans = Z4Translator::new_with_arrays();
//! let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);
//! // ... use enc methods to build sequence terms
//! ```
//!
//! Part of #3793

use z4_dpll::api::{Sort, Term};

use crate::error::Z4Result;

use super::Z4Translator;

/// A symbolic sequence represented as an SMT array + length.
///
/// This is returned by encoder methods so callers can thread both
/// the array term and the length term through further operations.
#[derive(Debug, Clone, Copy)]
pub struct SeqTerm {
    /// SMT array `(Array Int ElemSort)` holding the indexed elements.
    pub array: Term,
    /// SMT `Int` term representing the current length.
    pub len: Term,
}

/// Encoder for TLA+ sequences as SMT arrays.
///
/// Provides methods to build and manipulate sequence terms
/// within a [`Z4Translator`] context.
///
/// Sequences are represented as `(Array Int ElemSort)` + `Int`:
/// - The index sort is `Int` (1-based TLA+ indexing).
/// - The element sort is configurable (typically `Int` or `Bool`).
/// - A separate `Int` term tracks the length.
#[derive(Debug, Clone)]
pub struct SequenceEncoder {
    /// The sort of each element in the sequence.
    element_sort: Sort,
}

impl SequenceEncoder {
    /// Create a new sequence encoder for the given element sort.
    ///
    /// The element sort determines the range of the underlying SMT array.
    /// Common choices: `Sort::Int` for integer sequences, `Sort::Bool` for
    /// boolean sequences.
    #[must_use]
    pub fn new(element_sort: Sort) -> Self {
        Self { element_sort }
    }

    /// Get the SMT sort for the underlying array: `(Array Int ElemSort)`.
    #[must_use]
    pub fn array_sort(&self) -> Sort {
        Sort::array(Sort::Int, self.element_sort.clone())
    }

    /// Get the element sort.
    #[must_use]
    pub fn element_sort(&self) -> &Sort {
        &self.element_sort
    }

    // =========================================================================
    // Construction
    // =========================================================================

    /// Encode the empty sequence `<<>>`.
    ///
    /// Returns a `SeqTerm` with length = 0. The array contents at
    /// all indices are unconstrained (irrelevant since length is 0).
    pub fn empty_seq(&self, trans: &mut Z4Translator) -> Z4Result<SeqTerm> {
        let arr = self.declare_fresh_array(trans, "seq_empty")?;
        let len = trans.solver_mut().int_const(0);
        Ok(SeqTerm { array: arr, len })
    }

    /// Encode a sequence enumeration `<<e1, ..., en>>`.
    ///
    /// Builds an array with `(store arr 1 e1) ... (store arr n en)`
    /// and sets length = n.
    ///
    /// Each element must have the same sort as `self.element_sort`.
    pub fn encode_seq_enum(
        &self,
        trans: &mut Z4Translator,
        elements: &[Term],
    ) -> Z4Result<SeqTerm> {
        let mut arr = self.declare_fresh_array(trans, "seq_enum")?;

        // Store each element at its 1-based index.
        for (i, &elem) in elements.iter().enumerate() {
            let idx = trans.solver_mut().int_const((i + 1) as i64);
            arr = trans.solver_mut().try_store(arr, idx, elem)?;
        }

        let len = trans.solver_mut().int_const(elements.len() as i64);
        Ok(SeqTerm { array: arr, len })
    }

    /// Declare a fresh symbolic sequence variable with bounded length.
    ///
    /// Returns a `SeqTerm` whose length is constrained to `0 <= len <= max_len`.
    /// The array contents at indices > len are unconstrained.
    pub fn declare_symbolic_seq(
        &self,
        trans: &mut Z4Translator,
        name: &str,
        max_len: usize,
    ) -> Z4Result<SeqTerm> {
        let arr_name = format!("{name}__arr");
        let len_name = format!("{name}__len");

        let arr = trans
            .solver_mut()
            .declare_const(&arr_name, self.array_sort());
        let len = trans.solver_mut().declare_const(&len_name, Sort::Int);

        // Constrain: 0 <= len <= max_len
        let zero = trans.solver_mut().int_const(0);
        let max = trans.solver_mut().int_const(max_len as i64);
        let ge_zero = trans.solver_mut().try_ge(len, zero)?;
        let le_max = trans.solver_mut().try_le(len, max)?;
        trans.assert(ge_zero);
        trans.assert(le_max);

        Ok(SeqTerm { array: arr, len })
    }

    // =========================================================================
    // Accessors
    // =========================================================================

    /// Encode `Len(s)` — returns the length term of the sequence.
    ///
    /// This is just the `len` component of the `SeqTerm`.
    #[must_use]
    pub fn encode_len(&self, seq: &SeqTerm) -> Term {
        seq.len
    }

    /// Encode `Head(s)` — `(select arr 1)`.
    ///
    /// TLA+ requires `Len(s) >= 1` for Head to be defined. This method
    /// does NOT assert that guard; callers should add it if needed.
    pub fn encode_head(&self, trans: &mut Z4Translator, seq: &SeqTerm) -> Z4Result<Term> {
        let one = trans.solver_mut().int_const(1);
        Ok(trans.solver_mut().try_select(seq.array, one)?)
    }

    /// Encode `s[i]` — `(select arr i)` for a given index term.
    ///
    /// TLA+ requires `1 <= i <= Len(s)` for indexing to be defined.
    /// This method does NOT assert bounds; callers should add guards.
    pub fn encode_index(
        &self,
        trans: &mut Z4Translator,
        seq: &SeqTerm,
        index: Term,
    ) -> Z4Result<Term> {
        Ok(trans.solver_mut().try_select(seq.array, index)?)
    }

    // =========================================================================
    // Derived operations
    // =========================================================================

    /// Encode `Tail(s)` — a new sequence with the first element removed.
    ///
    /// The result has `len' = len - 1` and for each index `i` in `1..len-1`:
    /// `(select result_arr i) = (select s_arr (i+1))`.
    ///
    /// Since SMT arrays cannot express arbitrary index shifts natively,
    /// we create a fresh array and assert the shift constraint for each
    /// index in `1..max_len`. The `max_len` parameter bounds the expansion.
    pub fn encode_tail(
        &self,
        trans: &mut Z4Translator,
        seq: &SeqTerm,
        max_len: usize,
    ) -> Z4Result<SeqTerm> {
        let result_arr = self.declare_fresh_array(trans, "seq_tail")?;

        // For each position i in 1..max_len, assert:
        //   i < len => (select result i) = (select seq (i+1))
        for i in 1..max_len {
            let i_term = trans.solver_mut().int_const(i as i64);
            let i_plus_1 = trans.solver_mut().int_const((i + 1) as i64);

            let in_bounds = trans.solver_mut().try_lt(i_term, seq.len)?;
            let src_val = trans.solver_mut().try_select(seq.array, i_plus_1)?;
            let dst_val = trans.solver_mut().try_select(result_arr, i_term)?;
            let vals_eq = trans.solver_mut().try_eq(dst_val, src_val)?;
            let guarded = trans.solver_mut().try_implies(in_bounds, vals_eq)?;
            trans.assert(guarded);
        }

        // len' = max(0, len - 1)
        // Guard against Tail of empty sequence producing negative length.
        // TLA+ leaves Tail(<<>>) undefined, but the SMT encoding must not
        // produce an unconstrained negative length term.
        let one = trans.solver_mut().int_const(1);
        let zero = trans.solver_mut().int_const(0);
        let raw_len = trans.solver_mut().try_sub(seq.len, one)?;
        let len_ge_one = trans.solver_mut().try_ge(seq.len, one)?;
        let new_len = trans.solver_mut().try_ite(len_ge_one, raw_len, zero)?;

        Ok(SeqTerm {
            array: result_arr,
            len: new_len,
        })
    }

    /// Encode `Append(s, e)` — append element `e` to sequence `s`.
    ///
    /// Result: `(store arr (len+1) e)` with `len' = len + 1`.
    pub fn encode_append(
        &self,
        trans: &mut Z4Translator,
        seq: &SeqTerm,
        element: Term,
    ) -> Z4Result<SeqTerm> {
        let one = trans.solver_mut().int_const(1);
        let new_len = trans.solver_mut().try_add(seq.len, one)?;
        let new_arr = trans.solver_mut().try_store(seq.array, new_len, element)?;

        Ok(SeqTerm {
            array: new_arr,
            len: new_len,
        })
    }

    /// Encode `s \o t` (concatenation) — merge two sequences.
    ///
    /// The result has `len' = len_s + len_t`. For indices in `1..len_s`,
    /// the result reads from `s`. For indices in `len_s+1..len_s+len_t`,
    /// the result reads from `t` with shifted index.
    ///
    /// Since SMT arrays cannot express conditional reads natively,
    /// we create a fresh array and assert per-index constraints
    /// bounded by `max_len`.
    pub fn encode_concat(
        &self,
        trans: &mut Z4Translator,
        seq_s: &SeqTerm,
        seq_t: &SeqTerm,
        max_len: usize,
    ) -> Z4Result<SeqTerm> {
        let result_arr = self.declare_fresh_array(trans, "seq_concat")?;
        let new_len = trans.solver_mut().try_add(seq_s.len, seq_t.len)?;

        for i in 1..=max_len {
            let i_term = trans.solver_mut().int_const(i as i64);

            // Case 1: i <= len_s => result[i] = s[i]
            let in_s = trans.solver_mut().try_le(i_term, seq_s.len)?;
            let s_val = trans.solver_mut().try_select(seq_s.array, i_term)?;
            let r_val = trans.solver_mut().try_select(result_arr, i_term)?;
            let eq_s = trans.solver_mut().try_eq(r_val, s_val)?;
            let guard_s = trans.solver_mut().try_implies(in_s, eq_s)?;
            trans.assert(guard_s);

            // Case 2: i > len_s AND i <= len_s + len_t
            //       => result[i] = t[i - len_s]
            let gt_s = trans.solver_mut().try_gt(i_term, seq_s.len)?;
            let le_total = trans.solver_mut().try_le(i_term, new_len)?;
            let in_t = trans.solver_mut().try_and(gt_s, le_total)?;
            let offset = trans.solver_mut().try_sub(i_term, seq_s.len)?;
            let t_val = trans.solver_mut().try_select(seq_t.array, offset)?;
            let r_val2 = trans.solver_mut().try_select(result_arr, i_term)?;
            let eq_t = trans.solver_mut().try_eq(r_val2, t_val)?;
            let guard_t = trans.solver_mut().try_implies(in_t, eq_t)?;
            trans.assert(guard_t);
        }

        Ok(SeqTerm {
            array: result_arr,
            len: new_len,
        })
    }

    /// Encode `SubSeq(s, m, n)` — subsequence from index m to n (inclusive).
    ///
    /// The result has `len' = max(0, n - m + 1)` and for each index `i`:
    /// `result[i] = s[m + i - 1]`.
    ///
    /// `m` and `n` are SMT Int terms (1-indexed, following TLA+ convention).
    /// The `max_len` parameter bounds the finite expansion.
    pub fn encode_subseq(
        &self,
        trans: &mut Z4Translator,
        seq: &SeqTerm,
        m: Term,
        n: Term,
        max_len: usize,
    ) -> Z4Result<SeqTerm> {
        let result_arr = self.declare_fresh_array(trans, "seq_subseq")?;

        // new_len = max(0, n - m + 1)
        let one = trans.solver_mut().int_const(1);
        let zero = trans.solver_mut().int_const(0);
        let n_minus_m = trans.solver_mut().try_sub(n, m)?;
        let raw_len = trans.solver_mut().try_add(n_minus_m, one)?;
        let len_positive = trans.solver_mut().try_gt(raw_len, zero)?;
        let new_len = trans.solver_mut().try_ite(len_positive, raw_len, zero)?;

        // For each index i in 1..=max_len:
        //   i <= new_len => result[i] = s[m + i - 1]
        for i in 1..=max_len {
            let i_term = trans.solver_mut().int_const(i as i64);
            let in_bounds = trans.solver_mut().try_le(i_term, new_len)?;

            // source index = m + i - 1
            let m_plus_i = trans.solver_mut().try_add(m, i_term)?;
            let src_idx = trans.solver_mut().try_sub(m_plus_i, one)?;

            let src_val = trans.solver_mut().try_select(seq.array, src_idx)?;
            let dst_val = trans.solver_mut().try_select(result_arr, i_term)?;
            let vals_eq = trans.solver_mut().try_eq(dst_val, src_val)?;
            let guarded = trans.solver_mut().try_implies(in_bounds, vals_eq)?;
            trans.assert(guarded);
        }

        Ok(SeqTerm {
            array: result_arr,
            len: new_len,
        })
    }

    /// Encode `Seq(S)` for bounded symbolic generation.
    ///
    /// Generates a symbolic sequence of length up to `max_len` where
    /// each element is constrained to be a member of the given `domain`
    /// set (represented as a list of concrete element terms).
    ///
    /// This is useful for encoding `s \in Seq(S)` where S is finite:
    /// the returned sequence has symbolic length and symbolic elements,
    /// each constrained to be in S.
    pub fn encode_seq_of_set(
        &self,
        trans: &mut Z4Translator,
        domain: &[Term],
        max_len: usize,
    ) -> Z4Result<SeqTerm> {
        let name = trans.fresh_name("seq_of");
        let seq = self.declare_symbolic_seq(trans, &name, max_len)?;

        if domain.is_empty() {
            // Seq({}) contains only <<>>
            let zero = trans.solver_mut().int_const(0);
            let len_eq_zero = trans.solver_mut().try_eq(seq.len, zero)?;
            trans.assert(len_eq_zero);
            return Ok(seq);
        }

        // For each index i in 1..=max_len:
        //   i <= len => (select arr i) \in domain
        // Membership is encoded as a disjunction: elem = d1 \/ elem = d2 \/ ...
        for i in 1..=max_len {
            let i_term = trans.solver_mut().int_const(i as i64);
            let in_bounds = trans.solver_mut().try_le(i_term, seq.len)?;
            let elem = trans.solver_mut().try_select(seq.array, i_term)?;

            // Build disjunction: elem = d1 \/ elem = d2 \/ ...
            let mut disj = Vec::with_capacity(domain.len());
            for &d in domain {
                let eq = trans.solver_mut().try_eq(elem, d)?;
                disj.push(eq);
            }
            let in_domain = if disj.len() == 1 {
                disj[0]
            } else {
                trans.solver_mut().try_or_many(&disj)?
            };

            let guarded = trans.solver_mut().try_implies(in_bounds, in_domain)?;
            trans.assert(guarded);
        }

        Ok(seq)
    }

    // =========================================================================
    // Equality and comparison
    // =========================================================================

    /// Encode sequence equality `s = t` over a bounded range.
    ///
    /// Two sequences are equal iff they have the same length and
    /// agree on all indices within that length:
    /// `len_s = len_t /\ \A i in 1..max_len: i <= len_s => s[i] = t[i]`
    pub fn encode_seq_eq(
        &self,
        trans: &mut Z4Translator,
        seq_s: &SeqTerm,
        seq_t: &SeqTerm,
        max_len: usize,
    ) -> Z4Result<Term> {
        let len_eq = trans.solver_mut().try_eq(seq_s.len, seq_t.len)?;

        let mut conjuncts = vec![len_eq];
        for i in 1..=max_len {
            let i_term = trans.solver_mut().int_const(i as i64);
            let in_bounds = trans.solver_mut().try_le(i_term, seq_s.len)?;
            let s_val = trans.solver_mut().try_select(seq_s.array, i_term)?;
            let t_val = trans.solver_mut().try_select(seq_t.array, i_term)?;
            let vals_eq = trans.solver_mut().try_eq(s_val, t_val)?;
            let guarded = trans.solver_mut().try_implies(in_bounds, vals_eq)?;
            conjuncts.push(guarded);
        }

        if conjuncts.len() == 1 {
            Ok(conjuncts[0])
        } else {
            Ok(trans.solver_mut().try_and_many(&conjuncts)?)
        }
    }

    // =========================================================================
    // Internal helpers
    // =========================================================================

    /// Declare a fresh array variable `(Array Int ElemSort)` with a unique name.
    fn declare_fresh_array(&self, trans: &mut Z4Translator, prefix: &str) -> Z4Result<Term> {
        let name = trans.fresh_name(prefix);
        Ok(trans.solver_mut().declare_const(&name, self.array_sort()))
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
    // Construction tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_seq_has_length_zero() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        let seq = enc.empty_seq(&mut trans).unwrap();

        // Assert Len(seq) = 0
        let zero = trans.solver_mut().int_const(0);
        let len_eq = trans.solver_mut().try_eq(seq.len, zero).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_seq_length_nonzero_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        let seq = enc.empty_seq(&mut trans).unwrap();

        // Assert Len(seq) = 1 (should be UNSAT since empty seq has len 0)
        let one = trans.solver_mut().int_const(1);
        let len_eq = trans.solver_mut().try_eq(seq.len, one).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_enum_length() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // Assert Len(seq) = 3
        let three = trans.solver_mut().int_const(3);
        let len_eq = trans.solver_mut().try_eq(seq.len, three).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_enum_head() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // Head(seq) = 10
        let head = enc.encode_head(&mut trans, &seq).unwrap();
        let ten = trans.solver_mut().int_const(10);
        let eq = trans.solver_mut().try_eq(head, ten).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_enum_head_wrong_value_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // Head(seq) = 20 (should be UNSAT, head is 10)
        let head = enc.encode_head(&mut trans, &seq).unwrap();
        let twenty = trans.solver_mut().int_const(20);
        let eq = trans.solver_mut().try_eq(head, twenty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_enum_index() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // seq[2] = 20
        let idx = trans.solver_mut().int_const(2);
        let val = enc.encode_index(&mut trans, &seq, idx).unwrap();
        let twenty = trans.solver_mut().int_const(20);
        let eq = trans.solver_mut().try_eq(val, twenty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_enum_index_third() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        // seq[3] = 30
        let idx = trans.solver_mut().int_const(3);
        let val = enc.encode_index(&mut trans, &seq, idx).unwrap();
        let thirty = trans.solver_mut().int_const(30);
        let eq = trans.solver_mut().try_eq(val, thirty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Append tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_append_length() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20>> then Append(_, 30)
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

        let e3 = trans.solver_mut().int_const(30);
        let appended = enc.encode_append(&mut trans, &seq, e3).unwrap();

        // Len(appended) = 3
        let three = trans.solver_mut().int_const(3);
        let len_eq = trans.solver_mut().try_eq(appended.len, three).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_append_element_at_end() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20>> then Append(_, 30)
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

        let e3 = trans.solver_mut().int_const(30);
        let appended = enc.encode_append(&mut trans, &seq, e3).unwrap();

        // appended[3] = 30
        let idx = trans.solver_mut().int_const(3);
        let val = enc.encode_index(&mut trans, &appended, idx).unwrap();
        let thirty = trans.solver_mut().int_const(30);
        let eq = trans.solver_mut().try_eq(val, thirty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_append_preserves_existing() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20>> then Append(_, 30)
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

        let e3 = trans.solver_mut().int_const(30);
        let appended = enc.encode_append(&mut trans, &seq, e3).unwrap();

        // appended[1] = 10 (original first element preserved)
        let idx = trans.solver_mut().int_const(1);
        let val = enc.encode_index(&mut trans, &appended, idx).unwrap();
        let ten = trans.solver_mut().int_const(10);
        let eq = trans.solver_mut().try_eq(val, ten).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Tail tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tail_length() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let tail = enc.encode_tail(&mut trans, &seq, 3).unwrap();

        // Len(Tail(seq)) = 2
        let two = trans.solver_mut().int_const(2);
        let len_eq = trans.solver_mut().try_eq(tail.len, two).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tail_shifts_elements() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let tail = enc.encode_tail(&mut trans, &seq, 3).unwrap();

        // Tail(seq)[1] = 20 (shifted from original index 2)
        let idx = trans.solver_mut().int_const(1);
        let val = enc.encode_index(&mut trans, &tail, idx).unwrap();
        let twenty = trans.solver_mut().int_const(20);
        let eq = trans.solver_mut().try_eq(val, twenty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tail_second_element() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<10, 20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let tail = enc.encode_tail(&mut trans, &seq, 3).unwrap();

        // Tail(seq)[2] = 30 (shifted from original index 3)
        let idx = trans.solver_mut().int_const(2);
        let val = enc.encode_index(&mut trans, &tail, idx).unwrap();
        let thirty = trans.solver_mut().int_const(30);
        let eq = trans.solver_mut().try_eq(val, thirty).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Concatenation tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_concat_length() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2>> \o <<3, 4, 5>>
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let e4 = trans.solver_mut().int_const(4);
        let e5 = trans.solver_mut().int_const(5);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();
        let s2 = enc.encode_seq_enum(&mut trans, &[e3, e4, e5]).unwrap();

        let cat = enc.encode_concat(&mut trans, &s1, &s2, 5).unwrap();

        // Len(s1 \o s2) = 5
        let five = trans.solver_mut().int_const(5);
        let len_eq = trans.solver_mut().try_eq(cat.len, five).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_concat_first_part() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2>> \o <<3, 4, 5>>
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let e4 = trans.solver_mut().int_const(4);
        let e5 = trans.solver_mut().int_const(5);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();
        let s2 = enc.encode_seq_enum(&mut trans, &[e3, e4, e5]).unwrap();

        let cat = enc.encode_concat(&mut trans, &s1, &s2, 5).unwrap();

        // cat[1] = 1, cat[2] = 2 (from s1)
        let idx1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_index(&mut trans, &cat, idx1).unwrap();
        let one = trans.solver_mut().int_const(1);
        let eq1 = trans.solver_mut().try_eq(val1, one).unwrap();
        trans.assert(eq1);

        let idx2 = trans.solver_mut().int_const(2);
        let val2 = enc.encode_index(&mut trans, &cat, idx2).unwrap();
        let two = trans.solver_mut().int_const(2);
        let eq2 = trans.solver_mut().try_eq(val2, two).unwrap();
        trans.assert(eq2);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_concat_second_part() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2>> \o <<3, 4, 5>>
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let e4 = trans.solver_mut().int_const(4);
        let e5 = trans.solver_mut().int_const(5);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();
        let s2 = enc.encode_seq_enum(&mut trans, &[e3, e4, e5]).unwrap();

        let cat = enc.encode_concat(&mut trans, &s1, &s2, 5).unwrap();

        // cat[3] = 3, cat[4] = 4, cat[5] = 5 (from s2)
        let idx3 = trans.solver_mut().int_const(3);
        let val3 = enc.encode_index(&mut trans, &cat, idx3).unwrap();
        let three = trans.solver_mut().int_const(3);
        let eq3 = trans.solver_mut().try_eq(val3, three).unwrap();
        trans.assert(eq3);

        let idx5 = trans.solver_mut().int_const(5);
        let val5 = enc.encode_index(&mut trans, &cat, idx5).unwrap();
        let five = trans.solver_mut().int_const(5);
        let eq5 = trans.solver_mut().try_eq(val5, five).unwrap();
        trans.assert(eq5);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // SubSeq tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subseq_length() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // SubSeq(<<10, 20, 30, 40>>, 2, 3) => <<20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let e4 = trans.solver_mut().int_const(40);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3, e4]).unwrap();

        let m = trans.solver_mut().int_const(2);
        let n = trans.solver_mut().int_const(3);
        let sub = enc.encode_subseq(&mut trans, &seq, m, n, 4).unwrap();

        // Len(SubSeq) = 2
        let two = trans.solver_mut().int_const(2);
        let len_eq = trans.solver_mut().try_eq(sub.len, two).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subseq_elements() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // SubSeq(<<10, 20, 30, 40>>, 2, 3) => <<20, 30>>
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let e4 = trans.solver_mut().int_const(40);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3, e4]).unwrap();

        let m = trans.solver_mut().int_const(2);
        let n = trans.solver_mut().int_const(3);
        let sub = enc.encode_subseq(&mut trans, &seq, m, n, 4).unwrap();

        // sub[1] = 20
        let idx1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_index(&mut trans, &sub, idx1).unwrap();
        let twenty = trans.solver_mut().int_const(20);
        let eq1 = trans.solver_mut().try_eq(val1, twenty).unwrap();
        trans.assert(eq1);

        // sub[2] = 30
        let idx2 = trans.solver_mut().int_const(2);
        let val2 = enc.encode_index(&mut trans, &sub, idx2).unwrap();
        let thirty = trans.solver_mut().int_const(30);
        let eq2 = trans.solver_mut().try_eq(val2, thirty).unwrap();
        trans.assert(eq2);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_subseq_empty_when_m_gt_n() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // SubSeq(<<10, 20, 30>>, 3, 1) => <<>> (m > n)
        let e1 = trans.solver_mut().int_const(10);
        let e2 = trans.solver_mut().int_const(20);
        let e3 = trans.solver_mut().int_const(30);
        let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let m = trans.solver_mut().int_const(3);
        let n = trans.solver_mut().int_const(1);
        let sub = enc.encode_subseq(&mut trans, &seq, m, n, 3).unwrap();

        // Len(SubSeq) = 0
        let zero = trans.solver_mut().int_const(0);
        let len_eq = trans.solver_mut().try_eq(sub.len, zero).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    // =========================================================================
    // Seq(S) bounded generation tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_of_set_elements_in_domain() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Seq({1, 2}) with max_len=3
        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let seq = enc.encode_seq_of_set(&mut trans, &[d1, d2], 3).unwrap();

        // Force Len(seq) = 2
        let two = trans.solver_mut().int_const(2);
        let len_eq = trans.solver_mut().try_eq(seq.len, two).unwrap();
        trans.assert(len_eq);

        // seq[1] must be 1 or 2
        assert!(matches!(trans.check_sat(), SolveResult::Sat));

        // The constraints ensure elements are within domain; SAT is sufficient.
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_of_empty_set_is_empty() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Seq({}) with max_len=3 => only <<>> is valid
        let seq = enc.encode_seq_of_set(&mut trans, &[], 3).unwrap();

        // Len must be 0
        let zero = trans.solver_mut().int_const(0);
        let len_eq = trans.solver_mut().try_eq(seq.len, zero).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_of_empty_set_nonzero_len_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Seq({}) with max_len=3 => Len > 0 should be UNSAT
        let seq = enc.encode_seq_of_set(&mut trans, &[], 3).unwrap();

        let one = trans.solver_mut().int_const(1);
        let len_eq = trans.solver_mut().try_eq(seq.len, one).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Equality tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_eq_same_sequences() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2, 3>> = <<1, 2, 3>>
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let f1 = trans.solver_mut().int_const(1);
        let f2 = trans.solver_mut().int_const(2);
        let f3 = trans.solver_mut().int_const(3);
        let s2 = enc.encode_seq_enum(&mut trans, &[f1, f2, f3]).unwrap();

        let eq = enc.encode_seq_eq(&mut trans, &s1, &s2, 3).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_eq_different_lengths_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2>> = <<1, 2, 3>> should be UNSAT
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

        let f1 = trans.solver_mut().int_const(1);
        let f2 = trans.solver_mut().int_const(2);
        let f3 = trans.solver_mut().int_const(3);
        let s2 = enc.encode_seq_enum(&mut trans, &[f1, f2, f3]).unwrap();

        let eq = enc.encode_seq_eq(&mut trans, &s1, &s2, 3).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_eq_different_elements_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2, 3>> = <<1, 99, 3>> should be UNSAT
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let e3 = trans.solver_mut().int_const(3);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

        let f1 = trans.solver_mut().int_const(1);
        let f2 = trans.solver_mut().int_const(99);
        let f3 = trans.solver_mut().int_const(3);
        let s2 = enc.encode_seq_enum(&mut trans, &[f1, f2, f3]).unwrap();

        let eq = enc.encode_seq_eq(&mut trans, &s1, &s2, 3).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Symbolic sequence tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_seq_length_bounded() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        let seq = enc.declare_symbolic_seq(&mut trans, "s", 5).unwrap();

        // Assert Len(s) = 5 (should be SAT since max_len = 5)
        let five = trans.solver_mut().int_const(5);
        let len_eq = trans.solver_mut().try_eq(seq.len, five).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_seq_length_exceeds_bound_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        let seq = enc.declare_symbolic_seq(&mut trans, "s", 5).unwrap();

        // Assert Len(s) = 6 (should be UNSAT since max_len = 5)
        let six = trans.solver_mut().int_const(6);
        let len_eq = trans.solver_mut().try_eq(seq.len, six).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symbolic_seq_negative_length_unsat() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        let seq = enc.declare_symbolic_seq(&mut trans, "s", 5).unwrap();

        // Assert Len(s) = -1 (should be UNSAT since len >= 0)
        let neg1 = trans.solver_mut().int_const(-1);
        let len_eq = trans.solver_mut().try_eq(seq.len, neg1).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // =========================================================================
    // Combined operation tests
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_append_then_head() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Append(<<>>, 42) then Head
        let empty = enc.empty_seq(&mut trans).unwrap();
        let val = trans.solver_mut().int_const(42);
        let appended = enc.encode_append(&mut trans, &empty, val).unwrap();

        let head = enc.encode_head(&mut trans, &appended).unwrap();
        let forty_two = trans.solver_mut().int_const(42);
        let eq = trans.solver_mut().try_eq(head, forty_two).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tail_of_singleton_is_empty() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Tail(<<42>>) has length 0
        let e1 = trans.solver_mut().int_const(42);
        let seq = enc.encode_seq_enum(&mut trans, &[e1]).unwrap();
        let tail = enc.encode_tail(&mut trans, &seq, 1).unwrap();

        let zero = trans.solver_mut().int_const(0);
        let len_eq = trans.solver_mut().try_eq(tail.len, zero).unwrap();
        trans.assert(len_eq);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_concat_with_empty() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // <<1, 2>> \o <<>> has length 2
        let e1 = trans.solver_mut().int_const(1);
        let e2 = trans.solver_mut().int_const(2);
        let s1 = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();
        let empty = enc.empty_seq(&mut trans).unwrap();

        let cat = enc.encode_concat(&mut trans, &s1, &empty, 2).unwrap();

        // Len = 2
        let two = trans.solver_mut().int_const(2);
        let len_eq = trans.solver_mut().try_eq(cat.len, two).unwrap();
        trans.assert(len_eq);

        // cat[1] = 1
        let idx1 = trans.solver_mut().int_const(1);
        let val1 = enc.encode_index(&mut trans, &cat, idx1).unwrap();
        let one = trans.solver_mut().int_const(1);
        let eq1 = trans.solver_mut().try_eq(val1, one).unwrap();
        trans.assert(eq1);

        assert!(matches!(trans.check_sat(), SolveResult::Sat));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_of_set_rejects_out_of_domain() {
        let mut trans = array_translator();
        let enc = SequenceEncoder::new(Sort::Int);

        // Seq({1, 2}) with max_len=2
        let d1 = trans.solver_mut().int_const(1);
        let d2 = trans.solver_mut().int_const(2);
        let seq = enc.encode_seq_of_set(&mut trans, &[d1, d2], 2).unwrap();

        // Force len = 1 and seq[1] = 3 (NOT in domain) => UNSAT
        let one_len = trans.solver_mut().int_const(1);
        let len_eq = trans.solver_mut().try_eq(seq.len, one_len).unwrap();
        trans.assert(len_eq);

        let idx1 = trans.solver_mut().int_const(1);
        let val1 = trans.solver_mut().try_select(seq.array, idx1).unwrap();
        let three = trans.solver_mut().int_const(3);
        let eq3 = trans.solver_mut().try_eq(val1, three).unwrap();
        trans.assert(eq3);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }
}
