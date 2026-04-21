// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence operations for Z4 translation.
//!
//! Bridges the per-variable `SequenceVarInfo` representation (used for
//! `s[i]` indexing via ITE chains) with the array-based `SequenceEncoder`
//! (used for compositional operations like Tail, Append, SubSeq).
//!
//! # Dispatch
//!
//! - `s[i]` — dispatched from `membership/mod.rs` via `translate_seq_apply_{bool,int}`
//! - `Len(s)`, `Head(s)`, `Tail(s)`, `Append(s,e)`, `SubSeq(s,m,n)` — dispatched
//!   from `translate_expr_impl.rs` via `Expr::Apply` in `translate_{bool,int}_extended`
//!
//! Part of #3793: sequence encoding as bounded arrays.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::{Sort, Term};

use super::sequence_encoder::{SeqTerm, SequenceEncoder};
use super::{SequenceVarInfo, TlaSort, Z4Translator};
use crate::error::{Z4Error, Z4Result};

// =========================================================================
// Default max_len for intermediate sequences when no SequenceVarInfo exists
// =========================================================================
const DEFAULT_MAX_LEN: usize = 10;

impl Z4Translator {
    // =====================================================================
    // s[i] indexing (dispatched from membership/mod.rs)
    // =====================================================================

    /// Translate sequence application `s[i]` returning Bool.
    ///
    /// Uses an ITE chain over per-variable terms (same pattern as tuple indexing).
    pub(super) fn translate_seq_apply_bool(
        &mut self,
        var_name: &str,
        seq_info: &SequenceVarInfo,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        if seq_info.element_sort != TlaSort::Bool {
            return Err(Z4Error::TypeMismatch {
                name: format!("{var_name}[i]"),
                expected: "Bool".to_string(),
                actual: format!("{}", seq_info.element_sort),
            });
        }

        // Constant index fast path
        if let Some(idx) = self.try_expr_to_int(arg) {
            if idx < 1 || idx as usize > seq_info.max_len {
                return Err(Z4Error::UnsupportedOp(format!(
                    "sequence index {idx} out of bounds (max_len={})",
                    seq_info.max_len
                )));
            }
            return seq_info
                .element_terms
                .get(&(idx as usize))
                .copied()
                .ok_or_else(|| Z4Error::UnsupportedOp(format!("{var_name}[{idx}] not found")));
        }

        // Dynamic index: build ITE chain
        self.build_seq_ite_chain_bool(var_name, seq_info, arg)
    }

    /// Translate sequence application `s[i]` returning Int.
    ///
    /// Uses an ITE chain over per-variable terms (same pattern as tuple indexing).
    pub(super) fn translate_seq_apply_int(
        &mut self,
        var_name: &str,
        seq_info: &SequenceVarInfo,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        if seq_info.element_sort != TlaSort::Int {
            return Err(Z4Error::TypeMismatch {
                name: format!("{var_name}[i]"),
                expected: "Int".to_string(),
                actual: format!("{}", seq_info.element_sort),
            });
        }

        // Constant index fast path
        if let Some(idx) = self.try_expr_to_int(arg) {
            if idx < 1 || idx as usize > seq_info.max_len {
                return Err(Z4Error::UnsupportedOp(format!(
                    "sequence index {idx} out of bounds (max_len={})",
                    seq_info.max_len
                )));
            }
            return seq_info
                .element_terms
                .get(&(idx as usize))
                .copied()
                .ok_or_else(|| Z4Error::UnsupportedOp(format!("{var_name}[{idx}] not found")));
        }

        // Dynamic index: build ITE chain
        self.build_seq_ite_chain_int(var_name, seq_info, arg)
    }

    // =====================================================================
    // ITE chain builders (mirror tuple.rs pattern)
    // =====================================================================

    /// Build ITE chain: IF idx=1 THEN s__1 ELSE IF idx=2 THEN s__2 ELSE ... s__n
    fn build_seq_ite_chain_int(
        &mut self,
        var_name: &str,
        seq_info: &SequenceVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let index_term = self.translate_int(index)?;
        let max = seq_info.max_len;

        // Default to last element
        let mut result = seq_info
            .element_terms
            .get(&max)
            .copied()
            .ok_or_else(|| Z4Error::UnsupportedOp(format!("{var_name}[{max}] not found")))?;

        // Build from max-1 down to 1
        for idx in (1..max).rev() {
            let idx_const = self.solver_mut().int_const(idx as i64);
            let cond = self.solver_mut().try_eq(index_term, idx_const)?;
            let elem_term =
                seq_info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{var_name}[{idx}] not found"))
                })?;
            result = self.solver_mut().try_ite(cond, elem_term, result)?;
        }

        Ok(result)
    }

    /// Build ITE chain for Bool-sorted sequence elements.
    fn build_seq_ite_chain_bool(
        &mut self,
        var_name: &str,
        seq_info: &SequenceVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let index_term = self.translate_int(index)?;
        let max = seq_info.max_len;

        let mut result = seq_info
            .element_terms
            .get(&max)
            .copied()
            .ok_or_else(|| Z4Error::UnsupportedOp(format!("{var_name}[{max}] not found")))?;

        for idx in (1..max).rev() {
            let idx_const = self.solver_mut().int_const(idx as i64);
            let cond = self.solver_mut().try_eq(index_term, idx_const)?;
            let elem_term =
                seq_info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{var_name}[{idx}] not found"))
                })?;
            result = self.solver_mut().try_ite(cond, elem_term, result)?;
        }

        Ok(result)
    }

    // =====================================================================
    // Stdlib sequence operations (dispatched from translate_expr_impl.rs)
    // =====================================================================

    /// Try to translate a sequence operation returning Bool.
    ///
    /// Handles `Expr::Apply(Ident("Head"), [s])` when the sequence has Bool elements.
    /// Returns `None` if the Apply is not a recognized sequence operation.
    pub(super) fn try_translate_seq_op_bool(
        &mut self,
        func: &Spanned<Expr>,
        args: &[Spanned<Expr>],
    ) -> Option<Z4Result<Term>> {
        let name = match &func.node {
            Expr::Ident(name, _) => name.as_str(),
            _ => return None,
        };

        match name {
            "Head" if args.len() == 1 => Some(self.translate_head_bool(&args[0])),
            _ => None,
        }
    }

    /// Try to translate a sequence operation returning Int.
    ///
    /// Handles:
    /// - `Len(s)` — always returns Int
    /// - `Head(s)` — when the sequence has Int elements
    ///
    /// Returns `None` if the Apply is not a recognized sequence operation.
    pub(super) fn try_translate_seq_op_int(
        &mut self,
        func: &Spanned<Expr>,
        args: &[Spanned<Expr>],
    ) -> Option<Z4Result<Term>> {
        let name = match &func.node {
            Expr::Ident(name, _) => name.as_str(),
            _ => return None,
        };

        match name {
            "Len" if args.len() == 1 => Some(self.translate_len(&args[0])),
            "Head" if args.len() == 1 => Some(self.translate_head_int(&args[0])),
            _ => None,
        }
    }

    // =====================================================================
    // Individual operation implementations
    // =====================================================================

    /// Translate `Len(s)` — returns the length term of the sequence.
    fn translate_len(&mut self, seq_expr: &Spanned<Expr>) -> Z4Result<Term> {
        let seq = self.resolve_seq_term(seq_expr)?;
        let enc = SequenceEncoder::new(Sort::Int); // sort doesn't matter for Len
        Ok(enc.encode_len(&seq))
    }

    /// Translate `Head(s)` where the sequence has Int elements.
    fn translate_head_int(&mut self, seq_expr: &Spanned<Expr>) -> Z4Result<Term> {
        let (seq, elem_sort) = self.resolve_seq_term_with_sort(seq_expr)?;
        let enc = SequenceEncoder::new(elem_sort);
        enc.encode_head(self, &seq)
    }

    /// Translate `Head(s)` where the sequence has Bool elements.
    fn translate_head_bool(&mut self, seq_expr: &Spanned<Expr>) -> Z4Result<Term> {
        let (seq, elem_sort) = self.resolve_seq_term_with_sort(seq_expr)?;
        let enc = SequenceEncoder::new(elem_sort);
        enc.encode_head(self, &seq)
    }

    // =====================================================================
    // SeqTerm resolution: bridge SequenceVarInfo -> SeqTerm
    // =====================================================================

    /// Resolve a TLA+ expression to a `SeqTerm` (array + length).
    ///
    /// For `Ident` expressions that reference a declared sequence variable,
    /// converts the per-variable `SequenceVarInfo` into an array-based `SeqTerm`
    /// by building `(store ... (store arr 1 s__1) 2 s__2) ... n s__n)`.
    fn resolve_seq_term(&mut self, expr: &Spanned<Expr>) -> Z4Result<SeqTerm> {
        let (seq, _sort) = self.resolve_seq_term_with_sort(expr)?;
        Ok(seq)
    }

    /// Like `resolve_seq_term` but also returns the element sort.
    ///
    /// Handles:
    /// - `Ident(name)` — lookup in `seq_vars` and bridge to `SeqTerm`
    /// - `Apply(Ident("Tail"), [s])` — resolve `s` then apply Tail encoding
    /// - `Apply(Ident("Append"), [s, e])` — resolve `s` then apply Append encoding
    /// - `Apply(Ident("SubSeq"), [s, m, n])` — resolve `s` then apply SubSeq encoding
    /// - `Apply(Ident("\\o"), [s, t])` — resolve both then apply Concat encoding
    fn resolve_seq_term_with_sort(&mut self, expr: &Spanned<Expr>) -> Z4Result<(SeqTerm, Sort)> {
        match &expr.node {
            Expr::Ident(name, _) => {
                if let Some(info) = self.seq_vars.get(name).cloned() {
                    let z4_sort = info.element_sort.to_z4()?;
                    let seq = self.seq_var_to_seq_term(&info, &z4_sort)?;
                    Ok((seq, z4_sort))
                } else {
                    Err(Z4Error::UnsupportedOp(format!(
                        "{name} is not a declared sequence variable"
                    )))
                }
            }
            Expr::Apply(op, args) => {
                let name = match &op.node {
                    Expr::Ident(name, _) => name.as_str(),
                    _ => {
                        return Err(Z4Error::UnsupportedOp(
                            "sequence operation on non-Ident Apply not supported".to_string(),
                        ))
                    }
                };
                match name {
                    "Tail" if args.len() == 1 => self.resolve_tail_seq_term(&args[0]),
                    "Append" if args.len() == 2 => self.resolve_append_seq_term(&args[0], &args[1]),
                    "SubSeq" if args.len() == 3 => {
                        self.resolve_subseq_seq_term(&args[0], &args[1], &args[2])
                    }
                    "\\o" if args.len() == 2 => self.resolve_concat_seq_term(&args[0], &args[1]),
                    _ => Err(Z4Error::UnsupportedOp(format!(
                        "unrecognized sequence operation: {name}"
                    ))),
                }
            }
            _ => Err(Z4Error::UnsupportedOp(
                "sequence operations on non-variable expressions not yet supported".to_string(),
            )),
        }
    }

    /// Resolve `Tail(s)` to a `SeqTerm`.
    ///
    /// Recursively resolves `s`, then applies the Tail encoding from
    /// `SequenceEncoder`. Uses the inner sequence's max_len (from
    /// `SequenceVarInfo` if available, otherwise `DEFAULT_MAX_LEN`).
    fn resolve_tail_seq_term(&mut self, seq_expr: &Spanned<Expr>) -> Z4Result<(SeqTerm, Sort)> {
        let max_len = self.infer_max_len(seq_expr);
        let (seq, elem_sort) = self.resolve_seq_term_with_sort(seq_expr)?;
        let enc = SequenceEncoder::new(elem_sort.clone());
        let result = enc.encode_tail(self, &seq, max_len)?;
        Ok((result, elem_sort))
    }

    /// Resolve `Append(s, e)` to a `SeqTerm`.
    ///
    /// Recursively resolves `s`, translates `e` as an Int or Bool term,
    /// then applies the Append encoding from `SequenceEncoder`.
    fn resolve_append_seq_term(
        &mut self,
        seq_expr: &Spanned<Expr>,
        elem_expr: &Spanned<Expr>,
    ) -> Z4Result<(SeqTerm, Sort)> {
        let (seq, elem_sort) = self.resolve_seq_term_with_sort(seq_expr)?;
        let elem_term = match elem_sort {
            Sort::Int => self.translate_int(elem_expr)?,
            Sort::Bool => self.translate_bool(elem_expr)?,
            _ => {
                return Err(Z4Error::UnsupportedOp(format!(
                    "Append: unsupported element sort {elem_sort:?}"
                )))
            }
        };
        let enc = SequenceEncoder::new(elem_sort.clone());
        let result = enc.encode_append(self, &seq, elem_term)?;
        Ok((result, elem_sort))
    }

    /// Resolve `SubSeq(s, m, n)` to a `SeqTerm`.
    ///
    /// Recursively resolves `s`, translates `m` and `n` as Int terms,
    /// then applies the SubSeq encoding from `SequenceEncoder`.
    fn resolve_subseq_seq_term(
        &mut self,
        seq_expr: &Spanned<Expr>,
        m_expr: &Spanned<Expr>,
        n_expr: &Spanned<Expr>,
    ) -> Z4Result<(SeqTerm, Sort)> {
        let max_len = self.infer_max_len(seq_expr);
        let (seq, elem_sort) = self.resolve_seq_term_with_sort(seq_expr)?;
        let m = self.translate_int(m_expr)?;
        let n = self.translate_int(n_expr)?;
        let enc = SequenceEncoder::new(elem_sort.clone());
        let result = enc.encode_subseq(self, &seq, m, n, max_len)?;
        Ok((result, elem_sort))
    }

    /// Resolve `s \o t` (concatenation) to a `SeqTerm`.
    ///
    /// Recursively resolves both `s` and `t`, then applies the Concat
    /// encoding from `SequenceEncoder`.
    fn resolve_concat_seq_term(
        &mut self,
        s_expr: &Spanned<Expr>,
        t_expr: &Spanned<Expr>,
    ) -> Z4Result<(SeqTerm, Sort)> {
        let max_len_s = self.infer_max_len(s_expr);
        let max_len_t = self.infer_max_len(t_expr);
        let (seq_s, elem_sort_s) = self.resolve_seq_term_with_sort(s_expr)?;
        let (seq_t, elem_sort_t) = self.resolve_seq_term_with_sort(t_expr)?;
        // Both sequences must have the same element sort
        if elem_sort_s != elem_sort_t {
            return Err(Z4Error::TypeMismatch {
                name: "\\o".to_string(),
                expected: format!("{elem_sort_s:?}"),
                actual: format!("{elem_sort_t:?}"),
            });
        }
        let max_len = max_len_s + max_len_t;
        let enc = SequenceEncoder::new(elem_sort_s.clone());
        let result = enc.encode_concat(self, &seq_s, &seq_t, max_len)?;
        Ok((result, elem_sort_s))
    }

    /// Infer the max_len for a sequence expression.
    ///
    /// If the expression is an `Ident` referencing a declared sequence variable,
    /// returns that variable's `max_len`. Otherwise returns `DEFAULT_MAX_LEN`.
    fn infer_max_len(&self, expr: &Spanned<Expr>) -> usize {
        match &expr.node {
            Expr::Ident(name, _) => self
                .seq_vars
                .get(name)
                .map_or(DEFAULT_MAX_LEN, |info| info.max_len),
            _ => DEFAULT_MAX_LEN,
        }
    }

    /// Convert a per-variable `SequenceVarInfo` to an array-based `SeqTerm`.
    ///
    /// Builds the array by storing each per-variable term:
    /// `(store (store ... (store base_arr 1 s__1) 2 s__2) ... n s__n)`
    fn seq_var_to_seq_term(
        &mut self,
        info: &SequenceVarInfo,
        elem_sort: &Sort,
    ) -> Z4Result<SeqTerm> {
        let arr_sort = Sort::array(Sort::Int, elem_sort.clone());
        let arr_name = self.fresh_name("seq_arr");
        let mut arr = self.solver_mut().declare_const(&arr_name, arr_sort);

        // Store each per-variable element into the array
        for idx in 1..=info.max_len {
            if let Some(&elem_term) = info.element_terms.get(&idx) {
                let idx_term = self.solver_mut().int_const(idx as i64);
                arr = self.solver_mut().try_store(arr, idx_term, elem_term)?;
            }
        }

        Ok(SeqTerm {
            array: arr,
            len: info.len_term,
        })
    }
}

#[cfg(test)]
mod tests {
    use z4_dpll::api::SolveResult;

    use super::*;

    /// Helper: create a translator with array support and declare a sequence variable.
    fn setup_int_seq(name: &str, max_len: usize) -> Z4Translator {
        let mut trans = Z4Translator::new_with_arrays();
        trans
            .declare_seq_var(name, TlaSort::Int, max_len)
            .expect("declare_seq_var should succeed");
        trans
    }

    fn setup_bool_seq(name: &str, max_len: usize) -> Z4Translator {
        let mut trans = Z4Translator::new_with_arrays();
        trans
            .declare_seq_var(name, TlaSort::Bool, max_len)
            .expect("declare_seq_var should succeed");
        trans
    }

    fn make_int_expr(val: i64) -> Spanned<Expr> {
        Spanned::new(Expr::Int(num_bigint::BigInt::from(val)), Default::default())
    }

    fn make_ident_expr(name: &str) -> Spanned<Expr> {
        Spanned::new(
            Expr::Ident(name.to_string(), tla_core::name_intern::NameId::INVALID),
            Default::default(),
        )
    }

    // -----------------------------------------------------------------
    // s[i] indexing tests
    // -----------------------------------------------------------------

    #[test]
    fn test_seq_apply_int_constant_index() {
        let mut trans = setup_int_seq("s", 3);
        let seq_info = trans.get_seq_var("s").unwrap().clone();
        let arg = make_int_expr(2);
        let result = trans.translate_seq_apply_int("s", &seq_info, &arg);
        assert!(result.is_ok(), "constant index should succeed");
    }

    #[test]
    fn test_seq_apply_int_out_of_bounds() {
        let mut trans = setup_int_seq("s", 3);
        let seq_info = trans.get_seq_var("s").unwrap().clone();
        let arg = make_int_expr(5);
        let result = trans.translate_seq_apply_int("s", &seq_info, &arg);
        assert!(result.is_err(), "index 5 on max_len=3 should fail");
    }

    #[test]
    fn test_seq_apply_int_zero_index() {
        let mut trans = setup_int_seq("s", 3);
        let seq_info = trans.get_seq_var("s").unwrap().clone();
        let arg = make_int_expr(0);
        let result = trans.translate_seq_apply_int("s", &seq_info, &arg);
        assert!(result.is_err(), "index 0 should fail (1-indexed)");
    }

    #[test]
    fn test_seq_apply_bool_type_mismatch() {
        let mut trans = setup_int_seq("s", 3);
        let seq_info = trans.get_seq_var("s").unwrap().clone();
        let arg = make_int_expr(1);
        let result = trans.translate_seq_apply_bool("s", &seq_info, &arg);
        assert!(result.is_err(), "Bool access on Int seq should fail");
    }

    #[test]
    fn test_seq_apply_bool_constant_index() {
        let mut trans = setup_bool_seq("b", 3);
        let seq_info = trans.get_seq_var("b").unwrap().clone();
        let arg = make_int_expr(1);
        let result = trans.translate_seq_apply_bool("b", &seq_info, &arg);
        assert!(result.is_ok(), "Bool access on Bool seq should succeed");
    }

    #[test]
    fn test_seq_apply_int_dynamic_index() {
        let mut trans = setup_int_seq("s", 3);
        // Declare an index variable
        trans.declare_var("idx", TlaSort::Int).expect("declare idx");
        let seq_info = trans.get_seq_var("s").unwrap().clone();
        let arg = make_ident_expr("idx");
        let result = trans.translate_seq_apply_int("s", &seq_info, &arg);
        assert!(result.is_ok(), "dynamic index should build ITE chain");
    }

    // -----------------------------------------------------------------
    // Len tests
    // -----------------------------------------------------------------

    #[test]
    fn test_len_returns_length_term() {
        let mut trans = setup_int_seq("s", 5);
        let seq_expr = make_ident_expr("s");
        let len_term = trans.translate_len(&seq_expr);
        assert!(len_term.is_ok(), "Len(s) should succeed");
    }

    #[test]
    fn test_len_constrained_sat() {
        let mut trans = setup_int_seq("s", 5);
        let seq_expr = make_ident_expr("s");
        let len_term = trans.translate_len(&seq_expr).unwrap();

        // Assert Len(s) = 3
        let three = trans.solver_mut().int_const(3);
        let eq = trans.solver_mut().try_eq(len_term, three).unwrap();
        trans.assert(eq);

        assert_eq!(trans.check_sat(), SolveResult::Sat);
    }

    #[test]
    fn test_len_exceeds_max_unsat() {
        let mut trans = setup_int_seq("s", 5);
        let seq_expr = make_ident_expr("s");
        let len_term = trans.translate_len(&seq_expr).unwrap();

        // Assert Len(s) = 10 (max_len=5, so unsat)
        let ten = trans.solver_mut().int_const(10);
        let eq = trans.solver_mut().try_eq(len_term, ten).unwrap();
        trans.assert(eq);

        assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
    }

    // -----------------------------------------------------------------
    // Head tests
    // -----------------------------------------------------------------

    #[test]
    fn test_head_int() {
        let mut trans = setup_int_seq("s", 3);
        let seq_expr = make_ident_expr("s");
        let head = trans.translate_head_int(&seq_expr);
        assert!(head.is_ok(), "Head(s) for Int seq should succeed");
    }

    #[test]
    fn test_head_bool() {
        let mut trans = setup_bool_seq("b", 3);
        let seq_expr = make_ident_expr("b");
        let head = trans.translate_head_bool(&seq_expr);
        assert!(head.is_ok(), "Head(b) for Bool seq should succeed");
    }

    #[test]
    fn test_head_equals_first_element_sat() {
        let mut trans = setup_int_seq("s", 3);

        // Set s__1 = 42
        let s1 = *trans
            .get_seq_var("s")
            .unwrap()
            .element_terms
            .get(&1)
            .unwrap();
        let forty_two = trans.solver_mut().int_const(42);
        let eq1 = trans.solver_mut().try_eq(s1, forty_two).unwrap();
        trans.assert(eq1);

        // Assert Len(s) >= 1
        let len = trans.get_seq_var("s").unwrap().len_term;
        let one = trans.solver_mut().int_const(1);
        let ge = trans.solver_mut().try_ge(len, one).unwrap();
        trans.assert(ge);

        // Head(s) should equal 42
        let seq_expr = make_ident_expr("s");
        let head = trans.translate_head_int(&seq_expr).unwrap();
        let eq_head = trans.solver_mut().try_eq(head, forty_two).unwrap();
        trans.assert(eq_head);

        assert_eq!(trans.check_sat(), SolveResult::Sat);
    }

    // -----------------------------------------------------------------
    // seq_var_to_seq_term bridge test
    // -----------------------------------------------------------------

    #[test]
    fn test_seq_var_to_seq_term_roundtrip() {
        let mut trans = setup_int_seq("s", 3);
        let info = trans.get_seq_var("s").unwrap().clone();
        let result = trans.seq_var_to_seq_term(&info, &Sort::Int);
        assert!(result.is_ok(), "bridge should succeed");

        let seq = result.unwrap();
        // The length should be the same term
        // The array should be a store chain
        assert_eq!(trans.check_sat(), SolveResult::Sat);

        // Use the encoder to get Head and assert it equals s__1
        let enc = SequenceEncoder::new(Sort::Int);
        let head = enc.encode_head(&mut trans, &seq).unwrap();
        let s1 = info.element_terms.get(&1).copied().unwrap();
        let eq = trans.solver_mut().try_eq(head, s1).unwrap();
        trans.assert(eq);
        assert_eq!(trans.check_sat(), SolveResult::Sat);
    }

    // -----------------------------------------------------------------
    // resolve_seq_term error cases
    // -----------------------------------------------------------------

    #[test]
    fn test_resolve_seq_term_unknown_var() {
        let mut trans = Z4Translator::new_with_arrays();
        let expr = make_ident_expr("nonexistent");
        let result = trans.resolve_seq_term(&expr);
        assert!(result.is_err(), "unknown seq var should fail");
    }

    #[test]
    fn test_resolve_seq_term_non_ident() {
        let mut trans = setup_int_seq("s", 3);
        let expr = make_int_expr(42);
        let result = trans.resolve_seq_term(&expr);
        assert!(result.is_err(), "non-Ident should fail");
    }
}
