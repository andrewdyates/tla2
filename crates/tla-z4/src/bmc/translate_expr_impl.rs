// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`TranslateExpr`] trait implementation for [`BmcTranslator`].
//!
//! This bridges the shared `dispatch_translate_{bool,int}` arms in `tla_core`
//! to the BMC-specific translation methods in the parent module.
//!
//! Compound type encoders (set operations, function EXCEPT/DOMAIN, function
//! construction, sequence ops, and Cardinality) are wired into the dispatch so
//! that the BmcTranslator automatically routes compound type operations to the
//! appropriate encoder. Part of #3778.

use tla_core::ast::Expr;
use tla_core::{dispatch_translate_bool, dispatch_translate_int, Spanned, TranslateExpr};
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::compound_dispatch::SetBinOp;
use super::BmcTranslator;
use crate::TlaSort;

impl TranslateExpr for BmcTranslator {
    type Bool = Term;
    type Int = Term;
    type Error = Z4Error;

    fn bool_const(&mut self, val: bool) -> Term {
        self.solver.bool_const(val)
    }

    fn int_const(&mut self, val: i64) -> Z4Result<Term> {
        Ok(self.solver.int_const(val))
    }

    fn lookup_bool_var(&mut self, name: &str) -> Z4Result<Term> {
        let term = self.get_var_at_step(name, self.current_step)?;
        if let Some(info) = self.vars.get(name) {
            if info.sort != TlaSort::Bool {
                return Err(Z4Error::TypeMismatch {
                    name: name.to_string(),
                    expected: "Bool".to_string(),
                    actual: format!("{}", info.sort),
                });
            }
        }
        Ok(term)
    }

    fn lookup_int_var(&mut self, name: &str) -> Z4Result<Term> {
        let term = self.get_var_at_step(name, self.current_step)?;
        if let Some(info) = self.vars.get(name) {
            if info.sort != TlaSort::Int {
                return Err(Z4Error::TypeMismatch {
                    name: name.to_string(),
                    expected: "Int".to_string(),
                    actual: format!("{}", info.sort),
                });
            }
        }
        Ok(term)
    }

    fn and(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_and(lhs, rhs)
            .expect("invariant: and requires Bool-sorted terms")
    }

    fn or(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_or(lhs, rhs)
            .expect("invariant: or requires Bool-sorted terms")
    }

    fn not(&mut self, expr: Term) -> Term {
        self.solver
            .try_not(expr)
            .expect("invariant: not requires Bool-sorted term")
    }

    fn implies(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_implies(lhs, rhs)
            .expect("invariant: implies requires Bool-sorted terms")
    }

    // iff() uses default from TranslateExpr: (a => b) /\ (b => a)

    fn lt(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_lt(lhs, rhs)
            .expect("invariant: lt requires Int-sorted terms")
    }

    fn le(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_le(lhs, rhs)
            .expect("invariant: le requires Int-sorted terms")
    }

    fn gt(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_gt(lhs, rhs)
            .expect("invariant: gt requires Int-sorted terms")
    }

    fn ge(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_ge(lhs, rhs)
            .expect("invariant: ge requires Int-sorted terms")
    }

    fn add(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_add(lhs, rhs)
            .expect("invariant: add requires Int-sorted terms")
    }

    fn sub(&mut self, lhs: Term, rhs: Term) -> Term {
        self.solver
            .try_sub(lhs, rhs)
            .expect("invariant: sub requires Int-sorted terms")
    }

    fn mul(&mut self, lhs: Term, rhs: Term) -> Z4Result<Term> {
        Ok(self.solver.try_mul(lhs, rhs)?)
    }

    fn neg(&mut self, expr: Term) -> Term {
        // BMC uses 0 - x for negation (QF_LIA compatible)
        let zero = self.solver.int_const(0);
        self.solver
            .try_sub(zero, expr)
            .expect("invariant: sub requires Int-sorted terms")
    }

    fn div(&mut self, _lhs: Term, _rhs: Term) -> Z4Result<Term> {
        // BMC handles div via translate_int_extended (needs AST-level access
        // to check for constant divisors and do QF_LIA linearization).
        // This path should not be reached -- the extended hook intercepts first.
        Err(Z4Error::UntranslatableExpr(
            "BMC div requires constant divisor (handled by extension hook)".to_string(),
        ))
    }

    fn modulo(&mut self, _lhs: Term, _rhs: Term) -> Z4Result<Term> {
        // Same as div -- BMC needs AST-level access for linearization.
        Err(Z4Error::UntranslatableExpr(
            "BMC modulo requires constant divisor (handled by extension hook)".to_string(),
        ))
    }

    fn ite_bool(&mut self, cond: Term, then_b: Term, else_b: Term) -> Term {
        self.solver
            .try_ite(cond, then_b, else_b)
            .expect("invariant: ite requires Bool cond, matching then/else sorts")
    }

    fn ite_int(&mut self, cond: Term, then_i: Term, else_i: Term) -> Term {
        self.solver
            .try_ite(cond, then_i, else_i)
            .expect("invariant: ite requires Bool cond, matching then/else sorts")
    }

    fn translate_eq(&mut self, left: &Spanned<Expr>, right: &Spanned<Expr>) -> Z4Result<Term> {
        // Check for function EXCEPT equality: f' = [f EXCEPT ![a] = b]
        if let Some(result) = self.try_translate_func_except_eq(left, right) {
            return result;
        }

        // Check for function construction equality: f = [x \in S |-> e(x)]
        // Part of #3786: Function encoding in BMC translator.
        if let Some(result) = self.try_translate_func_construct_eq(left, right) {
            return result;
        }

        // Check for function variable equality: f = g (both function variables)
        // Part of #3778: Apalache parity — function equality in BMC.
        if let Some(result) = self.try_translate_func_equality(left, right) {
            return result;
        }

        // Check for record equality (Part of #3787)
        // Pattern: r' = [r EXCEPT !.a = v], r' = [a |-> e1, ...], r = r'
        if let Some(result) = self.try_translate_record_except_eq(left, right) {
            return result;
        }
        if let Some(result) = self.try_translate_record_eq(left, right) {
            return result;
        }

        // Check for tuple equality (Part of #3787)
        // Pattern: t' = <<e1, e2>>, t = t'
        if let Some(result) = self.try_translate_tuple_eq(left, right) {
            return result;
        }

        // Check for sequence equality (Part of #3793)
        // Pattern: s' = Tail(s), s' = Append(s, e), s = s'
        if let Some(result) = self.try_translate_seq_eq(left, right) {
            return result;
        }

        // Check for set equality (Part of #3826): S = T where both sides
        // are set-typed expressions (SetEnum, set variable, etc.).
        // Pointwise: \A u \in universe : (select S u) = (select T u).
        if let Some(result) = self.try_translate_set_eq(left, right) {
            return result;
        }

        // Try integer equality first, then bool
        if let (Ok(l), Ok(r)) = (
            dispatch_translate_int(self, left),
            dispatch_translate_int(self, right),
        ) {
            Ok(self.solver.try_eq(l, r)?)
        } else {
            let l = dispatch_translate_bool(self, left)?;
            let r = dispatch_translate_bool(self, right)?;
            // Bool equality: (a /\ b) \/ (~a /\ ~b)
            let a_and_b = self.solver.try_and(l, r)?;
            let not_l = self.solver.try_not(l)?;
            let not_r = self.solver.try_not(r)?;
            let not_a_and_not_b = self.solver.try_and(not_l, not_r)?;
            Ok(self.solver.try_or(a_and_b, not_a_and_not_b)?)
        }
    }

    fn translate_bool_extended(&mut self, expr: &Spanned<Expr>) -> Option<Z4Result<Term>> {
        match &expr.node {
            // Fix #3822: Rewrite negated quantifiers to avoid unsound Skolemization.
            // ~(\E x \in S : P(x)) == \A x \in S : ~P(x)
            // ~(\A x \in S : P(x)) == \E x \in S : ~P(x)
            Expr::Not(inner) => match &inner.node {
                Expr::Exists(bounds, body) => {
                    let negated_body = Spanned::new(Expr::Not(body.clone()), body.span);
                    Some(self.translate_bmc_quantifier(bounds, &negated_body, true))
                }
                Expr::Forall(bounds, body) => {
                    let negated_body = Spanned::new(Expr::Not(body.clone()), body.span);
                    Some(self.translate_bmc_quantifier(bounds, &negated_body, false))
                }
                _ => None,
            },
            // Quantifiers: \A x \in S : P(x), \E x \in S : P(x)
            Expr::Forall(bounds, body) => Some(self.translate_bmc_quantifier(bounds, body, true)),
            Expr::Exists(bounds, body) => Some(self.translate_bmc_quantifier(bounds, body, false)),
            Expr::Prime(inner) => {
                // Primed variable: use next step
                match &inner.node {
                    Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                        Some(self.get_var_at_step(name, self.current_step + 1))
                    }
                    _ => {
                        // Complex primed expression: temporarily shift step
                        let old_step = self.current_step;
                        self.current_step += 1;
                        let result = dispatch_translate_bool(self, inner);
                        self.current_step = old_step;
                        Some(result)
                    }
                }
            }
            Expr::In(elem, set) => Some(self.translate_membership(elem, set)),
            // x \notin S => ~(x \in S)
            Expr::NotIn(elem, set) => Some(
                self.translate_membership(elem, set)
                    .and_then(|t| self.solver.try_not(t).map_err(Z4Error::Solver)),
            ),
            // CHOOSE x \in S : P(x) — Skolemized, returns Int, wrap for Bool context
            Expr::Choose(bound, body) => {
                Some(self.translate_choose_bmc(bound, body).and_then(|int_term| {
                    // In Bool context, CHOOSE result is truthy if non-zero.
                    // This handles CHOOSE x \in BOOLEAN : P(x) where result
                    // is 0 or 1 (Bool-as-Int). Compare: ~(sk = 0).
                    let zero = self.solver.int_const(0);
                    let eq_zero = self.solver.try_eq(int_term, zero)?;
                    self.solver.try_not(eq_zero).map_err(Z4Error::Solver)
                }))
            }
            Expr::Unchanged(inner) => Some(self.translate_unchanged_expr(inner)),
            // --- Compound type dispatch (Part of #3778) ---

            // S \subseteq T: extract universe from both operands, then expand
            // pointwise \A u \in universe : (select S u) => (select T u).
            Expr::Subseteq(left, right) => Some(self.translate_subseteq_dispatch(left, right)),

            // Set enumeration {e1, ..., en}: build SMT array, return TRUE.
            Expr::SetEnum(elements) => Some(self.translate_set_enum_bool(elements)),

            // Set operations (Union, Intersect, SetMinus): build SMT array
            // terms with extracted universe, return TRUE.
            Expr::Union(left, right) => {
                Some(self.translate_set_binop_bool(left, right, SetBinOp::Union))
            }
            Expr::Intersect(left, right) => {
                Some(self.translate_set_binop_bool(left, right, SetBinOp::Intersect))
            }
            Expr::SetMinus(left, right) => {
                Some(self.translate_set_binop_bool(left, right, SetBinOp::Minus))
            }

            // SUBSET S: powerset (set of all subsets).
            // For small base sets, enumerates subsets; in Bool context,
            // returns TRUE after ensuring the base is translatable.
            Expr::Powerset(base) => Some(self.translate_powerset_bool(base)),

            // UNION S: big union of a set-of-sets (flattening).
            // Part of #3778: Apalache parity — BigUnion in BMC.
            Expr::BigUnion(inner) => Some(self.translate_big_union_bool(inner)),

            // a..b as a set expression in Bool context.
            // Part of #3778: Apalache parity — Range-as-set in BMC.
            Expr::Range(lo, hi) => {
                // translate_range_set_term builds the array; in Bool context
                // we just need to ensure it's constructed, then return TRUE.
                Some(
                    self.translate_range_set_term(lo, hi)
                        .map(|_arr| self.solver.bool_const(true)),
                )
            }

            // DOMAIN f: set-valued expression. In Bool context, return
            // an error with guidance to use membership tests instead.
            Expr::Domain(func_expr) => Some(self.translate_domain_bool_dispatch(func_expr)),

            // [f EXCEPT ![a] = b]: function or record update.
            Expr::Except(base, specs) => Some(self.translate_except_bool_dispatch(base, specs)),

            // [x \in S |-> expr]: function construction.
            Expr::FuncDef(bounds, body) => {
                Some(self.translate_func_def_bool_dispatch(bounds, body))
            }
            // Function application with Bool result via FunctionEncoder
            Expr::FuncApply(func, arg) => {
                // Try as function variable first
                if self.is_func_var_expr(func) {
                    Some(self.translate_func_apply_bmc(func, arg))
                } else if self.is_seq_var_expr(func) {
                    // Sequence indexing: s[i] returning Bool
                    // For Bool-valued sequences (uncommon), route through Int
                    // and let the solver sort-check.
                    Some(self.translate_seq_index_bmc(func, arg))
                } else if self.is_tuple_var_expr(func) {
                    // Tuple indexing: t[i] returning Bool (Part of #3787)
                    Some(self.translate_tuple_index(func, arg))
                } else {
                    None
                }
            }
            // Sequence operations returning Bool (e.g., Head of Bool seq)
            Expr::Apply(op, args) => self.translate_seq_bool_op(op, args),
            // Record construction: [a |-> e1, b |-> e2] (Part of #3787)
            Expr::Record(fields) => Some(self.translate_record_construct(fields)),
            // Record field access on a record variable (Part of #3787)
            Expr::RecordAccess(record_expr, field_name) if self.is_record_var_expr(record_expr) => {
                Some(self.translate_record_access(record_expr, &field_name.name.node))
            }
            _ => None,
        }
    }

    fn translate_int_extended(&mut self, expr: &Spanned<Expr>) -> Option<Z4Result<Term>> {
        match &expr.node {
            // CHOOSE x \in S : P(x) — Skolemized, returns Int term
            Expr::Choose(bound, body) => Some(self.translate_choose_bmc(bound, body)),
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    Some(self.get_var_at_step(name, self.current_step + 1))
                }
                _ => {
                    let old_step = self.current_step;
                    self.current_step += 1;
                    let result = dispatch_translate_int(self, inner);
                    self.current_step = old_step;
                    Some(result)
                }
            },
            Expr::Mul(left, right) => {
                // Part of #771: reject non-linear multiplication under QF_LIA
                if crate::translate::is_nonlinear_mul(left, right) {
                    return Some(Err(Z4Error::UnsupportedOp(
                        "BMC cannot translate non-linear integer multiplication (x * y) under QF_LIA"
                            .to_string(),
                    )));
                }
                // Linear multiplication: let shared dispatch handle via trait's mul()
                None
            }
            Expr::IntDiv(left, right) => Some(self.translate_int_div_bmc(left, right)),
            Expr::Mod(left, right) => Some(self.translate_mod_bmc(left, right)),
            // Function application with Int result via FunctionEncoder
            Expr::FuncApply(func, arg) => {
                if self.is_func_var_expr(func) {
                    Some(self.translate_func_apply_bmc(func, arg))
                } else if self.is_seq_var_expr(func) {
                    // Sequence indexing: s[i] -> (select arr i)
                    Some(self.translate_seq_index_bmc(func, arg))
                } else if self.is_tuple_var_expr(func) {
                    // Tuple indexing: t[i] -> element variable (Part of #3787)
                    Some(self.translate_tuple_index(func, arg))
                } else {
                    None
                }
            }
            // Operator applications returning Int: Cardinality, Len, Head
            Expr::Apply(op, args) => {
                // Cardinality(S) via set encoding (Part of #3778)
                if let Expr::Ident(name, _) = &op.node {
                    if name == "Cardinality" && args.len() == 1 {
                        return Some(self.translate_cardinality_int_dispatch(&args[0]));
                    }
                }
                // Sequence operations (Len, Head returning Int)
                self.translate_seq_int_op(op, args)
            }
            _ => None,
        }
    }
}

impl BmcTranslator {
    /// Translate sequence indexing: `s[i]` -> `(select arr i)`.
    fn translate_seq_index_bmc(
        &mut self,
        seq_expr: &Spanned<Expr>,
        index_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (name, step) = self.resolve_seq_var(seq_expr)?;
        let arr = self.get_seq_array_at_step(&name, step)?;
        let idx = dispatch_translate_int(self, index_expr)?;
        Ok(self.solver.try_select(arr, idx)?)
    }

    /// Try to translate a sequence operation that returns Int.
    ///
    /// Handles:
    /// - `Len(s)` -> length term
    /// - `Head(s)` -> `(select arr 1)`
    ///
    /// Returns `None` if the Apply is not a known sequence operation.
    fn translate_seq_int_op(
        &mut self,
        op: &Spanned<Expr>,
        args: &[Spanned<Expr>],
    ) -> Option<Z4Result<Term>> {
        let op_name = match &op.node {
            Expr::Ident(name, _) => name.as_str(),
            _ => return None,
        };

        match op_name {
            "Len" if args.len() == 1 => {
                if self.is_seq_var_expr(&args[0]) {
                    Some(self.translate_seq_len_bmc(&args[0]))
                } else {
                    None
                }
            }
            "Head" if args.len() == 1 => {
                if self.is_seq_var_expr(&args[0]) {
                    Some(self.translate_seq_head_bmc(&args[0]))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Try to translate a sequence operation that returns Bool.
    ///
    /// Currently no sequence operations return Bool in BMC context,
    /// but this provides the extension point for future operations.
    ///
    /// Returns `None` if the Apply is not a known Bool sequence operation.
    fn translate_seq_bool_op(
        &mut self,
        op: &Spanned<Expr>,
        args: &[Spanned<Expr>],
    ) -> Option<Z4Result<Term>> {
        let op_name = match &op.node {
            Expr::Ident(name, _) => name.as_str(),
            _ => return None,
        };

        // Head of a Bool-valued sequence would go here; for now
        // Bool sequence ops are uncommon in BMC context.
        match op_name {
            "Head" if args.len() == 1 && self.is_seq_var_expr(&args[0]) => {
                // Head returns the element at index 1; works for any element sort
                Some(self.translate_seq_head_bmc(&args[0]))
            }
            _ => None,
        }
    }

    /// Try to translate sequence equality: `s' = Tail(s)`, `s' = Append(s, e)`,
    /// or `s = s'` where at least one side is a sequence-valued expression.
    ///
    /// Returns `None` if neither side involves a sequence variable.
    /// Returns `Some(result)` if sequence equality is detected.
    fn try_translate_seq_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // Try both directions: left = right, right = left
        if let Some(result) = self.try_translate_seq_eq_directed(left, right) {
            return Some(result);
        }
        self.try_translate_seq_eq_directed(right, left)
    }

    /// Try sequence equality in one direction: lhs is a seq variable,
    /// rhs is a seq operation or seq variable.
    fn try_translate_seq_eq_directed(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // lhs must be a (possibly primed) sequence variable
        if !self.is_seq_var_expr(lhs) {
            return None;
        }

        let lhs_resolved = match self.resolve_seq_var(lhs) {
            Ok(r) => r,
            Err(e) => return Some(Err(e)),
        };

        // rhs can be: another seq variable, Tail(s), Append(s, e), or <<e1,...,en>>
        if self.is_seq_var_expr(rhs) {
            // seq = seq
            let rhs_resolved = match self.resolve_seq_var(rhs) {
                Ok(r) => r,
                Err(e) => return Some(Err(e)),
            };
            return Some(self.assert_seq_eq_vars(&lhs_resolved, &rhs_resolved));
        }

        // Check for Apply(op, args) patterns: Tail, Append
        if let Expr::Apply(op, args) = &rhs.node {
            if let Expr::Ident(op_name, _) = &op.node {
                match op_name.as_str() {
                    "Tail" if args.len() == 1 && self.is_seq_var_expr(&args[0]) => {
                        return Some(self.translate_seq_eq_tail(&lhs_resolved, &args[0]));
                    }
                    "Append" if args.len() == 2 && self.is_seq_var_expr(&args[0]) => {
                        return Some(self.translate_seq_eq_append(
                            &lhs_resolved,
                            &args[0],
                            &args[1],
                        ));
                    }
                    "SubSeq" if args.len() == 3 && self.is_seq_var_expr(&args[0]) => {
                        return Some(self.translate_seq_eq_subseq(
                            &lhs_resolved,
                            &args[0],
                            &args[1],
                            &args[2],
                        ));
                    }
                    "\\o"
                        if args.len() == 2
                            && self.is_seq_var_expr(&args[0])
                            && self.is_seq_var_expr(&args[1]) =>
                    {
                        return Some(self.translate_seq_eq_concat(
                            &lhs_resolved,
                            &args[0],
                            &args[1],
                        ));
                    }
                    _ => {}
                }
            }
        }

        // Check for Tuple (sequence literal): s = <<e1, e2, ...>>
        if let Expr::Tuple(elems) = &rhs.node {
            return Some(self.translate_seq_eq_literal(&lhs_resolved, elems));
        }

        None
    }

    /// Assert equality between two sequence variables: arr_l = arr_r /\ len_l = len_r
    fn assert_seq_eq_vars(
        &mut self,
        lhs: &(String, usize),
        rhs: &(String, usize),
    ) -> Z4Result<Term> {
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;
        let r_arr = self.get_seq_array_at_step(&rhs.0, rhs.1)?;
        let r_len = self.get_seq_length_at_step(&rhs.0, rhs.1)?;

        let arr_eq = self.solver.try_eq(l_arr, r_arr)?;
        let len_eq = self.solver.try_eq(l_len, r_len)?;
        Ok(self.solver.try_and(arr_eq, len_eq)?)
    }

    /// Translate `lhs = Tail(s)`: lhs_arr = tail_arr, lhs_len = len - 1
    fn translate_seq_eq_tail(
        &mut self,
        lhs: &(String, usize),
        seq_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (tail_arr, tail_len) = self.translate_seq_tail_bmc(seq_expr)?;
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;

        let arr_eq = self.solver.try_eq(l_arr, tail_arr)?;
        let len_eq = self.solver.try_eq(l_len, tail_len)?;
        Ok(self.solver.try_and(arr_eq, len_eq)?)
    }

    /// Translate `lhs = Append(s, e)`: lhs_arr = (store arr (len+1) e), lhs_len = len + 1
    fn translate_seq_eq_append(
        &mut self,
        lhs: &(String, usize),
        seq_expr: &Spanned<Expr>,
        elem_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (append_arr, append_len) = self.translate_seq_append_bmc(seq_expr, elem_expr)?;
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;

        let arr_eq = self.solver.try_eq(l_arr, append_arr)?;
        let len_eq = self.solver.try_eq(l_len, append_len)?;
        Ok(self.solver.try_and(arr_eq, len_eq)?)
    }

    /// Translate `lhs = SubSeq(s, m, n)`: lhs_arr = subseq_arr, lhs_len = max(0, n-m+1)
    fn translate_seq_eq_subseq(
        &mut self,
        lhs: &(String, usize),
        seq_expr: &Spanned<Expr>,
        m_expr: &Spanned<Expr>,
        n_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (subseq_arr, subseq_len) = self.translate_seq_subseq_bmc(seq_expr, m_expr, n_expr)?;
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;

        let arr_eq = self.solver.try_eq(l_arr, subseq_arr)?;
        let len_eq = self.solver.try_eq(l_len, subseq_len)?;
        Ok(self.solver.try_and(arr_eq, len_eq)?)
    }

    /// Translate `lhs = s \o t`: lhs_arr = concat_arr, lhs_len = len_s + len_t
    fn translate_seq_eq_concat(
        &mut self,
        lhs: &(String, usize),
        s_expr: &Spanned<Expr>,
        t_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (concat_arr, concat_len) = self.translate_seq_concat_bmc(s_expr, t_expr)?;
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;

        let arr_eq = self.solver.try_eq(l_arr, concat_arr)?;
        let len_eq = self.solver.try_eq(l_len, concat_len)?;
        Ok(self.solver.try_and(arr_eq, len_eq)?)
    }

    /// Translate `lhs = <<e1, e2, ...>>`: set length and elements
    fn translate_seq_eq_literal(
        &mut self,
        lhs: &(String, usize),
        elements: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        let l_arr = self.get_seq_array_at_step(&lhs.0, lhs.1)?;
        let l_len = self.get_seq_length_at_step(&lhs.0, lhs.1)?;

        // Assert length
        let len_val = self.solver.int_const(elements.len() as i64);
        let len_eq = self.solver.try_eq(l_len, len_val)?;

        // Assert each element: (select arr i) = ei
        let mut conjuncts = vec![len_eq];
        for (i, elem) in elements.iter().enumerate() {
            let idx = self.solver.int_const((i + 1) as i64);
            let elem_term = dispatch_translate_int(self, elem)?;
            let selected = self.solver.try_select(l_arr, idx)?;
            let eq = self.solver.try_eq(selected, elem_term)?;
            conjuncts.push(eq);
        }

        // Build conjunction
        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = self.solver.try_and(result, c)?;
        }
        Ok(result)
    }

    /// Check whether an expression refers to a declared function variable.
    ///
    /// Used by `translate_{bool,int}_extended` to decide whether
    /// to handle `FuncApply` or defer to the shared dispatch.
    fn is_func_var_expr(&self, expr: &Spanned<Expr>) -> bool {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => self.func_vars.contains_key(name),
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    self.func_vars.contains_key(name)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Try to translate function EXCEPT equality.
    ///
    /// Handles patterns like:
    /// - `f' = [f EXCEPT ![a] = b]`
    /// - `[f EXCEPT ![a] = b] = f'`
    /// - `f' = [f EXCEPT ![a] = b, ![c] = d]`
    /// - `f' = [f EXCEPT ![a][b] = c]`
    ///
    /// The EXCEPT produces a new mapping array via `(store ...)`. This
    /// method asserts that the target function variable's mapping equals
    /// the store result, and that the domain is preserved.
    ///
    /// Returns `None` if neither side involves a function EXCEPT.
    fn try_translate_func_except_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // Try left = EXCEPT, right = func var (or vice versa)
        if let Some(result) = self.try_translate_func_except_eq_directed(left, right) {
            return Some(result);
        }
        self.try_translate_func_except_eq_directed(right, left)
    }

    /// Try function EXCEPT equality in one direction:
    /// lhs is a (possibly primed) function variable, rhs is an EXCEPT expression.
    fn try_translate_func_except_eq_directed(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // rhs must be Except(base, specs) with a function variable base
        let (base, specs) = match &rhs.node {
            Expr::Except(base, specs) if self.is_func_var_expr(base) => {
                (base.as_ref(), specs.as_slice())
            }
            _ => return None,
        };

        // lhs must be a (possibly primed) function variable
        if !self.is_func_var_expr(lhs) {
            return None;
        }

        // Resolve the target mapping (lhs)
        let target_mapping = match self.resolve_func_mapping(lhs) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        // Build the EXCEPT result mapping (rhs)
        let except_mapping = match self.translate_func_except_bmc(base, specs) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        // Assert mapping equality: target_map = except_map
        let map_eq = match self.solver.try_eq(target_mapping, except_mapping) {
            Ok(t) => t,
            Err(e) => return Some(Err(Z4Error::Solver(e))),
        };

        // Also assert domain preservation: target_dom = source_dom
        let dom_eq = match self.assert_domain_preserved(lhs, base) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        Some(self.solver.try_and(map_eq, dom_eq).map_err(Z4Error::Solver))
    }

    /// Try to translate function construction equality.
    ///
    /// Handles patterns like:
    /// - `f = [x \in S |-> e(x)]`
    /// - `f' = [x \in S |-> e(x)]`
    /// - `[x \in S |-> e(x)] = f`
    ///
    /// The FuncDef produces a (domain, mapping) pair via
    /// `translate_func_construct_bmc`. This method asserts that the target
    /// function variable's domain and mapping equal the construction results.
    ///
    /// Returns `None` if neither side involves a function construction.
    ///
    /// Part of #3786: Function encoding in BMC translator.
    fn try_translate_func_construct_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        if let Some(result) = self.try_translate_func_construct_eq_directed(left, right) {
            return Some(result);
        }
        self.try_translate_func_construct_eq_directed(right, left)
    }

    /// Try function construction equality in one direction:
    /// lhs is a (possibly primed) function variable, rhs is a FuncDef expression.
    ///
    /// Part of #3786.
    fn try_translate_func_construct_eq_directed(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // rhs must be FuncDef(bounds, body)
        let (bounds, body) = match &rhs.node {
            Expr::FuncDef(bounds, body) => (bounds.as_slice(), body.as_ref()),
            _ => return None,
        };

        // lhs must be a (possibly primed) function variable
        if !self.is_func_var_expr(lhs) {
            return None;
        }

        // Resolve the target mapping and domain (lhs)
        let target_mapping = match self.resolve_func_mapping(lhs) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        let target_domain = match self.resolve_func_domain(lhs) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        // Build the construction (domain, mapping) pair (rhs)
        let (construct_domain, construct_mapping) =
            match self.translate_func_construct_bmc(bounds, body) {
                Ok(pair) => pair,
                Err(e) => return Some(Err(e)),
            };

        // Assert mapping equality: target_map = construct_map
        let map_eq = match self.solver.try_eq(target_mapping, construct_mapping) {
            Ok(t) => t,
            Err(e) => return Some(Err(Z4Error::Solver(e))),
        };

        // Assert domain equality: target_dom = construct_dom
        let dom_eq = match self.solver.try_eq(target_domain, construct_domain) {
            Ok(t) => t,
            Err(e) => return Some(Err(Z4Error::Solver(e))),
        };

        Some(self.solver.try_and(map_eq, dom_eq).map_err(Z4Error::Solver))
    }

    /// Assert that two function variables have the same domain.
    ///
    /// Used when translating EXCEPT equality: the domain of f' must
    /// equal the domain of f (EXCEPT does not change the domain).
    fn assert_domain_preserved(
        &mut self,
        target: &Spanned<Expr>,
        source: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let target_dom = self.resolve_func_domain(target)?;
        let source_dom = self.resolve_func_domain(source)?;
        Ok(self.solver.try_eq(target_dom, source_dom)?)
    }

    /// Resolve the domain array for a function expression.
    fn resolve_func_domain(&self, expr: &Spanned<Expr>) -> Z4Result<Term> {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                self.get_func_domain_at_step(name, self.current_step)
            }
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    self.get_func_domain_at_step(name, self.current_step + 1)
                }
                _ => Err(Z4Error::UntranslatableExpr(
                    "BMC domain resolution requires function variable".to_string(),
                )),
            },
            _ => Err(Z4Error::UntranslatableExpr(
                "BMC domain resolution requires function variable".to_string(),
            )),
        }
    }

    // Compound type dispatch helpers (subseteq, set enum, set binop, domain,
    // except, func def, cardinality, universe extraction) are in
    // compound_dispatch.rs — Part of #3778.
}
