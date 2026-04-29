// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! [`TranslateExpr`] trait implementation for [`Z4Translator`].
//!
//! This bridges the shared `dispatch_translate_{bool,int}` arms in `tla_core`
//! to the z4-specific translation methods defined in the parent module and
//! sibling submodules (`membership`, `tuple`, `quantifier`).
//!
//! Compound type encoders (FiniteSetEncoder, FunctionEncoder, RecordEncoder,
//! SequenceEncoder) are wired into the dispatch here so that the Z4Translator
//! automatically routes compound type operations to the appropriate encoder.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::Term;

use tla_core::TranslateExpr;

use crate::error::{Z4Error, Z4Result};

use super::{is_nonlinear_mul, TlaSort, Z4Translator};

impl TranslateExpr for Z4Translator {
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
        let (sort, term) = self.get_var(name)?;
        if sort != TlaSort::Bool {
            return Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Bool".to_string(),
                actual: format!("{sort}"),
            });
        }
        Ok(term)
    }

    fn lookup_int_var(&mut self, name: &str) -> Z4Result<Term> {
        let (sort, term) = self.get_var(name)?;
        if sort != TlaSort::Int {
            return Err(Z4Error::TypeMismatch {
                name: name.to_string(),
                expected: "Int".to_string(),
                actual: format!("{sort}"),
            });
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
        self.solver
            .try_neg(expr)
            .expect("invariant: neg requires Int-sorted term")
    }

    fn div(&mut self, lhs: Term, rhs: Term) -> Z4Result<Term> {
        Ok(self.solver.try_int_div(lhs, rhs)?)
    }

    fn modulo(&mut self, lhs: Term, rhs: Term) -> Z4Result<Term> {
        Ok(self.solver.try_modulo(lhs, rhs)?)
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
        // Z4's 5-way type inference: int, string, bool, tuple, cross-type
        if let (Ok(l), Ok(r)) = (self.translate_int(left), self.translate_int(right)) {
            Ok(self.solver.try_eq(l, r)?)
        } else if let (Ok(l), Ok(r)) = (self.translate_string(left), self.translate_string(right)) {
            Ok(self.solver.try_eq(l, r)?)
        } else if let (Ok(l), Ok(r)) = (self.translate_bool(left), self.translate_bool(right)) {
            let a_and_b = self.solver.try_and(l, r)?;
            let not_l = self.solver.try_not(l)?;
            let not_r = self.solver.try_not(r)?;
            let not_a_and_not_b = self.solver.try_and(not_l, not_r)?;
            Ok(self.solver.try_or(a_and_b, not_a_and_not_b)?)
        } else if let Some(result) = self.try_translate_tuple_equality(left, right)? {
            Ok(result)
        } else if let Some(result) = self.try_translate_record_equality(left, right)? {
            Ok(result)
        } else if let Some(result) = self.try_translate_func_equality(left, right)? {
            Ok(result)
        } else {
            let left_type = self.infer_scalar_type(left);
            let right_type = self.infer_scalar_type(right);
            match (left_type, right_type) {
                (Some(_), Some(_)) => Ok(self.solver.bool_const(false)),
                _ => Err(Z4Error::UntranslatableExpr(
                    "cannot determine type for equality comparison".to_string(),
                )),
            }
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
                    Some(self.translate_quantifier(bounds, &negated_body, true))
                }
                Expr::Forall(bounds, body) => {
                    let negated_body = Spanned::new(Expr::Not(body.clone()), body.span);
                    Some(self.translate_quantifier(bounds, &negated_body, false))
                }
                _ => None,
            },
            Expr::Forall(bounds, body) => Some(self.translate_quantifier(bounds, body, true)),
            Expr::Exists(bounds, body) => Some(self.translate_quantifier(bounds, body, false)),
            Expr::Choose(bound, body) => Some(self.translate_choose_bool(bound, body)),
            Expr::In(elem, set) => Some(self.translate_membership(elem, set)),
            // x \notin S => ~(x \in S)
            Expr::NotIn(elem, set) => Some(
                self.translate_membership(elem, set)
                    .and_then(|t| self.solver.try_not(t).map_err(Z4Error::Solver)),
            ),
            Expr::FuncApply(func, arg) => Some(self.translate_func_apply_bool(func, arg)),
            Expr::ModuleRef(target, op_name, args) => {
                Some(self.translate_module_ref_bool(target, op_name, args))
            }
            // Record field access returning Bool via RecordEncoder
            Expr::RecordAccess(base, field) => {
                Some(self.translate_record_access_bool(base, &field.name.node))
            }
            // S \subseteq T via FiniteSetEncoder
            Expr::Subseteq(left, right) => Some(self.translate_subseteq_bool(left, right)),
            // Record construction [a |-> 1, b |-> 2] via RecordEncoder
            Expr::Record(fields) => Some(self.translate_record_construct_bool(fields)),
            // Function definition [x \in S |-> expr] via FunctionEncoder
            Expr::FuncDef(bounds, body) => Some(self.translate_func_def_bool(bounds, body)),
            // EXCEPT [f EXCEPT ![a] = b] via FunctionEncoder/RecordEncoder
            Expr::Except(base, specs) => Some(self.translate_except_bool(base, specs)),
            // Tuple construction <<e1, ..., en>> via RecordEncoder
            Expr::Tuple(elements) => Some(self.translate_tuple_construct_bool(elements)),
            // Finite set enumeration {e1, ..., en} via FiniteSetEncoder
            // Builds the SMT array set term; returns TRUE to indicate success.
            Expr::SetEnum(elements) => Some(
                self.translate_set_enum_term(elements)
                    .map(|_| self.solver.bool_const(true)),
            ),
            // Set operations via FiniteSetEncoder -- build SMT array terms
            Expr::Union(..) | Expr::Intersect(..) | Expr::SetMinus(..) => Some(
                self.translate_set_expr_term(expr)
                    .map(|_| self.solver.bool_const(true)),
            ),
            // DOMAIN f -- set-valued; handled as Bool constraint
            Expr::Domain(func_expr) => Some(self.translate_domain_bool(func_expr)),
            // Sequence operations returning Bool (e.g., Head of Bool sequence)
            Expr::Apply(op, args) => self.try_translate_seq_op_bool(op, args),
            _ => None,
        }
    }

    fn translate_int_extended(&mut self, expr: &Spanned<Expr>) -> Option<Z4Result<Term>> {
        match &expr.node {
            Expr::Mul(left, right) => {
                // Part of #771: reject non-linear multiplication under QF_LIA
                if is_nonlinear_mul(left, right) {
                    return Some(Err(Z4Error::UnsupportedOp(
                        "Non-linear integer multiplication (x * y) is not supported by z4 yet"
                            .to_string(),
                    )));
                }
                // Linear multiplication: let dispatch handle via trait's mul()
                None
            }
            Expr::IntDiv(left, right) => Some(self.translate_int_div_floor(left, right)),
            Expr::Mod(left, right) => Some(self.translate_int_mod_floor(left, right)),
            Expr::FuncApply(func, arg) => Some(self.translate_func_apply_int(func, arg)),
            // CHOOSE x \in S : P(x) returning Int
            Expr::Choose(bound, body) => Some(self.translate_choose_int(bound, body)),
            // Record field access returning Int via RecordEncoder
            Expr::RecordAccess(base, field) => {
                Some(self.translate_record_access_int(base, &field.name.node))
            }
            // Operator applications returning Int:
            // - Cardinality(S) via FiniteSetEncoder
            // - Len(s), Head(s) via SequenceEncoder
            Expr::Apply(op, args) => {
                // Cardinality via FiniteSetEncoder
                if let Expr::Ident(name, _) = &op.node {
                    if name == "Cardinality" && args.len() == 1 {
                        return Some(self.translate_cardinality_int(&args[0]));
                    }
                }
                // Sequence operations (Len, Head returning Int)
                self.try_translate_seq_op_int(op, args)
            }
            _ => None,
        }
    }
}

impl Default for Z4Translator {
    fn default() -> Self {
        Self::new()
    }
}
