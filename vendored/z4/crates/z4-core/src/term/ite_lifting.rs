// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE lifting (Shannon expansion) for TermStore.
//!
//! Transforms: `(<= (ite c a b) x)` → `(ite c (<= a x) (<= b x))`
//! This allows theory solvers to handle arithmetic atoms without ITE expressions.

use super::*;

#[derive(Default)]
struct IteLiftCtx {
    recursive_rewritten: KaniHashMap<TermId, TermId>,
    arith_rewritten: KaniHashMap<TermId, TermId>,
    contains_liftable_ite: KaniHashMap<TermId, bool>,
}

impl TermStore {
    /// Lift ITE expressions out of arithmetic predicates.
    ///
    /// Transforms: `(<= (ite c a b) x)` → `(ite c (<= a x) (<= b x))`
    ///
    /// This allows the LRA/LIA theory solvers to handle the arithmetic atoms
    /// without needing to reason about ITE expressions directly.
    pub fn lift_arithmetic_ite(&mut self, term: TermId) -> TermId {
        let mut ctx = IteLiftCtx::default();
        self.lift_ite_recursive_with_ctx(term, &mut ctx)
    }

    /// Recursively lift ITEs from a term.
    fn lift_ite_recursive_with_ctx(&mut self, term: TermId, ctx: &mut IteLiftCtx) -> TermId {
        if let Some(&cached) = ctx.recursive_rewritten.get(&term) {
            return cached;
        }
        if !self.contains_liftable_ite(term, ctx) {
            ctx.recursive_rewritten.insert(term, term);
            return term;
        }

        let lifted = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,

            TermData::Not(inner) => {
                let lifted = self.lift_ite_recursive_with_ctx(inner, ctx);
                if lifted == inner {
                    term
                } else {
                    self.mk_not(lifted)
                }
            }

            TermData::Ite(cond, then_t, else_t) => {
                let lifted_cond = self.lift_ite_recursive_with_ctx(cond, ctx);
                let lifted_then = self.lift_ite_recursive_with_ctx(then_t, ctx);
                let lifted_else = self.lift_ite_recursive_with_ctx(else_t, ctx);
                if lifted_cond == cond && lifted_then == then_t && lifted_else == else_t {
                    term
                } else {
                    self.mk_ite(lifted_cond, lifted_then, lifted_else)
                }
            }

            TermData::App(Symbol::Named(ref name), ref args) => {
                // Arithmetic predicates: Shannon-expand ITE in arguments (#5081).
                let is_pred = matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=" | "distinct");
                if is_pred && args.len() == 2 {
                    let arg0 = self.lift_ite_recursive_with_ctx(args[0], ctx);
                    let arg1 = self.lift_ite_recursive_with_ctx(args[1], ctx);
                    self.lift_ite_from_predicate_with_ctx(&name.clone(), arg0, arg1, ctx)
                } else if matches!(name.as_str(), "and" | "or" | "xor" | "=>") {
                    let lifted: Vec<TermId> = args
                        .iter()
                        .map(|&a| self.lift_ite_recursive_with_ctx(a, ctx))
                        .collect();
                    if lifted.iter().zip(args.iter()).any(|(&a, &b)| a != b) {
                        self.mk_app(Symbol::Named(name.clone()), lifted, Sort::Bool)
                    } else {
                        term
                    }
                } else if matches!(
                    name.as_str(),
                    "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int"
                ) {
                    term // Arithmetic ops handled by lift_ite_from_arith.
                } else {
                    // DT/UF functions: lift non-Bool ITE (#5082).
                    self.lift_non_bool_ite_from_app_with_ctx(
                        term,
                        Symbol::Named(name.clone()),
                        args,
                        ctx,
                    )
                }
            }

            TermData::App(Symbol::Indexed(ref base, ref indices), ref args) => {
                let sym = Symbol::Indexed(base.clone(), indices.clone());
                self.lift_non_bool_ite_from_app_with_ctx(term, sym, args, ctx)
            }

            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => term,
        };

        ctx.recursive_rewritten.insert(term, lifted);
        lifted
    }

    /// Shannon expansion for non-Bool ITE arguments of non-arithmetic applications.
    ///
    /// Transforms: `f(..., ite(c,A,B), ...)` → `ite(c, f(...,A,...), f(...,B,...))`
    /// Used for DT selectors/testers and UF applications (#5082).
    fn lift_non_bool_ite_from_app_with_ctx(
        &mut self,
        term: TermId,
        sym: Symbol,
        args: &[TermId],
        ctx: &mut IteLiftCtx,
    ) -> TermId {
        let lifted_args: Vec<TermId> = args
            .iter()
            .map(|&a| self.lift_ite_recursive_with_ctx(a, ctx))
            .collect();

        for (i, &arg) in lifted_args.iter().enumerate() {
            if let TermData::Ite(cond, then_t, else_t) = self.get(arg).clone() {
                if self.sort(then_t) != &Sort::Bool {
                    let mut then_args = lifted_args.clone();
                    then_args[i] = then_t;
                    let mut else_args = lifted_args.clone();
                    else_args[i] = else_t;

                    let result_sort = self.sort(term).clone();
                    let then_app = self.mk_app(sym.clone(), then_args, result_sort.clone());
                    let else_app = self.mk_app(sym, else_args, result_sort);

                    let ite = self.mk_ite(cond, then_app, else_app);
                    return self.lift_ite_recursive_with_ctx(ite, ctx);
                }
            }
        }

        // No non-Bool ITE found; rebuild only if arguments changed
        if lifted_args.iter().zip(args.iter()).any(|(&a, &b)| a != b) {
            let result_sort = self.sort(term).clone();
            self.mk_app(sym, lifted_args, result_sort)
        } else {
            term
        }
    }

    /// Lift ITE from an arithmetic predicate's arguments.
    ///
    /// If arg0 or arg1 contains an arithmetic ITE, we expand:
    /// - `(pred (ite c t e) y)` → `(ite c (pred t y) (pred e y))`
    /// - `(pred x (ite c t e))` → `(ite c (pred x t) (pred x e))`
    ///
    /// This also handles nested ITEs like `(pred (+ x (ite c a b)) y)`.
    fn lift_ite_from_predicate_with_ctx(
        &mut self,
        pred: &str,
        arg0: TermId,
        arg1: TermId,
        ctx: &mut IteLiftCtx,
    ) -> TermId {
        let lifted_arg0 = self.lift_ite_from_arith_with_ctx(arg0, ctx);
        let lifted_arg1 = self.lift_ite_from_arith_with_ctx(arg1, ctx);

        if let TermData::Ite(cond, then_t, else_t) = self.get(lifted_arg0).clone() {
            if self.sort(then_t) != &Sort::Bool {
                let then_pred =
                    self.lift_ite_from_predicate_with_ctx(pred, then_t, lifted_arg1, ctx);
                let else_pred =
                    self.lift_ite_from_predicate_with_ctx(pred, else_t, lifted_arg1, ctx);
                // The condition may contain arithmetic ITEs in Boolean
                // predicates (e.g., `(= (+ (ite B 64 0) 52) 116)`).
                // Recursively lift so theory atoms are ITE-free (#4786).
                let lifted_cond = self.lift_ite_recursive_with_ctx(cond, ctx);
                return self.mk_ite(lifted_cond, then_pred, else_pred);
            }
        }

        if let TermData::Ite(cond, then_t, else_t) = self.get(lifted_arg1).clone() {
            if self.sort(then_t) != &Sort::Bool {
                let then_pred =
                    self.lift_ite_from_predicate_with_ctx(pred, lifted_arg0, then_t, ctx);
                let else_pred =
                    self.lift_ite_from_predicate_with_ctx(pred, lifted_arg0, else_t, ctx);
                let lifted_cond = self.lift_ite_recursive_with_ctx(cond, ctx);
                return self.mk_ite(lifted_cond, then_pred, else_pred);
            }
        }

        // No ITE at top level, create the predicate directly.
        // Use specialized constructors for constant folding (#4786).
        self.mk_predicate(pred, lifted_arg0, lifted_arg1)
    }

    /// Create a predicate term using specialized constructors that perform
    /// constant folding. Falls back to raw `mk_app` for unknown predicates.
    fn mk_predicate(&mut self, pred: &str, lhs: TermId, rhs: TermId) -> TermId {
        match pred {
            "=" => self.mk_eq(lhs, rhs),
            "<" => self.mk_lt(lhs, rhs),
            "<=" => self.mk_le(lhs, rhs),
            ">" => self.mk_gt(lhs, rhs),
            ">=" => self.mk_ge(lhs, rhs),
            "distinct" => self.mk_distinct(vec![lhs, rhs]),
            _ => self.mk_app(Symbol::Named(pred.to_string()), vec![lhs, rhs], Sort::Bool),
        }
    }

    /// Create an arithmetic term using specialized constructors that perform
    /// constant folding. Falls back to raw `mk_app` for unknown operations.
    ///
    /// This ensures that after ITE lifting, expressions like `(+ 64 52)` are
    /// folded to `116` instead of remaining as opaque `mk_app` terms (#4786).
    fn mk_arith_op(&mut self, op: &str, args: Vec<TermId>, sort: Sort) -> TermId {
        match op {
            "+" => self.mk_add(args),
            "-" if args.len() == 1 => self.mk_neg(args[0]),
            "-" => self.mk_sub(args),
            "*" => self.mk_mul(args),
            "/" if args.len() == 2 => self.mk_div(args[0], args[1]),
            "abs" if args.len() == 1 => self.mk_abs(args[0]),
            "to_real" if args.len() == 1 => self.mk_to_real(args[0]),
            "to_int" if args.len() == 1 => self.mk_to_int(args[0]),
            _ => self.mk_app(Symbol::Named(op.to_string()), args, sort),
        }
    }

    fn is_liftable_arith_op(name: &str) -> bool {
        matches!(
            name,
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int"
        )
    }

    fn lift_named_arith_app_with_ctx(
        &mut self,
        term: TermId,
        name: &str,
        args: &[TermId],
        sort: Sort,
        ctx: &mut IteLiftCtx,
    ) -> TermId {
        if !Self::is_liftable_arith_op(name) {
            return self.lift_ite_recursive_with_ctx(term, ctx);
        }

        let lifted_args: Vec<TermId> = args
            .iter()
            .map(|&arg| self.lift_ite_from_arith_with_ctx(arg, ctx))
            .collect();

        for (index, &arg) in lifted_args.iter().enumerate() {
            if let TermData::Ite(cond, then_t, else_t) = self.get(arg).clone() {
                let mut then_args = lifted_args.clone();
                then_args[index] = then_t;
                let mut else_args = lifted_args.clone();
                else_args[index] = else_t;

                let then_op = self.mk_arith_op(name, then_args, sort.clone());
                let else_op = self.mk_arith_op(name, else_args, sort);
                let lifted_then_op = self.lift_ite_from_arith_with_ctx(then_op, ctx);
                let lifted_else_op = self.lift_ite_from_arith_with_ctx(else_op, ctx);

                return self.mk_ite(cond, lifted_then_op, lifted_else_op);
            }
        }

        if lifted_args
            .iter()
            .zip(args.iter())
            .any(|(&lhs, &rhs)| lhs != rhs)
        {
            self.mk_arith_op(name, lifted_args, sort)
        } else {
            term
        }
    }

    /// Lift ITEs out of arithmetic expressions.
    ///
    /// Transforms: `(+ x (ite c a b))` → `(ite c (+ x a) (+ x b))`
    ///
    /// This is applied recursively to handle deeply nested ITEs.
    fn lift_ite_from_arith_with_ctx(&mut self, term: TermId, ctx: &mut IteLiftCtx) -> TermId {
        if let Some(&cached) = ctx.arith_rewritten.get(&term) {
            return cached;
        }

        let sort = self.sort(term).clone();

        if sort == Sort::Bool {
            ctx.arith_rewritten.insert(term, term);
            return term;
        }
        if !self.contains_liftable_ite(term, ctx) {
            ctx.arith_rewritten.insert(term, term);
            return term;
        }

        let lifted = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,

            TermData::Ite(cond, then_t, else_t) => {
                let lifted_then = self.lift_ite_from_arith_with_ctx(then_t, ctx);
                let lifted_else = self.lift_ite_from_arith_with_ctx(else_t, ctx);
                if lifted_then == then_t && lifted_else == else_t {
                    term
                } else {
                    self.mk_ite(cond, lifted_then, lifted_else)
                }
            }

            TermData::App(Symbol::Named(ref name), ref args) => {
                self.lift_named_arith_app_with_ctx(term, name, args, sort, ctx)
            }

            TermData::App(Symbol::Indexed(_, _), _)
            | TermData::Not(_)
            | TermData::Let(_, _)
            | TermData::Forall(_, _, _)
            | TermData::Exists(_, _, _) => term,
        };

        ctx.arith_rewritten.insert(term, lifted);
        lifted
    }

    fn contains_liftable_ite(&self, term: TermId, ctx: &mut IteLiftCtx) -> bool {
        if let Some(&cached) = ctx.contains_liftable_ite.get(&term) {
            return cached;
        }

        let contains = match self.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => false,
            TermData::Not(inner) => self.contains_liftable_ite(*inner, ctx),
            TermData::Ite(cond, then_t, else_t) => {
                self.sort(term) != &Sort::Bool
                    || self.contains_liftable_ite(*cond, ctx)
                    || self.contains_liftable_ite(*then_t, ctx)
                    || self.contains_liftable_ite(*else_t, ctx)
            }
            TermData::App(_, args) => args.iter().any(|&arg| self.contains_liftable_ite(arg, ctx)),
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => false,
        };

        ctx.contains_liftable_ite.insert(term, contains);
        contains
    }

    /// Lift arithmetic ITEs from all terms in a list.
    pub fn lift_arithmetic_ite_all(&mut self, terms: &[TermId]) -> Vec<TermId> {
        let mut ctx = IteLiftCtx::default();
        terms
            .iter()
            .map(|&term| self.lift_ite_recursive_with_ctx(term, &mut ctx))
            .collect()
    }
}
