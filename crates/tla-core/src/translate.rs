// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared expression translation dispatch for solver backends.
//!
//! This module provides [`TranslateExpr`] plus shared dispatch helpers used by
//! SMT backends that translate `Spanned<Expr>` into backend-specific terms.
//! The core crate defines the shared recursion and backend hooks; solver crates
//! provide backend-specific implementations.

use crate::ast::Expr;
use crate::name_intern::NameId;
use crate::span::Spanned;

/// Backend hook points for translating TLA+ expressions.
///
/// Backends choose output types via associated types:
/// - solvers with one term type use `Bool = Int = Term`
/// - solvers with split sorts (for example Z3) use separate bool/int types.
///
/// # Stability
///
/// The stable public translate surface is re-exported from the crate root:
/// `tla_core::{dispatch_translate_bool, dispatch_translate_int, TranslateExpr}`.
/// The internal module path `tla_core::translate::*` is not part of the
/// external API contract and should not be used from downstream docs or tests.
pub trait TranslateExpr {
    type Bool: Clone;
    type Int;
    type Error: From<String>;

    // === Primitive constructors ===
    fn bool_const(&mut self, val: bool) -> Self::Bool;
    fn int_const(&mut self, val: i64) -> Result<Self::Int, Self::Error>;

    // === Variable lookup ===
    fn lookup_bool_var(&mut self, name: &str) -> Result<Self::Bool, Self::Error>;
    fn lookup_int_var(&mut self, name: &str) -> Result<Self::Int, Self::Error>;

    // === Boolean operations ===
    fn and(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool;
    fn or(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool;
    fn not(&mut self, expr: Self::Bool) -> Self::Bool;
    fn implies(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool;
    /// Biconditional (iff). Default: `(lhs => rhs) /\ (rhs => lhs)`.
    fn iff(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool {
        let lr = self.implies(lhs.clone(), rhs.clone());
        let rl = self.implies(rhs, lhs);
        self.and(lr, rl)
    }

    // === Comparisons (Int -> Bool) ===
    fn lt(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool;
    fn le(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool;
    fn gt(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool;
    fn ge(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool;

    // === Arithmetic ===
    fn add(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Int;
    fn sub(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Int;
    fn mul(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error>;
    fn neg(&mut self, expr: Self::Int) -> Self::Int;
    fn div(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error>;
    fn modulo(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error>;

    // === If-then-else ===
    fn ite_bool(&mut self, cond: Self::Bool, then_b: Self::Bool, else_b: Self::Bool) -> Self::Bool;
    fn ite_int(&mut self, cond: Self::Bool, then_i: Self::Int, else_i: Self::Int) -> Self::Int;

    // === Equality (backend-specific type inference) ===
    fn translate_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Result<Self::Bool, Self::Error>;

    // === Extension hooks for backend-specific variants ===
    /// Hook that runs before shared bool dispatch.
    ///
    /// Returning `Some(...)` short-circuits the shared matcher. Backends may
    /// override any expression arm here, including arms otherwise handled by
    /// the shared dispatcher. Return `None` to continue with shared dispatch.
    fn translate_bool_extended(
        &mut self,
        _expr: &Spanned<Expr>,
    ) -> Option<Result<Self::Bool, Self::Error>> {
        None
    }

    /// Hook that runs before shared int dispatch.
    ///
    /// Returning `Some(...)` short-circuits the shared matcher. Backends may
    /// override any expression arm here, including arms otherwise handled by
    /// the shared dispatcher. Return `None` to continue with shared dispatch.
    fn translate_int_extended(
        &mut self,
        _expr: &Spanned<Expr>,
    ) -> Option<Result<Self::Int, Self::Error>> {
        None
    }
}

/// Shared `translate_bool` dispatch for [`TranslateExpr`] backends.
///
/// Extension hooks are checked first. Backends may override any expression arm,
/// including arms otherwise handled by the shared matcher, by returning
/// `Some(...)` from [`TranslateExpr::translate_bool_extended`]. Returning
/// `None` continues into the shared dispatch below.
pub fn dispatch_translate_bool<T: TranslateExpr + ?Sized>(
    translator: &mut T,
    expr: &Spanned<Expr>,
) -> Result<T::Bool, T::Error> {
    // Check backend extension hooks first — backends can override any arm.
    if let Some(result) = translator.translate_bool_extended(expr) {
        return result;
    }

    match &expr.node {
        Expr::Bool(b) => Ok(translator.bool_const(*b)),

        Expr::Ident(name, NameId::INVALID) | Expr::StateVar(name, _, _) => {
            translator.lookup_bool_var(name)
        }

        Expr::And(left, right) => {
            let lhs = dispatch_translate_bool(translator, left)?;
            let rhs = dispatch_translate_bool(translator, right)?;
            Ok(translator.and(lhs, rhs))
        }

        Expr::Or(left, right) => {
            let lhs = dispatch_translate_bool(translator, left)?;
            let rhs = dispatch_translate_bool(translator, right)?;
            Ok(translator.or(lhs, rhs))
        }

        Expr::Not(inner) => {
            let val = dispatch_translate_bool(translator, inner)?;
            Ok(translator.not(val))
        }

        Expr::Implies(left, right) => {
            let lhs = dispatch_translate_bool(translator, left)?;
            let rhs = dispatch_translate_bool(translator, right)?;
            Ok(translator.implies(lhs, rhs))
        }

        Expr::Equiv(left, right) => {
            let lhs = dispatch_translate_bool(translator, left)?;
            let rhs = dispatch_translate_bool(translator, right)?;
            Ok(translator.iff(lhs, rhs))
        }

        Expr::Eq(left, right) => translator.translate_eq(left, right),

        Expr::Neq(left, right) => {
            let eq = translator.translate_eq(left, right)?;
            Ok(translator.not(eq))
        }

        Expr::Lt(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.lt(lhs, rhs))
        }

        Expr::Leq(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.le(lhs, rhs))
        }

        Expr::Gt(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.gt(lhs, rhs))
        }

        Expr::Geq(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.ge(lhs, rhs))
        }

        Expr::If(cond, then_branch, else_branch) => {
            let cond = dispatch_translate_bool(translator, cond)?;
            let then_b = dispatch_translate_bool(translator, then_branch)?;
            let else_b = dispatch_translate_bool(translator, else_branch)?;
            Ok(translator.ite_bool(cond, then_b, else_b))
        }

        _ => Err(format!("unsupported bool expr: {:?}", expr.node).into()),
    }
}

/// Shared `translate_int` dispatch for [`TranslateExpr`] backends.
///
/// Extension hooks are checked first. Backends may override any expression arm,
/// including arms otherwise handled by the shared matcher, by returning
/// `Some(...)` from [`TranslateExpr::translate_int_extended`]. Returning
/// `None` continues into the shared dispatch below.
pub fn dispatch_translate_int<T: TranslateExpr + ?Sized>(
    translator: &mut T,
    expr: &Spanned<Expr>,
) -> Result<T::Int, T::Error> {
    // Check backend extension hooks first — backends can override any arm.
    if let Some(result) = translator.translate_int_extended(expr) {
        return result;
    }

    match &expr.node {
        Expr::Int(n) => {
            let val: i64 = n
                .try_into()
                .map_err(|_| format!("integer {n} too large for i64"))?;
            translator.int_const(val)
        }

        Expr::Ident(name, NameId::INVALID) | Expr::StateVar(name, _, _) => {
            translator.lookup_int_var(name)
        }

        Expr::Add(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.add(lhs, rhs))
        }

        Expr::Sub(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            Ok(translator.sub(lhs, rhs))
        }

        Expr::Mul(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            translator.mul(lhs, rhs)
        }

        Expr::IntDiv(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            translator.div(lhs, rhs)
        }

        Expr::Mod(left, right) => {
            let lhs = dispatch_translate_int(translator, left)?;
            let rhs = dispatch_translate_int(translator, right)?;
            translator.modulo(lhs, rhs)
        }

        Expr::Neg(inner) => {
            let val = dispatch_translate_int(translator, inner)?;
            Ok(translator.neg(val))
        }

        Expr::If(cond, then_branch, else_branch) => {
            let cond = dispatch_translate_bool(translator, cond)?;
            let then_i = dispatch_translate_int(translator, then_branch)?;
            let else_i = dispatch_translate_int(translator, else_branch)?;
            Ok(translator.ite_int(cond, then_i, else_i))
        }

        _ => Err(format!("unsupported int expr: {:?}", expr.node).into()),
    }
}

#[cfg(test)]
mod tests;
