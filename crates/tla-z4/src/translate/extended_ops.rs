// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Extended translation operations for z4.
//!
//! Contains:
//! - Module reference translation (conjunct selection, Part of #572)
//! - Floor division/modulo encoding (TLA+ semantics, Part of #631)
//! - String expression translation (via integer interning)
//! - Helper utilities (`expr_variant_name`, `collect_conjuncts`)

use tla_core::ast::{Expr, ModuleTarget};
use tla_core::Spanned;
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{TlaSort, Z4Translator};

/// Returns a human-readable name for an Expr variant.
///
/// This is used to generate actionable error messages when an expression
/// cannot be translated, instead of opaque "Discriminant(N)" output.
pub(super) fn expr_variant_name(expr: &Expr) -> &'static str {
    match expr {
        // Literals
        Expr::Bool(_) => "Bool",
        Expr::Int(_) => "Int",
        Expr::String(_) => "String",
        // Names
        Expr::Ident(_, _) => "Ident",
        Expr::StateVar(..) => "StateVar",
        // Operators
        Expr::Apply(..) => "Apply (operator application)",
        Expr::OpRef(_) => "OpRef (operator reference)",
        Expr::ModuleRef(..) => "ModuleRef",
        Expr::InstanceExpr(..) => "InstanceExpr",
        Expr::Lambda(..) => "Lambda",
        // Logic
        Expr::And(..) => "And",
        Expr::Or(..) => "Or",
        Expr::Not(_) => "Not",
        Expr::Implies(..) => "Implies",
        Expr::Equiv(..) => "Equiv",
        // Quantifiers
        Expr::Forall(..) => "Forall",
        Expr::Exists(..) => "Exists",
        Expr::Choose(..) => "Choose",
        // Sets
        Expr::SetEnum(_) => "SetEnum",
        Expr::SetBuilder(..) => "SetBuilder",
        Expr::SetFilter(..) => "SetFilter",
        Expr::In(..) => "In (membership)",
        Expr::NotIn(..) => "NotIn",
        Expr::Subseteq(..) => "Subseteq",
        Expr::Union(..) => "Union",
        Expr::Intersect(..) => "Intersect",
        Expr::SetMinus(..) => "SetMinus",
        Expr::Powerset(_) => "Powerset",
        Expr::BigUnion(_) => "BigUnion",
        // Functions
        Expr::FuncDef(..) => "FuncDef",
        Expr::FuncApply(..) => "FuncApply",
        Expr::Domain(_) => "Domain",
        Expr::Except(..) => "Except",
        Expr::FuncSet(..) => "FuncSet",
        // Records
        Expr::Record(_) => "Record",
        Expr::RecordAccess(..) => "RecordAccess",
        Expr::RecordSet(_) => "RecordSet",
        // Tuples
        Expr::Tuple(_) => "Tuple",
        Expr::Times(_) => "Times (Cartesian product)",
        // Temporal
        Expr::Prime(_) => "Prime",
        Expr::Always(_) => "Always (temporal)",
        Expr::Eventually(_) => "Eventually (temporal)",
        Expr::LeadsTo(..) => "LeadsTo (temporal)",
        Expr::WeakFair(..) => "WeakFair (temporal)",
        Expr::StrongFair(..) => "StrongFair (temporal)",
        Expr::Enabled(_) => "Enabled",
        Expr::Unchanged(_) => "Unchanged",
        // Arithmetic
        Expr::Neg(_) => "Neg",
        Expr::Add(..) => "Add",
        Expr::Sub(..) => "Sub",
        Expr::Mul(..) => "Mul",
        Expr::Div(..) => "Div",
        Expr::IntDiv(..) => "IntDiv",
        Expr::Mod(..) => "Mod",
        Expr::Pow(..) => "Pow (exponentiation)",
        Expr::Range(..) => "Range (..)",
        // Comparison
        Expr::Eq(..) => "Eq",
        Expr::Neq(..) => "Neq",
        Expr::Lt(..) => "Lt",
        Expr::Leq(..) => "Leq",
        Expr::Gt(..) => "Gt",
        Expr::Geq(..) => "Geq",
        // Control
        Expr::If(..) => "If",
        Expr::Case(..) => "Case",
        Expr::Let(..) => "Let",
        Expr::SubstIn(..) => "SubstIn (deferred substitution)",
        Expr::Label(_) => "Label",
    }
}

/// Collect all conjuncts from a conjunction expression.
/// Part of #572
pub(super) fn collect_conjuncts(expr: &Spanned<Expr>) -> Vec<Spanned<Expr>> {
    fn collect_inner(expr: &Spanned<Expr>, out: &mut Vec<Spanned<Expr>>) {
        match &expr.node {
            Expr::And(left, right) => {
                collect_inner(left, out);
                collect_inner(right, out);
            }
            _ => {
                out.push(expr.clone());
            }
        }
    }
    let mut result = Vec::new();
    collect_inner(expr, &mut result);
    result
}

impl Z4Translator {
    /// Translate ModuleRef expressions (Part of #572: Conjunct selection).
    pub(super) fn translate_module_ref_bool(
        &mut self,
        target: &ModuleTarget,
        op_name: &str,
        args: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        if !args.is_empty() {
            return Err(Z4Error::UntranslatableExpr(format!(
                "ModuleRef with arguments not supported: {}!{} with {} args",
                match target {
                    ModuleTarget::Named(s) => s.clone(),
                    _ => "<complex>".into(),
                },
                op_name,
                args.len()
            )));
        }
        if let Ok(idx) = op_name.parse::<usize>() {
            if idx > 0 {
                let name = match target {
                    ModuleTarget::Named(n) => n.clone(),
                    _ => {
                        return Err(Z4Error::UntranslatableExpr(format!(
                            "Conjunct selection requires Named target: {target:?}!{op_name}"
                        )))
                    }
                };
                let def = self.constant_defs.get(&name).cloned().ok_or_else(|| {
                    Z4Error::UntranslatableExpr(format!("Undefined operator: {name}!{op_name}"))
                })?;
                if let Expr::And(_, _) = &def.node {
                    let cs = collect_conjuncts(&def);
                    if idx - 1 < cs.len() {
                        return self.translate_bool(&cs[idx - 1]);
                    }
                    return Err(Z4Error::UntranslatableExpr(format!(
                        "{}!{} out of range ({} conjuncts)",
                        name,
                        op_name,
                        cs.len()
                    )));
                }
                return Err(Z4Error::UntranslatableExpr(format!(
                    "{name}!{op_name} not a conjunction"
                )));
            }
        }
        Err(Z4Error::UntranslatableExpr(format!(
            "ModuleRef not supported: {target:?}!{op_name}"
        )))
    }

    /// Translate IntDiv with floor-division encoding (Part of #631).
    ///
    /// TLA+ uses floor division (rounds toward negative infinity).
    /// z4's int_div uses SMT-LIB Euclidean division (x = q*d + r, 0 <= r < |d|).
    pub(super) fn translate_int_div_floor(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Check for literal zero divisor at translation time.
        if let Expr::Int(k) = &right.node {
            if *k == num_bigint::BigInt::from(0) {
                return Err(Z4Error::UnsupportedOp("Division by zero".to_string()));
            }
        }
        let l = self.translate_int(left)?;
        let r = self.translate_int(right)?;
        // Euclidean→floor: adjust when divisor is negative and there is a remainder.
        // Euclidean q with positive divisor already equals floor q.
        // Euclidean q with negative divisor equals floor q + 1 (when remainder exists).
        let euclid_q = self.solver.try_int_div(l, r)?;
        let product = self.solver.try_mul(euclid_q, r)?;
        let eq_check = self.solver.try_eq(product, l)?;
        let has_remainder = self.solver.try_not(eq_check)?;
        let zero = self.solver.int_const(0);
        let r_neg = self.solver.try_lt(r, zero)?;
        let needs_adj = self.solver.try_and(r_neg, has_remainder)?;
        let one = self.solver.int_const(1);
        let adjusted = self.solver.try_sub(euclid_q, one)?;
        Ok(self.solver.try_ite(needs_adj, adjusted, euclid_q)?)
    }

    /// Translate Mod with TLA+ semantics (Part of #631).
    ///
    /// TLA+ mod result is in [0, divisor-1] for positive divisor.
    /// z4's modulo uses Euclidean semantics (0 <= r < |d|), which already
    /// produces non-negative results when the divisor is positive (as TLC requires).
    /// The defensive adjustment below handles any future semantic changes.
    pub(super) fn translate_int_mod_floor(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // TLC requires divisor > 0 for modulo (#554).
        if let Expr::Int(k) = &right.node {
            let zero = num_bigint::BigInt::from(0);
            if *k <= zero {
                return Err(Z4Error::UnsupportedOp(format!(
                    "TLA+ modulo requires positive divisor (got {k})"
                )));
            }
        }
        let l = self.translate_int(left)?;
        let r = self.translate_int(right)?;
        let euclid_r = self.solver.try_modulo(l, r)?;
        let zero = self.solver.int_const(0);
        let r_neg = self.solver.try_lt(euclid_r, zero)?;
        let adjusted = self.solver.try_add(euclid_r, r)?;
        Ok(self.solver.try_ite(r_neg, adjusted, euclid_r)?)
    }

    /// Translate a TLA+ string expression to z4 (as interned integer)
    pub fn translate_string(&mut self, expr: &Spanned<Expr>) -> Z4Result<Term> {
        match &expr.node {
            Expr::String(s) => {
                let id = self.intern_string(s);
                Ok(self.solver.int_const(id))
            }
            Expr::Ident(name, _) => {
                let (sort, term) = self.get_var(name)?;
                if sort != TlaSort::String {
                    return Err(Z4Error::TypeMismatch {
                        name: name.clone(),
                        expected: "String".to_string(),
                        actual: format!("{sort}"),
                    });
                }
                Ok(term)
            }
            Expr::If(cond, then_branch, else_branch) => {
                let c = self.translate_bool(cond)?;
                let t = self.translate_string(then_branch)?;
                let e = self.translate_string(else_branch)?;
                Ok(self.solver.try_ite(c, t, e)?)
            }
            Expr::FuncApply(func, arg) => self.translate_tuple_apply_string(func, arg),
            _ => Err(Z4Error::UntranslatableExpr(format!(
                "{} expression cannot be translated to String",
                expr_variant_name(&expr.node)
            ))),
        }
    }
}
