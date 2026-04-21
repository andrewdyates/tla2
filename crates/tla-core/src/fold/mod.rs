// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic expression fold trait for TLA+ AST.
//!
//! `ExprFold` provides a default identity traversal over all 65 `Expr` variants.
//! Override specific `fold_*` methods to customize behavior at particular nodes
//! while inheriting the structural recursion for all other variants.
//!
//! This fold's default recursion preserves the historical visitor traversal
//! shape used in `tla-check` while centralizing the structural logic in one
//! place.

mod free_vars;
mod substitute;

use crate::ast::*;
use crate::name_intern::NameId;
use crate::span::Spanned;

pub use substitute::{SpanPolicy, SubstituteAt, SubstituteExpr};

/// Trait for transforming expressions by structural recursion.
///
/// The default implementation recursively rebuilds the expression unchanged
/// (identity fold). Override `fold_expr` for top-level interception, or
/// override specific helpers (`fold_ident`, `fold_bound_var`, etc.) to
/// customize behavior at particular node types.
pub trait ExprFold {
    /// Main entry point. Override this for top-level interception.
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        Spanned {
            node: self.fold_expr_inner(expr.node),
            span,
        }
    }

    /// Dispatch to per-variant fold methods. Rarely needs overriding.
    fn fold_expr_inner(&mut self, expr: Expr) -> Expr {
        match expr {
            // === Leaf variants (no sub-expressions) ===
            Expr::Bool(b) => Expr::Bool(b),
            Expr::Int(n) => Expr::Int(n),
            Expr::String(s) => Expr::String(s),
            Expr::Ident(name, name_id) => self.fold_ident(name, name_id),
            Expr::StateVar(name, idx, id) => self.fold_state_var(name, idx, id),
            Expr::OpRef(name) => Expr::OpRef(name),

            // === Unary (one sub-expression) ===
            Expr::Not(e) => Expr::Not(self.fold_box(e)),
            Expr::Powerset(e) => Expr::Powerset(self.fold_box(e)),
            Expr::BigUnion(e) => Expr::BigUnion(self.fold_box(e)),
            Expr::Domain(e) => Expr::Domain(self.fold_box(e)),
            Expr::Prime(e) => Expr::Prime(self.fold_box(e)),
            Expr::Always(e) => Expr::Always(self.fold_box(e)),
            Expr::Eventually(e) => Expr::Eventually(self.fold_box(e)),
            Expr::Enabled(e) => Expr::Enabled(self.fold_box(e)),
            Expr::Unchanged(e) => Expr::Unchanged(self.fold_box(e)),
            Expr::Neg(e) => Expr::Neg(self.fold_box(e)),

            // === Binary (two sub-expressions) ===
            Expr::And(a, b) => Expr::And(self.fold_box(a), self.fold_box(b)),
            Expr::Or(a, b) => Expr::Or(self.fold_box(a), self.fold_box(b)),
            Expr::Implies(a, b) => Expr::Implies(self.fold_box(a), self.fold_box(b)),
            Expr::Equiv(a, b) => Expr::Equiv(self.fold_box(a), self.fold_box(b)),
            Expr::In(a, b) => Expr::In(self.fold_box(a), self.fold_box(b)),
            Expr::NotIn(a, b) => Expr::NotIn(self.fold_box(a), self.fold_box(b)),
            Expr::Subseteq(a, b) => Expr::Subseteq(self.fold_box(a), self.fold_box(b)),
            Expr::Union(a, b) => Expr::Union(self.fold_box(a), self.fold_box(b)),
            Expr::Intersect(a, b) => Expr::Intersect(self.fold_box(a), self.fold_box(b)),
            Expr::SetMinus(a, b) => Expr::SetMinus(self.fold_box(a), self.fold_box(b)),
            Expr::FuncApply(a, b) => Expr::FuncApply(self.fold_box(a), self.fold_box(b)),
            Expr::FuncSet(a, b) => Expr::FuncSet(self.fold_box(a), self.fold_box(b)),
            Expr::LeadsTo(a, b) => Expr::LeadsTo(self.fold_box(a), self.fold_box(b)),
            Expr::WeakFair(a, b) => Expr::WeakFair(self.fold_box(a), self.fold_box(b)),
            Expr::StrongFair(a, b) => Expr::StrongFair(self.fold_box(a), self.fold_box(b)),
            Expr::Eq(a, b) => Expr::Eq(self.fold_box(a), self.fold_box(b)),
            Expr::Neq(a, b) => Expr::Neq(self.fold_box(a), self.fold_box(b)),
            Expr::Lt(a, b) => Expr::Lt(self.fold_box(a), self.fold_box(b)),
            Expr::Leq(a, b) => Expr::Leq(self.fold_box(a), self.fold_box(b)),
            Expr::Gt(a, b) => Expr::Gt(self.fold_box(a), self.fold_box(b)),
            Expr::Geq(a, b) => Expr::Geq(self.fold_box(a), self.fold_box(b)),
            Expr::Add(a, b) => Expr::Add(self.fold_box(a), self.fold_box(b)),
            Expr::Sub(a, b) => Expr::Sub(self.fold_box(a), self.fold_box(b)),
            Expr::Mul(a, b) => Expr::Mul(self.fold_box(a), self.fold_box(b)),
            Expr::Div(a, b) => Expr::Div(self.fold_box(a), self.fold_box(b)),
            Expr::IntDiv(a, b) => Expr::IntDiv(self.fold_box(a), self.fold_box(b)),
            Expr::Mod(a, b) => Expr::Mod(self.fold_box(a), self.fold_box(b)),
            Expr::Pow(a, b) => Expr::Pow(self.fold_box(a), self.fold_box(b)),
            Expr::Range(a, b) => Expr::Range(self.fold_box(a), self.fold_box(b)),

            // === N-ary (Vec of sub-expressions) ===
            Expr::SetEnum(elems) => Expr::SetEnum(self.fold_vec(elems)),
            Expr::Tuple(elems) => Expr::Tuple(self.fold_vec(elems)),
            Expr::Times(elems) => Expr::Times(self.fold_vec(elems)),

            // === Quantifiers (bound vars + body) ===
            Expr::Forall(bounds, body) => {
                let bounds = self.fold_bound_vars(bounds);
                Expr::Forall(bounds, self.fold_box(body))
            }
            Expr::Exists(bounds, body) => {
                let bounds = self.fold_bound_vars(bounds);
                Expr::Exists(bounds, self.fold_box(body))
            }
            Expr::Choose(bound, body) => {
                let bound = self.fold_bound_var(bound);
                Expr::Choose(bound, self.fold_box(body))
            }
            Expr::SetBuilder(body, bounds) => {
                let bounds = self.fold_bound_vars(bounds);
                Expr::SetBuilder(self.fold_box(body), bounds)
            }
            Expr::SetFilter(bound, body) => {
                let bound = self.fold_bound_var(bound);
                Expr::SetFilter(bound, self.fold_box(body))
            }
            Expr::FuncDef(bounds, body) => {
                let bounds = self.fold_bound_vars(bounds);
                Expr::FuncDef(bounds, self.fold_box(body))
            }
            Expr::Lambda(params, body) => Expr::Lambda(params, self.fold_box(body)),
            Expr::Label(label) => Expr::Label(ExprLabel {
                name: label.name,
                body: self.fold_box(label.body),
            }),

            // === Compound structures ===
            Expr::Apply(func, args) => Expr::Apply(self.fold_box(func), self.fold_vec(args)),
            Expr::ModuleRef(target, op, args) => {
                let new_target = self.fold_module_target(target);
                Expr::ModuleRef(new_target, op, self.fold_vec(args))
            }
            Expr::InstanceExpr(name, substs) => {
                let new_substs = self.fold_substitutions(substs);
                Expr::InstanceExpr(name, new_substs)
            }
            Expr::Record(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(k, v)| (k, self.fold_expr(v)))
                    .collect();
                Expr::Record(fields)
            }
            Expr::RecordAccess(e, field) => Expr::RecordAccess(self.fold_box(e), field),
            Expr::RecordSet(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(k, v)| (k, self.fold_expr(v)))
                    .collect();
                Expr::RecordSet(fields)
            }
            Expr::Except(base, specs) => {
                let base = self.fold_box(base);
                let specs = self.fold_except_specs(specs);
                Expr::Except(base, specs)
            }
            Expr::If(cond, then_, else_) => Expr::If(
                self.fold_box(cond),
                self.fold_box(then_),
                self.fold_box(else_),
            ),
            Expr::Case(arms, default) => {
                let arms = arms
                    .into_iter()
                    .map(|arm| self.fold_case_arm(arm))
                    .collect();
                let default = default.map(|e| self.fold_box(e));
                Expr::Case(arms, default)
            }
            Expr::Let(defs, body) => {
                let defs = self.fold_operator_defs(defs);
                Expr::Let(defs, self.fold_box(body))
            }
            Expr::SubstIn(substs, body) => {
                let new_substs = self.fold_substitutions(substs);
                Expr::SubstIn(new_substs, self.fold_box(body))
            }
        }
    }

    // === Override hooks ===

    /// Fold an identifier. Override to implement substitution.
    fn fold_ident(&mut self, name: String, name_id: NameId) -> Expr {
        Expr::Ident(name, name_id)
    }

    /// Fold a pre-resolved state variable. Override for state-variable transforms.
    fn fold_state_var(&mut self, name: String, idx: u16, id: NameId) -> Expr {
        Expr::StateVar(name, idx, id)
    }

    /// Fold a boxed sub-expression.
    #[allow(clippy::boxed_local)]
    fn fold_box(&mut self, e: Box<Spanned<Expr>>) -> Box<Spanned<Expr>> {
        Box::new(self.fold_expr(*e))
    }

    /// Fold a vector of sub-expressions.
    fn fold_vec(&mut self, v: Vec<Spanned<Expr>>) -> Vec<Spanned<Expr>> {
        v.into_iter().map(|e| self.fold_expr(e)).collect()
    }

    /// Fold a single bound variable. Recurses into the domain expression.
    /// Preserves the `pattern` field (BoundPattern).
    fn fold_bound_var(&mut self, bv: BoundVar) -> BoundVar {
        BoundVar {
            name: bv.name,
            domain: bv.domain.map(|d| Box::new(self.fold_expr(*d))),
            pattern: bv.pattern,
        }
    }

    /// Fold a vector of bound variables.
    fn fold_bound_vars(&mut self, bvs: Vec<BoundVar>) -> Vec<BoundVar> {
        bvs.into_iter().map(|bv| self.fold_bound_var(bv)).collect()
    }

    /// Fold EXCEPT specs. Handles both `Index` (recurse) and `Field` (clone).
    fn fold_except_specs(&mut self, specs: Vec<ExceptSpec>) -> Vec<ExceptSpec> {
        specs
            .into_iter()
            .map(|spec| ExceptSpec {
                path: spec
                    .path
                    .into_iter()
                    .map(|elem| match elem {
                        ExceptPathElement::Index(idx) => {
                            ExceptPathElement::Index(self.fold_expr(idx))
                        }
                        ExceptPathElement::Field(f) => ExceptPathElement::Field(f),
                    })
                    .collect(),
                value: self.fold_expr(spec.value),
            })
            .collect()
    }

    /// Fold a CASE arm (guard + body).
    fn fold_case_arm(&mut self, arm: CaseArm) -> CaseArm {
        CaseArm {
            guard: self.fold_expr(arm.guard),
            body: self.fold_expr(arm.body),
        }
    }

    /// Fold LET operator definitions. Preserves all 8 OperatorDef fields.
    fn fold_operator_defs(&mut self, defs: Vec<OperatorDef>) -> Vec<OperatorDef> {
        defs.into_iter()
            .map(|def| OperatorDef {
                name: def.name,
                params: def.params,
                body: self.fold_expr(def.body),
                local: def.local,
                contains_prime: def.contains_prime,
                guards_depend_on_prime: def.guards_depend_on_prime,
                has_primed_param: def.has_primed_param,
                is_recursive: def.is_recursive,
                self_call_count: def.self_call_count,
            })
            .collect()
    }

    /// Fold a module target. Recurses into Parameterized params and Chained base.
    fn fold_module_target(&mut self, target: ModuleTarget) -> ModuleTarget {
        match target {
            ModuleTarget::Named(name) => ModuleTarget::Named(name),
            ModuleTarget::Parameterized(name, params) => {
                ModuleTarget::Parameterized(name, self.fold_vec(params))
            }
            ModuleTarget::Chained(base) => ModuleTarget::Chained(Box::new(self.fold_expr(*base))),
        }
    }

    /// Fold instance substitutions. Recurses into each substitution's `to` expression.
    /// The `from` field is a binding target, not an expression to transform.
    fn fold_substitutions(&mut self, substs: Vec<Substitution>) -> Vec<Substitution> {
        substs
            .into_iter()
            .map(|sub| Substitution {
                from: sub.from,
                to: self.fold_expr(sub.to),
            })
            .collect()
    }
}

#[cfg(test)]
mod tests;
