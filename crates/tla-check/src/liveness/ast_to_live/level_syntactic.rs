// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Syntactic-only expression level classification.
//!
//! These methods classify TLA+ expressions by level (Constant, State, Action,
//! Temporal) without resolving operator definitions. For context-aware
//! classification that resolves operators and instance scoping, see `level.rs`.

use super::super::live_expr::ExprLevel;
use super::core::AstToLive;
use tla_core::ast::{BoundVar, ExceptSpec, Expr, ModuleTarget, Substitution};
use tla_core::Spanned;

impl AstToLive {
    /// Determine the level of an expression (syntactic only, no operator resolution)
    ///
    /// Returns:
    /// - Constant: No variables, can be evaluated statically
    /// - State: Depends on current state only (no primes, no temporal)
    /// - Action: Depends on current and next state (has primes)
    /// - Temporal: Contains temporal operators ([], <>, WF, SF, ~>)
    #[allow(clippy::only_used_in_recursion)]
    pub fn get_level(&self, expr: &Expr) -> ExprLevel {
        match expr {
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => ExprLevel::Constant,
            Expr::Ident(_, _) | Expr::StateVar(_, _, _) | Expr::Enabled(_) => ExprLevel::State,
            Expr::Prime(_) | Expr::Unchanged(_) => ExprLevel::Action,
            Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => ExprLevel::Temporal,

            // Binary: max of both operand levels
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::FuncApply(a, b)
            | Expr::FuncSet(a, b)
            | Expr::Range(a, b) => self.get_level(&a.node).max(self.get_level(&b.node)),

            // Unary: inherit from operand
            Expr::Not(e)
            | Expr::Neg(e)
            | Expr::Powerset(e)
            | Expr::BigUnion(e)
            | Expr::Domain(e) => self.get_level(&e.node),

            Expr::If(c, t, e) => self.level_max3(&c.node, &t.node, &e.node),
            Expr::RecordAccess(r, _) | Expr::Lambda(_, r) => self.get_level(&r.node),
            Expr::Label(label) => self.get_level(&label.body.node),

            // Compound: delegate to helpers
            Expr::Let(defs, body) => self.level_bounds_body_let(defs, body),
            Expr::Apply(op, args) => self.level_apply(op, args),
            Expr::ModuleRef(target, _, args) => self.level_module_ref(target, args),
            Expr::InstanceExpr(_, subs) => self.level_subs(subs),
            Expr::SubstIn(subs, body) => self.get_level(&body.node).max(self.level_subs(subs)),
            Expr::Forall(b, body) | Expr::Exists(b, body) => self.level_bounds_body(b, &body.node),
            Expr::Choose(b, pred) | Expr::SetFilter(b, pred) => {
                self.level_bound_pred(b, &pred.node)
            }
            Expr::SetBuilder(e, b) => self.level_bounds_body(b, &e.node),
            Expr::FuncDef(b, body) => self.level_bounds_body(b, &body.node),
            Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
                self.level_spanned_max(elems)
            }
            Expr::Except(base, specs) => self.level_except(&base.node, specs),
            Expr::Record(fields) => self.level_fields(fields),
            Expr::RecordSet(fields) => self.level_fields(fields),
            Expr::Case(arms, other) => self.level_case(arms, other),
        }
    }

    /// Check if an expression contains primed variables
    pub fn contains_prime(&self, expr: &Expr) -> bool {
        self.get_level(expr) >= ExprLevel::Action
    }

    /// Check if an expression contains temporal operators
    pub fn contains_temporal(&self, expr: &Expr) -> bool {
        self.get_level(expr) >= ExprLevel::Temporal
    }

    // -- Helpers for get_level --

    fn level_max3(&self, a: &Expr, b: &Expr, c: &Expr) -> ExprLevel {
        self.get_level(a)
            .max(self.get_level(b))
            .max(self.get_level(c))
    }

    fn level_spanned_max(&self, items: &[Spanned<Expr>]) -> ExprLevel {
        items.iter().fold(ExprLevel::Constant, |acc, item| {
            acc.max(self.get_level(&item.node))
        })
    }

    fn level_subs(&self, subs: &[Substitution]) -> ExprLevel {
        subs.iter().fold(ExprLevel::Constant, |acc, sub| {
            acc.max(self.get_level(&sub.to.node))
        })
    }

    fn level_bounds_body(&self, bounds: &[BoundVar], body: &Expr) -> ExprLevel {
        let mut level = self.get_level(body);
        for bound in bounds {
            if let Some(domain) = &bound.domain {
                level = level.max(self.get_level(&domain.node));
            }
        }
        level
    }

    fn level_bound_pred(&self, bound: &BoundVar, pred: &Expr) -> ExprLevel {
        let mut level = self.get_level(pred);
        if let Some(domain) = &bound.domain {
            level = level.max(self.get_level(&domain.node));
        }
        level
    }

    fn level_bounds_body_let(
        &self,
        defs: &[tla_core::ast::OperatorDef],
        body: &Spanned<Expr>,
    ) -> ExprLevel {
        let mut level = self.get_level(&body.node);
        for def in defs {
            level = level.max(self.get_level(&def.body.node));
        }
        level
    }

    fn level_apply(&self, op: &Spanned<Expr>, args: &[Spanned<Expr>]) -> ExprLevel {
        if let Expr::Ident(name, _) = &op.node {
            if name.starts_with("WF_") || name.starts_with("SF_") {
                return ExprLevel::Temporal;
            }
        }
        let mut level = self.get_level(&op.node);
        for arg in args {
            level = level.max(self.get_level(&arg.node));
        }
        level
    }

    fn level_module_ref(&self, target: &ModuleTarget, args: &[Spanned<Expr>]) -> ExprLevel {
        let mut level = match target {
            ModuleTarget::Parameterized(_, params) => self.level_spanned_max(params),
            ModuleTarget::Chained(base) => self.get_level(&base.node),
            ModuleTarget::Named(_) => ExprLevel::Constant,
        };
        for arg in args {
            level = level.max(self.get_level(&arg.node));
        }
        level
    }

    fn level_except(&self, base: &Expr, specs: &[ExceptSpec]) -> ExprLevel {
        let mut level = self.get_level(base);
        for spec in specs {
            level = level.max(self.get_level(&spec.value.node));
            for path_elem in &spec.path {
                if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                    level = level.max(self.get_level(&idx.node));
                }
            }
        }
        level
    }

    fn level_fields(&self, fields: &[(Spanned<String>, Spanned<Expr>)]) -> ExprLevel {
        fields.iter().fold(ExprLevel::Constant, |acc, (_, v)| {
            acc.max(self.get_level(&v.node))
        })
    }

    fn level_case(
        &self,
        arms: &[tla_core::ast::CaseArm],
        other: &Option<Box<Spanned<Expr>>>,
    ) -> ExprLevel {
        let mut level = ExprLevel::Constant;
        for arm in arms {
            level = level.max(self.get_level(&arm.guard.node));
            level = level.max(self.get_level(&arm.body.node));
        }
        if let Some(other_expr) = other {
            level = level.max(self.get_level(&other_expr.node));
        }
        level
    }
}
