// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod identifier;
mod module_ref;

use super::super::live_expr::ExprLevel;
use super::core::AstToLive;
use crate::eval::EvalCtx;
use tla_core::ast::Expr;

impl AstToLive {
    /// Determine the level of an expression with context for operator resolution
    ///
    /// This version looks up operator definitions to correctly classify identifiers
    /// that refer to action-level operators (containing primed variables).
    ///
    /// Returns:
    /// - Constant: No variables, can be evaluated statically
    /// - State: Depends on current state only (no primes, no temporal)
    /// - Action: Depends on current and next state (has primes)
    /// - Temporal: Contains temporal operators ([], <>, WF, SF, ~>)
    pub fn get_level_with_ctx(&self, ctx: &EvalCtx, expr: &Expr) -> ExprLevel {
        self.get_level_with_ctx_inner(
            ctx,
            expr,
            &mut std::collections::HashSet::new(),
            &mut std::collections::HashSet::new(),
        )
    }

    #[allow(clippy::only_used_in_recursion)]
    pub(super) fn get_level_with_ctx_inner(
        &self,
        ctx: &EvalCtx,
        expr: &Expr,
        visited: &mut std::collections::HashSet<String>,
        bound_vars: &mut std::collections::HashSet<String>,
    ) -> ExprLevel {
        match expr {
            // Literals are constant level
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => ExprLevel::Constant,

            // StateVar is a pre-resolved state variable - state level
            Expr::StateVar(_, _, _) => ExprLevel::State,

            Expr::Ident(name, _) => self.level_ident_with_ctx(ctx, name, visited, bound_vars),

            // Prime makes it action level
            Expr::Prime(_) => ExprLevel::Action,

            // Temporal operators are temporal level
            Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => ExprLevel::Temporal,

            // ENABLED is state level (checks if action is enabled in current state)
            // The inner expression might be action-level, but ENABLED itself
            // produces a state-level result
            Expr::Enabled(_) => ExprLevel::State,

            // UNCHANGED is action level (compares x and x')
            Expr::Unchanged(_) => ExprLevel::Action,

            // Binary operators: max of operand levels
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
            | Expr::Range(a, b) => self
                .get_level_with_ctx_inner(ctx, &a.node, visited, bound_vars)
                .max(self.get_level_with_ctx_inner(ctx, &b.node, visited, bound_vars)),

            // Unary operators: inherit from operand
            Expr::Not(e)
            | Expr::Neg(e)
            | Expr::Powerset(e)
            | Expr::BigUnion(e)
            | Expr::Domain(e) => self.get_level_with_ctx_inner(ctx, &e.node, visited, bound_vars),

            // IF-THEN-ELSE: max of all three
            Expr::If(cond, then_e, else_e) => self
                .get_level_with_ctx_inner(ctx, &cond.node, visited, bound_vars)
                .max(self.get_level_with_ctx_inner(ctx, &then_e.node, visited, bound_vars))
                .max(self.get_level_with_ctx_inner(ctx, &else_e.node, visited, bound_vars)),

            // LET-IN: max of definitions and body
            Expr::Let(defs, body) => {
                let mut level = self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars);
                for def in defs {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &def.body.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            // Apply: check for WF_xxx/SF_xxx (parsed as function calls), otherwise max of operator and arguments
            Expr::Apply(op, args) => {
                // Check if this is WF_xxx or SF_xxx (lexer matches as single identifier)
                if let Expr::Ident(name, _) = &op.node {
                    if name.starts_with("WF_") || name.starts_with("SF_") {
                        return ExprLevel::Temporal;
                    }
                }
                let mut level = self.get_level_with_ctx_inner(ctx, &op.node, visited, bound_vars);
                for arg in args {
                    level = level
                        .max(self.get_level_with_ctx_inner(ctx, &arg.node, visited, bound_vars));
                }
                level
            }

            // OpRef is constant (just a reference to an operator)
            Expr::OpRef(_) => ExprLevel::Constant,

            // Module reference: resolve the target context and look up the operator definition.
            Expr::ModuleRef(target, op_name, args) => {
                self.level_module_ref_with_ctx(ctx, target, op_name, args, visited, bound_vars)
            }

            // Lambda: bound parameter names are constant within body
            Expr::Lambda(params, body) => {
                let added: Vec<String> = params
                    .iter()
                    .filter(|p| bound_vars.insert(p.node.clone()))
                    .map(|p| p.node.clone())
                    .collect();
                let level = self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars);
                for name in &added {
                    bound_vars.remove(name);
                }
                level
            }

            // Instance expression
            Expr::InstanceExpr(_, subs) => {
                let mut level = ExprLevel::Constant;
                for sub in subs {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &sub.to.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            // SubstIn: deferred INSTANCE substitution wrapper
            Expr::SubstIn(subs, body) => {
                let mut level = self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars);
                for sub in subs {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &sub.to.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            // Quantifiers: max of domain and body, with bound variable tracking
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                // Domains are evaluated OUTSIDE the binder scope
                let mut level = ExprLevel::Constant;
                for bound in bounds {
                    if let Some(domain) = &bound.domain {
                        level = level.max(self.get_level_with_ctx_inner(
                            ctx,
                            &domain.node,
                            visited,
                            bound_vars,
                        ));
                    }
                }
                // Add bound variable names for body analysis
                let added: Vec<String> = bounds
                    .iter()
                    .filter(|b| bound_vars.insert(b.name.node.clone()))
                    .map(|b| b.name.node.clone())
                    .collect();
                level =
                    level.max(self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars));
                for name in &added {
                    bound_vars.remove(name);
                }
                level
            }

            // CHOOSE: max of domain and predicate, with bound variable tracking
            Expr::Choose(bound, pred) => {
                let mut level = ExprLevel::Constant;
                if let Some(domain) = &bound.domain {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &domain.node,
                        visited,
                        bound_vars,
                    ));
                }
                let was_new = bound_vars.insert(bound.name.node.clone());
                level =
                    level.max(self.get_level_with_ctx_inner(ctx, &pred.node, visited, bound_vars));
                if was_new {
                    bound_vars.remove(&bound.name.node);
                }
                level
            }

            // Set enumeration: max of elements
            Expr::SetEnum(elems) => {
                let mut level = ExprLevel::Constant;
                for elem in elems {
                    level = level
                        .max(self.get_level_with_ctx_inner(ctx, &elem.node, visited, bound_vars));
                }
                level
            }

            // Set builder: max of expression and bounds, with bound variable tracking
            Expr::SetBuilder(expr, bounds) => {
                // Domains are evaluated OUTSIDE the binder scope
                let mut level = ExprLevel::Constant;
                for bound in bounds {
                    if let Some(domain) = &bound.domain {
                        level = level.max(self.get_level_with_ctx_inner(
                            ctx,
                            &domain.node,
                            visited,
                            bound_vars,
                        ));
                    }
                }
                // Add bound variable names for expression analysis
                let added: Vec<String> = bounds
                    .iter()
                    .filter(|b| bound_vars.insert(b.name.node.clone()))
                    .map(|b| b.name.node.clone())
                    .collect();
                level =
                    level.max(self.get_level_with_ctx_inner(ctx, &expr.node, visited, bound_vars));
                for name in &added {
                    bound_vars.remove(name);
                }
                level
            }

            // Set filter: max of domain and predicate, with bound variable tracking
            Expr::SetFilter(bound, pred) => {
                let mut level = ExprLevel::Constant;
                if let Some(domain) = &bound.domain {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &domain.node,
                        visited,
                        bound_vars,
                    ));
                }
                let was_new = bound_vars.insert(bound.name.node.clone());
                level =
                    level.max(self.get_level_with_ctx_inner(ctx, &pred.node, visited, bound_vars));
                if was_new {
                    bound_vars.remove(&bound.name.node);
                }
                level
            }

            // Function definition: max of bounds and body, with bound variable tracking
            Expr::FuncDef(bounds, body) => {
                // Domains are evaluated OUTSIDE the binder scope
                let mut level = ExprLevel::Constant;
                for bound in bounds {
                    if let Some(domain) = &bound.domain {
                        level = level.max(self.get_level_with_ctx_inner(
                            ctx,
                            &domain.node,
                            visited,
                            bound_vars,
                        ));
                    }
                }
                // Add bound variable names for body analysis
                let added: Vec<String> = bounds
                    .iter()
                    .filter(|b| bound_vars.insert(b.name.node.clone()))
                    .map(|b| b.name.node.clone())
                    .collect();
                level =
                    level.max(self.get_level_with_ctx_inner(ctx, &body.node, visited, bound_vars));
                for name in &added {
                    bound_vars.remove(name);
                }
                level
            }

            // EXCEPT: max of base and specs
            Expr::Except(base, specs) => {
                let mut level = self.get_level_with_ctx_inner(ctx, &base.node, visited, bound_vars);
                for spec in specs {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &spec.value.node,
                        visited,
                        bound_vars,
                    ));
                    for path_elem in &spec.path {
                        if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                            level = level.max(
                                self.get_level_with_ctx_inner(ctx, &idx.node, visited, bound_vars),
                            );
                        }
                    }
                }
                level
            }

            // Record: max of field values
            Expr::Record(fields) => {
                let mut level = ExprLevel::Constant;
                for (_, value) in fields {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &value.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            // Record access: level of record
            Expr::RecordAccess(record, _) => {
                self.get_level_with_ctx_inner(ctx, &record.node, visited, bound_vars)
            }

            // Record set: max of field domains
            Expr::RecordSet(fields) => {
                let mut level = ExprLevel::Constant;
                for (_, domain) in fields {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &domain.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            // Tuple: max of elements
            Expr::Tuple(elems) => {
                let mut level = ExprLevel::Constant;
                for elem in elems {
                    level = level
                        .max(self.get_level_with_ctx_inner(ctx, &elem.node, visited, bound_vars));
                }
                level
            }

            // Cartesian product: max of sets
            Expr::Times(sets) => {
                let mut level = ExprLevel::Constant;
                for set in sets {
                    level = level
                        .max(self.get_level_with_ctx_inner(ctx, &set.node, visited, bound_vars));
                }
                level
            }

            // CASE: max of all guards and bodies
            Expr::Case(arms, other) => {
                let mut level = ExprLevel::Constant;
                for arm in arms {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &arm.guard.node,
                        visited,
                        bound_vars,
                    ));
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &arm.body.node,
                        visited,
                        bound_vars,
                    ));
                }
                if let Some(other_expr) = other {
                    level = level.max(self.get_level_with_ctx_inner(
                        ctx,
                        &other_expr.node,
                        visited,
                        bound_vars,
                    ));
                }
                level
            }

            Expr::Label(label) => {
                self.get_level_with_ctx_inner(ctx, &label.body.node, visited, bound_vars)
            }
        }
    }
}
