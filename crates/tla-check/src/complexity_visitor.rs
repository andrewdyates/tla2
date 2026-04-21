// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Init predicate complexity visitor.
//!
//! Extracted from `init_strategy.rs` (Part of #3509): walks the AST to detect
//! patterns that indicate a complex Init predicate requiring z4 SMT enumeration.

use rustc_hash::FxHashSet;
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget};

use crate::init_strategy::Z4Reason;

/// Visitor for analyzing Init expression complexity
pub(crate) struct ComplexityVisitor {
    vars: FxHashSet<String>,
    pub(crate) reasons: Vec<Z4Reason>,
}

impl ComplexityVisitor {
    pub(crate) fn new(vars: &[Arc<str>]) -> Self {
        ComplexityVisitor {
            vars: vars.iter().map(std::string::ToString::to_string).collect(),
            reasons: Vec::new(),
        }
    }

    pub(crate) fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            // Function set membership: x \in [S -> T]
            Expr::In(lhs, rhs) => {
                if let Some(var_name) = self.extract_var_name(&lhs.node) {
                    if self.is_function_set(&rhs.node) {
                        self.reasons
                            .push(Z4Reason::FunctionSetMembership { variable: var_name });
                    }
                }
                self.visit_expr(&lhs.node);
                self.visit_expr(&rhs.node);
            }

            // Set filter with complex predicate
            Expr::SetFilter(bound_var, predicate) => {
                // Check if predicate is complex (has nested quantifiers, etc.)
                if self.is_complex_predicate(&predicate.node) {
                    self.reasons.push(Z4Reason::ComplexSetFilter {
                        description: format!(
                            "filter on {} with complex predicate",
                            bound_var.name.node
                        ),
                    });
                }
                if let Some(domain) = &bound_var.domain {
                    self.visit_expr(&domain.node);
                }
                self.visit_expr(&predicate.node);
            }

            // Set builder - check for permutation patterns
            Expr::SetBuilder(elem_expr, bound_vars) => {
                // Pattern: { f(x) : x \in [S -> T], P(x) }
                // This is often used for permutation-like constructions
                for bv in bound_vars {
                    if let Some(domain) = &bv.domain {
                        if self.is_function_set(&domain.node) {
                            self.reasons.push(Z4Reason::PermutationPattern {
                                description: format!(
                                    "set builder over function set for {}",
                                    bv.name.node
                                ),
                            });
                        }
                    }
                }
                self.visit_expr(&elem_expr.node);
                for bv in bound_vars {
                    if let Some(domain) = &bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
            }

            // Operator application - check for known complex operators
            Expr::Apply(op_expr, args) => {
                if let Some(op_name) = self.extract_op_name(&op_expr.node) {
                    if self.is_complex_operator(&op_name) {
                        self.reasons
                            .push(Z4Reason::ComplexOperatorReference { operator: op_name });
                    }
                }
                self.visit_expr(&op_expr.node);
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }

            // Recurse into subexpressions
            Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            Expr::Not(a) => self.visit_expr(&a.node),
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                for bv in bounds {
                    if let Some(domain) = &bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.visit_expr(&body.node);
            }
            Expr::Choose(bv, body) => {
                if let Some(domain) = &bv.domain {
                    self.visit_expr(&domain.node);
                }
                self.visit_expr(&body.node);
            }
            Expr::Eq(a, b) | Expr::Neq(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            Expr::Union(a, b) | Expr::Intersect(a, b) | Expr::SetMinus(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            // Part of #3826: Detect nested SUBSET(SUBSET ...) which produces
            // doubly-exponential state space. The z4 NestedPowersetEncoder can
            // handle this efficiently using Boolean SAT variables.
            Expr::Powerset(inner) => {
                if self.is_nested_powerset_or_high_cardinality(&inner.node) {
                    self.reasons
                        .push(Z4Reason::NestedSubsetPattern {
                            description: "SUBSET(SUBSET ...) — doubly exponential state space"
                                .to_string(),
                        });
                }
                self.visit_expr(&inner.node);
            }
            Expr::BigUnion(a) => {
                self.visit_expr(&a.node);
            }
            Expr::SetEnum(elems) => {
                for e in elems {
                    self.visit_expr(&e.node);
                }
            }
            Expr::If(cond, then_e, else_e) => {
                self.visit_expr(&cond.node);
                self.visit_expr(&then_e.node);
                self.visit_expr(&else_e.node);
            }
            Expr::Let(_, body) => {
                self.visit_expr(&body.node);
            }
            Expr::Case(arms, other) => {
                for arm in arms {
                    self.visit_expr(&arm.guard.node);
                    self.visit_expr(&arm.body.node);
                }
                if let Some(o) = other {
                    self.visit_expr(&o.node);
                }
            }
            Expr::Tuple(elems) => {
                for e in elems {
                    self.visit_expr(&e.node);
                }
            }
            Expr::FuncDef(_, body) => {
                self.visit_expr(&body.node);
            }
            Expr::FuncApply(f, arg) => {
                self.visit_expr(&f.node);
                self.visit_expr(&arg.node);
            }
            Expr::Record(fields) | Expr::RecordSet(fields) => {
                for (_, e) in fields {
                    self.visit_expr(&e.node);
                }
            }
            Expr::RecordAccess(e, _) => {
                self.visit_expr(&e.node);
            }
            Expr::Except(base, updates) => {
                self.visit_expr(&base.node);
                for update in updates {
                    // ExceptSpec contains path and value
                    self.visit_expr(&update.value.node);
                }
            }

            // Terminal nodes - no recursion needed
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::Ident(_, _)
            | Expr::StateVar(_, _, _)
            | Expr::OpRef(_) => {}

            // Module references and other complex constructs
            Expr::ModuleRef(target, _, args) => {
                match target {
                    ModuleTarget::Parameterized(_, params) => {
                        for p in params {
                            self.visit_expr(&p.node);
                        }
                    }
                    ModuleTarget::Chained(base) => {
                        self.visit_expr(&base.node);
                    }
                    ModuleTarget::Named(_) => {}
                }
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }
            Expr::InstanceExpr(_, _) => {}
            Expr::SubstIn(subs, body) => {
                for sub in subs {
                    self.visit_expr(&sub.to.node);
                }
                self.visit_expr(&body.node);
            }
            Expr::Lambda(_, body) => {
                self.visit_expr(&body.node);
            }

            // Set operations
            Expr::NotIn(a, b) | Expr::Subseteq(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            Expr::Times(sets) => {
                // Cartesian product: S \X T \X U
                for s in sets {
                    self.visit_expr(&s.node);
                }
            }
            Expr::FuncSet(domain, range) => {
                self.visit_expr(&domain.node);
                self.visit_expr(&range.node);
            }
            Expr::Domain(e) => {
                self.visit_expr(&e.node);
            }

            // Arithmetic and comparison
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::Range(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            Expr::Neg(a) => self.visit_expr(&a.node),

            // Temporal (not typically in Init, but handle for completeness)
            Expr::Prime(e) | Expr::Enabled(e) | Expr::Always(e) | Expr::Eventually(e) => {
                self.visit_expr(&e.node);
            }
            Expr::LeadsTo(a, b) | Expr::StrongFair(a, b) | Expr::WeakFair(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }

            Expr::Unchanged(e) => {
                self.visit_expr(&e.node);
            }

            Expr::Label(label) => {
                self.visit_expr(&label.body.node);
            }
        }
    }

    /// Extract variable name from simple expressions
    fn extract_var_name(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Ident(name, _) if self.vars.contains(name) => Some(name.clone()),
            Expr::StateVar(name, _, _) if self.vars.contains(name) => Some(name.clone()),
            _ => None,
        }
    }

    /// Extract operator name from expressions
    fn extract_op_name(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Ident(name, _) => Some(name.clone()),
            Expr::StateVar(name, _, _) => Some(name.clone()),
            _ => None,
        }
    }

    /// Check if expression is a function set: [S -> T]
    fn is_function_set(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::FuncSet(_, _))
    }

    /// Check if predicate is complex (nested quantifiers, etc.)
    #[allow(clippy::only_used_in_recursion)]
    fn is_complex_predicate(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Forall(_, _) | Expr::Exists(_, _) => true,
            Expr::And(a, b) | Expr::Or(a, b) => {
                self.is_complex_predicate(&a.node) || self.is_complex_predicate(&b.node)
            }
            Expr::Not(a) => self.is_complex_predicate(&a.node),
            _ => false,
        }
    }

    /// Check whether an expression is a Powerset or represents a high-cardinality
    /// set that would make SUBSET of it doubly exponential.
    ///
    /// Part of #3826.
    fn is_nested_powerset_or_high_cardinality(&self, expr: &Expr) -> bool {
        match expr {
            // Nested SUBSET: SUBSET(SUBSET X) is doubly exponential.
            Expr::Powerset(_) => true,
            // Set enumeration with many elements: SUBSET {a, b, ..., z}.
            Expr::SetEnum(elems) if elems.len() > 16 => true,
            // Cartesian product: SUBSET (S \X T \X ...) — product of domains.
            Expr::Times(factors) if factors.len() >= 3 => true,
            // RecordSet: SUBSET [a : S, b : T, ...] — like Cartesian product.
            Expr::RecordSet(fields) if fields.len() >= 3 => true,
            _ => false,
        }
    }

    /// Check if operator is known to be complex for enumeration
    fn is_complex_operator(&self, name: &str) -> bool {
        matches!(
            name,
            "Permutation"
                | "Permutations"
                | "PermutationsOf"
                | "BoundedSeq"
                | "AllMappings"
                | "Injections"
                | "Surjections"
                | "Bijections"
        )
    }
}
