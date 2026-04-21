// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::ast::{BoundVar, Expr};
use tla_core::span::Spanned;

impl TypeContext {
    /// Infer type for an expression
    pub fn infer_expr(&mut self, expr: &Spanned<Expr>) -> TlaType {
        match &expr.node {
            // Literals
            Expr::Bool(_) => TlaType::Bool,
            Expr::Int(_) => TlaType::Int,
            Expr::String(_) => TlaType::String,

            // Variables
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                if let Some(ty) = self.lookup_var(name) {
                    return ty.clone();
                }

                // Check for built-in constants
                match name.as_str() {
                    "TRUE" | "FALSE" => TlaType::Bool,
                    "BOOLEAN" => TlaType::Set(Box::new(TlaType::Bool)),
                    "Nat" | "Int" => TlaType::Set(Box::new(TlaType::Int)),
                    "STRING" => TlaType::Set(Box::new(TlaType::String)),
                    _ => self.ops.get(name).cloned().unwrap_or_else(|| {
                        self.error(TypeInferError::UnknownIdent(name.clone()));
                        TlaType::Unknown
                    }),
                }
            }

            // Logic
            Expr::And(a, b) | Expr::Or(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Bool
            }
            Expr::Not(a) => {
                self.infer_expr(a);
                TlaType::Bool
            }
            Expr::Implies(a, b) | Expr::Equiv(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Bool
            }

            // Comparison
            Expr::Eq(a, b) | Expr::Neq(a, b) => {
                let ty_a = self.infer_expr(a);
                let ty_b = self.infer_expr(b);
                // Propagate types: if one side is a variable with unresolved type,
                // update it to match the other side's concrete type
                self.try_unify_with_var(&a.node, &ty_b);
                self.try_unify_with_var(&b.node, &ty_a);
                TlaType::Bool
            }
            Expr::Lt(a, b) | Expr::Leq(a, b) | Expr::Gt(a, b) | Expr::Geq(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Bool
            }

            // Arithmetic
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Int
            }
            Expr::IntDiv(a, b) | Expr::Mod(a, b) | Expr::Pow(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Int
            }
            Expr::Neg(a) => {
                self.infer_expr(a);
                TlaType::Int
            }
            Expr::Range(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Set(Box::new(TlaType::Int))
            }

            // Sets
            Expr::SetEnum(elems) => {
                if elems.is_empty() {
                    TlaType::Set(Box::new(self.fresh_var()))
                } else {
                    let elem_type = self.infer_expr(&elems[0]);
                    for elem in elems.iter().skip(1) {
                        self.infer_expr(elem);
                    }
                    TlaType::Set(Box::new(elem_type))
                }
            }
            Expr::In(elem, set) | Expr::NotIn(elem, set) => {
                self.infer_expr(elem);
                let set_ty = self.infer_expr(set);
                // If set has type Set(T), then elem should have type T
                if let TlaType::Set(elem_ty) = set_ty {
                    self.try_unify_with_var(&elem.node, &elem_ty);
                }
                TlaType::Bool
            }
            Expr::Subseteq(a, b) => {
                self.infer_expr(a);
                self.infer_expr(b);
                TlaType::Bool
            }
            Expr::Union(a, b) | Expr::Intersect(a, b) | Expr::SetMinus(a, b) => {
                let ta = self.infer_expr(a);
                self.infer_expr(b);
                ta
            }
            Expr::Powerset(s) => {
                let inner = self.infer_expr(s);
                TlaType::Set(Box::new(inner))
            }
            Expr::BigUnion(s) => {
                // UNION {{1,2}, {3}} has type Set(Int) if s has type Set(Set(Int))
                let s_type = self.infer_expr(s);
                if let TlaType::Set(inner) = s_type {
                    if let TlaType::Set(elem) = *inner {
                        TlaType::Set(elem)
                    } else {
                        TlaType::Unknown
                    }
                } else {
                    TlaType::Unknown
                }
            }
            Expr::SetBuilder(body, bounds) => {
                for bound in bounds {
                    self.bind_bound_var(bound);
                }
                let elem_type = self.infer_expr(body);
                TlaType::Set(Box::new(elem_type))
            }
            Expr::SetFilter(bound, pred) => {
                let elem_type = self.bind_bound_var(bound);
                self.infer_expr(pred);
                TlaType::Set(Box::new(elem_type))
            }

            // Tuples and sequences
            Expr::Tuple(elems) => {
                let types: Vec<_> = elems.iter().map(|e| self.infer_expr(e)).collect();
                TlaType::Tuple(types)
            }
            Expr::Times(sets) => {
                let types: Vec<_> = sets
                    .iter()
                    .map(|s| {
                        let st = self.infer_expr(s);
                        if let TlaType::Set(inner) = st {
                            *inner
                        } else {
                            TlaType::Unknown
                        }
                    })
                    .collect();
                TlaType::Set(Box::new(TlaType::Tuple(types)))
            }

            // Records
            Expr::Record(fields) => {
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|(name, val)| (name.node.clone(), self.infer_expr(val)))
                    .collect();
                TlaType::Record(field_types)
            }
            Expr::RecordAccess(rec, field) => {
                let rec_type = self.infer_expr(rec);
                if let TlaType::Record(fields) = rec_type {
                    // Find field type
                    for (name, ty) in &fields {
                        if name == &field.name.node {
                            return ty.clone();
                        }
                    }
                }
                TlaType::Unknown
            }
            Expr::RecordSet(fields) => {
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|(name, set)| {
                        let set_type = self.infer_expr(set);
                        let elem_type = if let TlaType::Set(inner) = set_type {
                            *inner
                        } else {
                            TlaType::Unknown
                        };
                        (name.node.clone(), elem_type)
                    })
                    .collect();
                TlaType::Set(Box::new(TlaType::Record(field_types)))
            }

            // Functions
            Expr::FuncDef(bounds, body) => {
                let mut domain_types = Vec::new();
                for bound in bounds {
                    domain_types.push(self.bind_bound_var(bound));
                }
                let range_type = self.infer_expr(body);

                let domain_type = if domain_types.len() == 1 {
                    domain_types.pop().expect("len checked == 1")
                } else {
                    TlaType::Tuple(domain_types)
                };

                TlaType::Func(Box::new(domain_type), Box::new(range_type))
            }
            Expr::FuncApply(func, arg) => {
                let func_type = self.infer_expr(func);
                self.infer_expr(arg);
                if let TlaType::Func(_, range) = func_type {
                    *range
                } else {
                    TlaType::Unknown
                }
            }
            Expr::Domain(func) => {
                let func_type = self.infer_expr(func);
                if let TlaType::Func(domain, _) = func_type {
                    TlaType::Set(domain)
                } else {
                    TlaType::Unknown
                }
            }
            Expr::FuncSet(domain, range) => {
                let domain_type = self.infer_expr(domain);
                let range_type = self.infer_expr(range);
                let d = if let TlaType::Set(inner) = domain_type {
                    *inner
                } else {
                    TlaType::Unknown
                };
                let r = if let TlaType::Set(inner) = range_type {
                    *inner
                } else {
                    TlaType::Unknown
                };
                TlaType::Set(Box::new(TlaType::Func(Box::new(d), Box::new(r))))
            }
            Expr::Except(func, _specs) => self.infer_expr(func),

            // Quantifiers
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                for bound in bounds {
                    self.bind_bound_var(bound);
                }
                self.infer_expr(body);
                TlaType::Bool
            }
            Expr::Choose(bound, body) => {
                let elem_type = self.bind_bound_var(bound);
                self.infer_expr(body);
                elem_type
            }

            // Control
            Expr::If(cond, then_e, else_e) => {
                self.infer_expr(cond);
                let t1 = self.infer_expr(then_e);
                self.infer_expr(else_e);
                t1
            }
            Expr::Case(arms, other) => {
                let ty = if let Some(arm) = arms.first() {
                    self.infer_expr(&arm.guard);
                    self.infer_expr(&arm.body)
                } else {
                    TlaType::Unknown
                };
                for arm in arms.iter().skip(1) {
                    self.infer_expr(&arm.guard);
                    self.infer_expr(&arm.body);
                }
                if let Some(other_expr) = other {
                    self.infer_expr(other_expr);
                }
                ty
            }
            Expr::Let(defs, body) => {
                for def in defs {
                    self.infer_operator(def);
                }
                self.infer_expr(body)
            }
            Expr::Lambda(params, body) => {
                for param in params {
                    let fresh = self.fresh_var();
                    self.bind_var(&param.node, fresh);
                }
                self.infer_expr(body)
            }
            Expr::Label(label) => self.infer_expr(&label.body),
            Expr::Apply(op, args) => {
                let op_ty = self.infer_expr(op);
                for arg in args {
                    self.infer_expr(arg);
                }
                op_ty
            }

            // Prime is used in Next actions - the type of x' is the type of x
            Expr::Prime(inner) => self.infer_expr(inner),
            Expr::Always(_) | Expr::Eventually(_) | Expr::LeadsTo(_, _) => {
                self.error(TypeInferError::Unsupported(
                    "temporal operators".to_string(),
                ));
                TlaType::Unknown
            }
            Expr::WeakFair(_, _) | Expr::StrongFair(_, _) => {
                self.error(TypeInferError::Unsupported("fairness".to_string()));
                TlaType::Unknown
            }
            Expr::Enabled(_) => {
                self.error(TypeInferError::Unsupported("ENABLED".to_string()));
                TlaType::Unknown
            }
            Expr::Unchanged(_) => TlaType::Bool,
            Expr::ModuleRef(_, _, args) => {
                // ModuleRef that survived INSTANCE expansion — infer arg types
                // for side effects but return Unknown without error. The emitter
                // falls back to TlaValue for Unknown types.
                for arg in args {
                    self.infer_expr(arg);
                }
                TlaType::Unknown
            }
            Expr::InstanceExpr(_, _) => {
                // InstanceExpr that survived expansion is an operator definition
                // body, not an expression to evaluate. Skip silently.
                TlaType::Unknown
            }
            Expr::SubstIn(_, body) => self.infer_expr(body),
            Expr::OpRef(op) => {
                self.error(TypeInferError::Unsupported(format!(
                    "operator reference ({})",
                    op
                )));
                TlaType::Unknown
            }
        }
    }

    /// Bind a bound variable and return its type
    fn bind_bound_var(&mut self, bound: &BoundVar) -> TlaType {
        let elem_type = if let Some(domain) = &bound.domain {
            let domain_type = self.infer_expr(domain);
            if let TlaType::Set(inner) = domain_type {
                *inner
            } else {
                self.fresh_var()
            }
        } else {
            self.fresh_var()
        };
        self.bind_var(&bound.name.node, elem_type.clone());
        elem_type
    }

    /// Try to unify a variable with a concrete type.
    /// If the expression is an identifier with unresolved type, update it.
    fn try_unify_with_var(&mut self, expr: &Expr, ty: &TlaType) {
        // Only unify if the type is concrete (resolved)
        if !ty.is_resolved() {
            return;
        }

        if let Expr::Ident(name, _) = expr {
            if let Some(existing) = self.vars.get(name) {
                // Only update if existing type is unresolved (a type variable)
                if !existing.is_resolved() {
                    self.vars.insert(name.clone(), ty.clone());
                }
            }
        }
    }
}
