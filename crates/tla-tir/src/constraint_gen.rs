// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint generation pass over TIR expressions for type inference.
//!
//! Walks the TIR expression tree and generates unification constraints for the
//! `TypeUnifier`. This implements a Hindley-Milner style inference engine with
//! support for:
//!
//! - Polymorphic LET-definitions (generalize + instantiate)
//! - Row-polymorphic records (OpenRecord + row variables)
//! - Variant/sum types
//! - Gradual typing (Dyn as escape hatch)
//!
//! Part of #3750: Apalache Gap 2 — Full Type Checker.

use std::collections::{HashMap, HashSet};

use tla_core::NameId;

use crate::nodes::{TirBoundVar, TirCmpOp, TirExceptPathElement, TirExpr, TirLetDef};
use crate::types::TirType;
use crate::unify::{TypeScheme, TypeUnifier};

/// Type environment for constraint generation.
///
/// Tracks types for all in-scope names: state variables, constants, bound
/// variables, and operator definitions.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    /// Monomorphic bindings: variables, constants, bound vars.
    mono: HashMap<String, TirType>,
    /// Polymorphic bindings: LET-defined operators with type schemes.
    poly: HashMap<String, TypeScheme>,
}

impl TypeEnv {
    /// Create an empty environment.
    pub fn new() -> Self {
        Self {
            mono: HashMap::new(),
            poly: HashMap::new(),
        }
    }

    /// Add a monomorphic binding.
    pub fn bind_mono(&mut self, name: String, ty: TirType) {
        self.mono.insert(name, ty);
    }

    /// Add a polymorphic binding.
    pub fn bind_poly(&mut self, name: String, scheme: TypeScheme) {
        self.poly.insert(name, scheme);
    }

    /// Look up a name. Returns a type (instantiating poly bindings with fresh vars).
    pub fn lookup(&self, name: &str, unifier: &mut TypeUnifier) -> Option<TirType> {
        if let Some(ty) = self.mono.get(name) {
            return Some(ty.clone());
        }
        if let Some(scheme) = self.poly.get(name) {
            return Some(unifier.instantiate(scheme));
        }
        None
    }

    /// Collect all free type variables in the monomorphic environment.
    pub fn free_vars(&self) -> HashSet<u32> {
        let mut vars = HashSet::new();
        for ty in self.mono.values() {
            vars.extend(ty.free_vars());
        }
        vars
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// Constraint generator: walks TIR and feeds constraints to the unifier.
pub struct ConstraintGenerator {
    /// The unifier that solves type constraints.
    pub unifier: TypeUnifier,
    /// Current type environment.
    env: TypeEnv,
}

impl ConstraintGenerator {
    /// Create a new constraint generator with an empty environment.
    pub fn new() -> Self {
        Self {
            unifier: TypeUnifier::new(),
            env: TypeEnv::new(),
        }
    }

    /// Create a constraint generator with a pre-populated environment.
    pub fn with_env(env: TypeEnv) -> Self {
        Self {
            unifier: TypeUnifier::new(),
            env,
        }
    }

    /// Seed the environment with state variable names (assigned fresh type vars).
    pub fn add_variable(&mut self, name: &str) -> TirType {
        let tv = self.unifier.fresh_var();
        self.env.bind_mono(name.to_string(), tv.clone());
        tv
    }

    /// Seed the environment with constant names (assigned fresh type vars).
    pub fn add_constant(&mut self, name: &str) -> TirType {
        let tv = self.unifier.fresh_var();
        self.env.bind_mono(name.to_string(), tv.clone());
        tv
    }

    /// Infer the type of a TIR expression, generating unification constraints.
    ///
    /// Returns the inferred type (which may contain unresolved type variables).
    /// Call `unifier.resolve()` to get the fully resolved type after all
    /// constraints have been generated.
    pub fn infer(&mut self, expr: &TirExpr) -> TirType {
        match expr {
            // --- Literals ---
            TirExpr::Const { ty, .. } => {
                if *ty == TirType::Dyn {
                    // For untyped constants, allocate a fresh var.
                    self.unifier.fresh_var()
                } else {
                    ty.clone()
                }
            }

            // --- Names ---
            TirExpr::Name(name_ref) => {
                if let Some(env_ty) = self.env.lookup(&name_ref.name, &mut self.unifier) {
                    // Unify with the TIR-provided type hint if it's concrete.
                    if name_ref.ty != TirType::Dyn {
                        let _ = self.unifier.unify(&env_ty, &name_ref.ty, None);
                    }
                    env_ty
                } else if name_ref.ty != TirType::Dyn {
                    name_ref.ty.clone()
                } else {
                    self.unifier.fresh_var()
                }
            }

            // --- Arithmetic ---
            TirExpr::ArithBinOp { left, right, .. } => {
                let lt = self.infer(&left.node);
                let rt = self.infer(&right.node);
                let _ = self.unifier.unify(&lt, &TirType::Int, None);
                let _ = self.unifier.unify(&rt, &TirType::Int, None);
                TirType::Int
            }
            TirExpr::ArithNeg(inner) => {
                let t = self.infer(&inner.node);
                let _ = self.unifier.unify(&t, &TirType::Int, None);
                TirType::Int
            }

            // --- Boolean ---
            TirExpr::BoolBinOp { left, right, .. } => {
                let lt = self.infer(&left.node);
                let rt = self.infer(&right.node);
                let _ = self.unifier.unify(&lt, &TirType::Bool, None);
                let _ = self.unifier.unify(&rt, &TirType::Bool, None);
                TirType::Bool
            }
            TirExpr::BoolNot(inner) => {
                let t = self.infer(&inner.node);
                let _ = self.unifier.unify(&t, &TirType::Bool, None);
                TirType::Bool
            }

            // --- Comparisons ---
            TirExpr::Cmp { left, op, right } => {
                let lt = self.infer(&left.node);
                let rt = self.infer(&right.node);
                match op {
                    // Equality/inequality: operands must be the same type.
                    TirCmpOp::Eq | TirCmpOp::Neq => {
                        let _ = self.unifier.unify(&lt, &rt, None);
                    }
                    // Ordering: operands must be Int.
                    TirCmpOp::Lt | TirCmpOp::Leq | TirCmpOp::Gt | TirCmpOp::Geq => {
                        let _ = self.unifier.unify(&lt, &TirType::Int, None);
                        let _ = self.unifier.unify(&rt, &TirType::Int, None);
                    }
                }
                TirType::Bool
            }

            // --- Set membership ---
            TirExpr::In { elem, set } => {
                let elem_ty = self.infer(&elem.node);
                let set_ty = self.infer(&set.node);
                let _ = self
                    .unifier
                    .unify(&set_ty, &TirType::Set(Box::new(elem_ty)), None);
                TirType::Bool
            }
            TirExpr::Subseteq { left, right } => {
                let lt = self.infer(&left.node);
                let rt = self.infer(&right.node);
                let _ = self.unifier.unify(&lt, &rt, None);
                // Both should be sets.
                let elem_var = self.unifier.fresh_var();
                let _ = self
                    .unifier
                    .unify(&lt, &TirType::Set(Box::new(elem_var)), None);
                TirType::Bool
            }

            // --- Sets ---
            TirExpr::SetEnum(elems) => {
                if elems.is_empty() {
                    TirType::Set(Box::new(self.unifier.fresh_var()))
                } else {
                    let elem_ty = self.unifier.fresh_var();
                    for e in elems {
                        let et = self.infer(&e.node);
                        let _ = self.unifier.unify(&et, &elem_ty, None);
                    }
                    TirType::Set(Box::new(elem_ty))
                }
            }
            TirExpr::SetFilter { var, body } => {
                let (bound_name, domain_ty) = self.infer_bound_var(var);
                let old = self.env.mono.insert(bound_name.clone(), domain_ty.clone());
                let body_ty = self.infer(&body.node);
                let _ = self.unifier.unify(&body_ty, &TirType::Bool, None);
                // Restore environment.
                if let Some(prev) = old {
                    self.env.mono.insert(bound_name, prev);
                } else {
                    self.env.mono.remove(&bound_name);
                }
                TirType::Set(Box::new(domain_ty))
            }
            TirExpr::SetBuilder { body, vars } => {
                let mut saved: Vec<(String, Option<TirType>)> = Vec::new();
                for v in vars {
                    let (name, dom_ty) = self.infer_bound_var(v);
                    let old = self.env.mono.insert(name.clone(), dom_ty);
                    saved.push((name, old));
                }
                let body_ty = self.infer(&body.node);
                // Restore environment.
                for (name, old) in saved {
                    if let Some(prev) = old {
                        self.env.mono.insert(name, prev);
                    } else {
                        self.env.mono.remove(&name);
                    }
                }
                TirType::Set(Box::new(body_ty))
            }
            TirExpr::SetBinOp { left, op: _, right } => {
                let lt = self.infer(&left.node);
                let rt = self.infer(&right.node);
                let _ = self.unifier.unify(&lt, &rt, None);
                lt
            }
            TirExpr::Powerset(inner) => {
                let inner_ty = self.infer(&inner.node);
                TirType::Set(Box::new(inner_ty))
            }
            TirExpr::BigUnion(inner) => {
                let inner_ty = self.infer(&inner.node);
                let elem_var = self.unifier.fresh_var();
                let expected = TirType::Set(Box::new(TirType::Set(Box::new(elem_var.clone()))));
                let _ = self.unifier.unify(&inner_ty, &expected, None);
                TirType::Set(Box::new(elem_var))
            }
            TirExpr::KSubset { base, k } => {
                let base_ty = self.infer(&base.node);
                let k_ty = self.infer(&k.node);
                let _ = self.unifier.unify(&k_ty, &TirType::Int, None);
                TirType::Set(Box::new(base_ty))
            }

            // --- Ranges ---
            TirExpr::Range { lo, hi } => {
                let lo_ty = self.infer(&lo.node);
                let hi_ty = self.infer(&hi.node);
                let _ = self.unifier.unify(&lo_ty, &TirType::Int, None);
                let _ = self.unifier.unify(&hi_ty, &TirType::Int, None);
                TirType::Set(Box::new(TirType::Int))
            }

            // --- Functions ---
            TirExpr::FuncDef { vars, body } => {
                let mut saved: Vec<(String, Option<TirType>)> = Vec::new();
                let mut dom_types = Vec::new();
                for v in vars {
                    let (name, dom_ty) = self.infer_bound_var(v);
                    dom_types.push(dom_ty.clone());
                    let old = self.env.mono.insert(name.clone(), dom_ty);
                    saved.push((name, old));
                }
                let body_ty = self.infer(&body.node);
                // Restore environment.
                for (name, old) in saved {
                    if let Some(prev) = old {
                        self.env.mono.insert(name, prev);
                    } else {
                        self.env.mono.remove(&name);
                    }
                }
                let dom = if dom_types.len() == 1 {
                    dom_types.into_iter().next().unwrap()
                } else {
                    TirType::Tuple(dom_types)
                };
                TirType::Func(Box::new(dom), Box::new(body_ty))
            }
            TirExpr::FuncApply { func, arg } => {
                let func_ty = self.infer(&func.node);
                let arg_ty = self.infer(&arg.node);
                let ret_var = self.unifier.fresh_var();
                let expected_func = TirType::Func(Box::new(arg_ty), Box::new(ret_var.clone()));
                let _ = self.unifier.unify(&func_ty, &expected_func, None);
                ret_var
            }
            TirExpr::FuncSet { domain, range } => {
                let dom_ty = self.infer(&domain.node);
                let rng_ty = self.infer(&range.node);
                let dom_elem = self.unifier.fresh_var();
                let rng_elem = self.unifier.fresh_var();
                let _ =
                    self.unifier
                        .unify(&dom_ty, &TirType::Set(Box::new(dom_elem.clone())), None);
                let _ =
                    self.unifier
                        .unify(&rng_ty, &TirType::Set(Box::new(rng_elem.clone())), None);
                TirType::Set(Box::new(TirType::Func(
                    Box::new(dom_elem),
                    Box::new(rng_elem),
                )))
            }
            TirExpr::Domain(inner) => {
                let inner_ty = self.infer(&inner.node);
                let dom_var = self.unifier.fresh_var();
                let rng_var = self.unifier.fresh_var();
                let expected = TirType::Func(Box::new(dom_var.clone()), Box::new(rng_var));
                let _ = self.unifier.unify(&inner_ty, &expected, None);
                TirType::Set(Box::new(dom_var))
            }

            // --- Records ---
            TirExpr::Record(fields) => {
                let typed_fields: Vec<(NameId, TirType)> = fields
                    .iter()
                    .map(|(f, e)| (f.field_id, self.infer(&e.node)))
                    .collect();
                TirType::Record(typed_fields)
            }
            TirExpr::RecordSet(fields) => {
                let typed_fields: Vec<(NameId, TirType)> = fields
                    .iter()
                    .map(|(f, e)| {
                        let set_ty = self.infer(&e.node);
                        let elem_var = self.unifier.fresh_var();
                        let _ = self.unifier.unify(
                            &set_ty,
                            &TirType::Set(Box::new(elem_var.clone())),
                            None,
                        );
                        (f.field_id, elem_var)
                    })
                    .collect();
                TirType::Set(Box::new(TirType::Record(typed_fields)))
            }
            TirExpr::RecordAccess { record, field } => {
                let rec_ty = self.infer(&record.node);
                let field_var = self.unifier.fresh_var();
                // Create an open record with just this field + row variable.
                let row = match self.unifier.fresh_var() {
                    TirType::Var(id) => id,
                    _ => unreachable!(),
                };
                let expected = TirType::OpenRecord(vec![(field.field_id, field_var.clone())], row);
                let _ = self.unifier.unify(&rec_ty, &expected, None);
                field_var
            }

            // --- Tuples ---
            TirExpr::Tuple(elems) => {
                let elem_types: Vec<TirType> = elems.iter().map(|e| self.infer(&e.node)).collect();
                TirType::Tuple(elem_types)
            }
            TirExpr::Times(elems) => {
                let elem_types: Vec<TirType> = elems
                    .iter()
                    .map(|e| {
                        let set_ty = self.infer(&e.node);
                        let elem_var = self.unifier.fresh_var();
                        let _ = self.unifier.unify(
                            &set_ty,
                            &TirType::Set(Box::new(elem_var.clone())),
                            None,
                        );
                        elem_var
                    })
                    .collect();
                TirType::Set(Box::new(TirType::Tuple(elem_types)))
            }

            // --- Control flow ---
            TirExpr::If { cond, then_, else_ } => {
                let cond_ty = self.infer(&cond.node);
                let _ = self.unifier.unify(&cond_ty, &TirType::Bool, None);
                let then_ty = self.infer(&then_.node);
                let else_ty = self.infer(&else_.node);
                let _ = self.unifier.unify(&then_ty, &else_ty, None);
                then_ty
            }
            TirExpr::Case { arms, other } => {
                let result_var = self.unifier.fresh_var();
                for arm in arms {
                    let guard_ty = self.infer(&arm.guard.node);
                    let _ = self.unifier.unify(&guard_ty, &TirType::Bool, None);
                    let body_ty = self.infer(&arm.body.node);
                    let _ = self.unifier.unify(&body_ty, &result_var, None);
                }
                if let Some(other_expr) = other {
                    let other_ty = self.infer(&other_expr.node);
                    let _ = self.unifier.unify(&other_ty, &result_var, None);
                }
                result_var
            }

            // --- Quantifiers ---
            TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
                let mut saved: Vec<(String, Option<TirType>)> = Vec::new();
                for v in vars {
                    let (name, dom_ty) = self.infer_bound_var(v);
                    let old = self.env.mono.insert(name.clone(), dom_ty);
                    saved.push((name, old));
                }
                let body_ty = self.infer(&body.node);
                let _ = self.unifier.unify(&body_ty, &TirType::Bool, None);
                for (name, old) in saved {
                    if let Some(prev) = old {
                        self.env.mono.insert(name, prev);
                    } else {
                        self.env.mono.remove(&name);
                    }
                }
                TirType::Bool
            }
            TirExpr::Choose { var, body } => {
                let (name, dom_ty) = self.infer_bound_var(var);
                let old = self.env.mono.insert(name.clone(), dom_ty.clone());
                let body_ty = self.infer(&body.node);
                let _ = self.unifier.unify(&body_ty, &TirType::Bool, None);
                if let Some(prev) = old {
                    self.env.mono.insert(name, prev);
                } else {
                    self.env.mono.remove(&name);
                }
                dom_ty
            }

            // --- LET/IN with polymorphic generalization ---
            TirExpr::Let { defs, body } => {
                let saved_mono: Vec<(String, Option<TirType>)> = Vec::new();
                let mut saved_poly: Vec<(String, Option<TypeScheme>)> = Vec::new();

                for def in defs {
                    let def_ty = self.infer_let_def(def);
                    // Generalize: quantify over variables not in the environment.
                    let env_vars = self.env.free_vars();
                    let scheme = self.unifier.generalize(&def_ty, &env_vars);

                    let old = self.env.poly.insert(def.name.clone(), scheme);
                    saved_poly.push((def.name.clone(), old));
                }
                let body_ty = self.infer(&body.node);

                // Restore environment.
                for (name, old) in saved_poly {
                    if let Some(prev) = old {
                        self.env.poly.insert(name, prev);
                    } else {
                        self.env.poly.remove(&name);
                    }
                }
                for (name, old) in saved_mono {
                    if let Some(prev) = old {
                        self.env.mono.insert(name, prev);
                    } else {
                        self.env.mono.remove(&name);
                    }
                }

                body_ty
            }

            // --- EXCEPT ---
            TirExpr::Except { base, specs } => {
                let base_ty = self.infer(&base.node);
                for spec in specs {
                    self.infer(&spec.value.node);
                    for path_elem in &spec.path {
                        if let TirExceptPathElement::Index(idx) = path_elem {
                            self.infer(&idx.node);
                        }
                    }
                }
                base_ty
            }
            TirExpr::ExceptAt => self.unifier.fresh_var(),

            // --- Actions/temporal (return Bool) ---
            TirExpr::Unchanged(inner) => {
                self.infer(&inner.node);
                TirType::Bool
            }
            TirExpr::ActionSubscript {
                action, subscript, ..
            } => {
                self.infer(&action.node);
                self.infer(&subscript.node);
                TirType::Bool
            }
            TirExpr::Always(inner) | TirExpr::Eventually(inner) | TirExpr::Enabled(inner) => {
                self.infer(&inner.node);
                TirType::Bool
            }
            TirExpr::LeadsTo { left, right }
            | TirExpr::WeakFair {
                vars: left,
                action: right,
            }
            | TirExpr::StrongFair {
                vars: left,
                action: right,
            } => {
                self.infer(&left.node);
                self.infer(&right.node);
                TirType::Bool
            }
            TirExpr::Prime(inner) => self.infer(&inner.node),

            // --- Generic apply ---
            TirExpr::Apply { op, args } => {
                self.infer(&op.node);
                for a in args {
                    self.infer(&a.node);
                }
                self.unifier.fresh_var()
            }

            // --- Lambda ---
            TirExpr::Lambda { params, body, .. } => {
                let mut saved: Vec<(String, Option<TirType>)> = Vec::new();
                let mut param_types = Vec::new();
                for p in params {
                    let ptv = self.unifier.fresh_var();
                    param_types.push(ptv.clone());
                    let old = self.env.mono.insert(p.clone(), ptv);
                    saved.push((p.clone(), old));
                }
                let body_ty = self.infer(&body.node);
                for (name, old) in saved {
                    if let Some(prev) = old {
                        self.env.mono.insert(name, prev);
                    } else {
                        self.env.mono.remove(&name);
                    }
                }
                let dom = if param_types.len() == 1 {
                    param_types.into_iter().next().unwrap()
                } else {
                    TirType::Tuple(param_types)
                };
                TirType::Func(Box::new(dom), Box::new(body_ty))
            }

            // --- Operator ref ---
            TirExpr::OperatorRef(op_ref) => {
                for seg in &op_ref.path {
                    for a in &seg.args {
                        self.infer(&a.node);
                    }
                }
                for a in &op_ref.args {
                    self.infer(&a.node);
                }
                self.unifier.fresh_var()
            }

            // --- Leaves ---
            TirExpr::OpRef(_) => self.unifier.fresh_var(),
            TirExpr::Label { body, .. } => self.infer(&body.node),
        }
    }

    /// Infer the type of a LET definition body, handling parameters.
    fn infer_let_def(&mut self, def: &TirLetDef) -> TirType {
        if def.params.is_empty() {
            // Simple definition: just infer the body.
            self.infer(&def.body.node)
        } else {
            // Parameterized definition: bind params to fresh vars.
            let mut saved: Vec<(String, Option<TirType>)> = Vec::new();
            let mut param_types = Vec::new();
            for p in &def.params {
                let ptv = self.unifier.fresh_var();
                param_types.push(ptv.clone());
                let old = self.env.mono.insert(p.clone(), ptv);
                saved.push((p.clone(), old));
            }
            let body_ty = self.infer(&def.body.node);
            for (name, old) in saved {
                if let Some(prev) = old {
                    self.env.mono.insert(name, prev);
                } else {
                    self.env.mono.remove(&name);
                }
            }
            let dom = if param_types.len() == 1 {
                param_types.into_iter().next().unwrap()
            } else {
                TirType::Tuple(param_types)
            };
            TirType::Func(Box::new(dom), Box::new(body_ty))
        }
    }

    /// Infer the element type from a bound variable's domain.
    ///
    /// Returns `(variable_name, element_type)`.
    fn infer_bound_var(&mut self, var: &TirBoundVar) -> (String, TirType) {
        let elem_ty = if let Some(domain) = &var.domain {
            let dom_ty = self.infer(&domain.node);
            let elem_var = self.unifier.fresh_var();
            let _ = self
                .unifier
                .unify(&dom_ty, &TirType::Set(Box::new(elem_var.clone())), None);
            elem_var
        } else {
            self.unifier.fresh_var()
        };
        (var.name.clone(), elem_ty)
    }

    /// Get a reference to the unifier.
    pub fn unifier(&self) -> &TypeUnifier {
        &self.unifier
    }

    /// Get a mutable reference to the unifier.
    pub fn unifier_mut(&mut self) -> &mut TypeUnifier {
        &mut self.unifier
    }

    /// Get a reference to the environment.
    pub fn env(&self) -> &TypeEnv {
        &self.env
    }
}

impl Default for ConstraintGenerator {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::*;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
    use tla_core::Spanned;
    use tla_value::Value;

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn bool_const(b: bool) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        })
    }

    fn str_const(s: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::string(s),
            ty: TirType::Str,
        })
    }

    fn name_ref(name: &str, ty: TirType) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty,
        }))
    }

    fn set_of_ints() -> Spanned<TirExpr> {
        spanned(TirExpr::SetEnum(vec![int_const(1), int_const(2)]))
    }

    #[test]
    fn test_arith_constraints() {
        let mut cg = ConstraintGenerator::new();
        let expr = TirExpr::ArithBinOp {
            left: Box::new(int_const(1)),
            op: TirArithOp::Add,
            right: Box::new(int_const(2)),
        };
        let ty = cg.infer(&expr);
        let resolved = cg.unifier.resolve(&ty);
        assert_eq!(resolved, TirType::Int);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_set_membership_constraints() {
        let mut cg = ConstraintGenerator::new();
        // 1 \in {1, 2}: elem is Int, set is Set(Int), should unify cleanly.
        let expr = TirExpr::In {
            elem: Box::new(int_const(1)),
            set: Box::new(set_of_ints()),
        };
        let ty = cg.infer(&expr);
        assert_eq!(cg.unifier.resolve(&ty), TirType::Bool);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_function_application() {
        let mut cg = ConstraintGenerator::new();
        // Build: [x \in {1,2} |-> TRUE][1]
        let bound = TirBoundVar {
            name: "x".to_string(),
            name_id: intern_name("x"),
            domain: Some(Box::new(set_of_ints())),
            pattern: None,
        };
        let func = spanned(TirExpr::FuncDef {
            vars: vec![bound],
            body: Box::new(bool_const(true)),
        });
        let expr = TirExpr::FuncApply {
            func: Box::new(func),
            arg: Box::new(int_const(1)),
        };
        let ty = cg.infer(&expr);
        let resolved = cg.unifier.resolve(&ty);
        assert_eq!(resolved, TirType::Bool);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_record_access() {
        let mut cg = ConstraintGenerator::new();
        let id_x = intern_name("x");
        let id_y = intern_name("y");
        // Build: [x |-> 1, y |-> TRUE].x
        let rec = spanned(TirExpr::Record(vec![
            (
                TirFieldName {
                    name: "x".to_string(),
                    field_id: id_x,
                },
                int_const(1),
            ),
            (
                TirFieldName {
                    name: "y".to_string(),
                    field_id: id_y,
                },
                bool_const(true),
            ),
        ]));
        let expr = TirExpr::RecordAccess {
            record: Box::new(rec),
            field: TirFieldName {
                name: "x".to_string(),
                field_id: id_x,
            },
        };
        let ty = cg.infer(&expr);
        let resolved = cg.unifier.resolve(&ty);
        assert_eq!(resolved, TirType::Int);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_polymorphic_operator() {
        let mut cg = ConstraintGenerator::new();

        // Simulate: LET Id(x) == x IN <<Id(1), Id(TRUE)>>
        // Id should be polymorphic: forall a. a -> a

        // We need to manually set up the LET/IN since we can't easily construct
        // a full TirExpr::Let with Apply. Instead, test via TypeScheme directly.
        let a = cg.unifier.fresh_var(); // t0
        let id_ty = TirType::Func(Box::new(a.clone()), Box::new(a.clone()));
        let env_vars = cg.env.free_vars();
        let scheme = cg.unifier.generalize(&id_ty, &env_vars);

        // Instantiate twice: should get different variables.
        let inst1 = cg.unifier.instantiate(&scheme);
        let inst2 = cg.unifier.instantiate(&scheme);

        // Unify inst1 with Int -> Int
        match &inst1 {
            TirType::Func(d, r) => {
                let _ = cg.unifier.unify(d, &TirType::Int, None);
                // d and r should be the same variable, so r should also be Int.
                assert_eq!(cg.unifier.resolve(r), TirType::Int);
            }
            _ => panic!("expected Func"),
        }

        // Unify inst2 with Bool -> Bool (independent from inst1).
        match &inst2 {
            TirType::Func(d, r) => {
                let _ = cg.unifier.unify(d, &TirType::Bool, None);
                assert_eq!(cg.unifier.resolve(r), TirType::Bool);
            }
            _ => panic!("expected Func"),
        }

        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_if_then_else_unifies_branches() {
        let mut cg = ConstraintGenerator::new();
        let expr = TirExpr::If {
            cond: Box::new(bool_const(true)),
            then_: Box::new(int_const(1)),
            else_: Box::new(int_const(2)),
        };
        let ty = cg.infer(&expr);
        assert_eq!(cg.unifier.resolve(&ty), TirType::Int);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_if_then_else_branch_mismatch() {
        let mut cg = ConstraintGenerator::new();
        // IF TRUE THEN 1 ELSE TRUE: branches are Int and Bool
        let expr = TirExpr::If {
            cond: Box::new(bool_const(true)),
            then_: Box::new(int_const(1)),
            else_: Box::new(bool_const(true)),
        };
        let _ty = cg.infer(&expr);
        // Should produce a unification error (Int vs Bool).
        assert!(cg.unifier.has_errors());
    }

    #[test]
    fn test_quantifier_constraints() {
        let mut cg = ConstraintGenerator::new();
        let bound = TirBoundVar {
            name: "x".to_string(),
            name_id: intern_name("x"),
            domain: Some(Box::new(set_of_ints())),
            pattern: None,
        };
        // \A x \in {1,2} : x > 0
        let expr = TirExpr::Forall {
            vars: vec![bound],
            body: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(name_ref("x", TirType::Dyn)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
        };
        let ty = cg.infer(&expr);
        assert_eq!(cg.unifier.resolve(&ty), TirType::Bool);
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_range_constraints() {
        let mut cg = ConstraintGenerator::new();
        let expr = TirExpr::Range {
            lo: Box::new(int_const(1)),
            hi: Box::new(int_const(10)),
        };
        let ty = cg.infer(&expr);
        assert_eq!(
            cg.unifier.resolve(&ty),
            TirType::Set(Box::new(TirType::Int))
        );
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_domain_constraints() {
        let mut cg = ConstraintGenerator::new();
        let bound = TirBoundVar {
            name: "x".to_string(),
            name_id: intern_name("x"),
            domain: Some(Box::new(set_of_ints())),
            pattern: None,
        };
        let func = spanned(TirExpr::FuncDef {
            vars: vec![bound],
            body: Box::new(bool_const(true)),
        });
        let expr = TirExpr::Domain(Box::new(func));
        let ty = cg.infer(&expr);
        let resolved = cg.unifier.resolve(&ty);
        assert_eq!(resolved, TirType::Set(Box::new(TirType::Int)));
        assert!(!cg.unifier.has_errors());
    }

    #[test]
    fn test_tuple_constraints() {
        let mut cg = ConstraintGenerator::new();
        let expr = TirExpr::Tuple(vec![int_const(1), bool_const(true), str_const("hi")]);
        let ty = cg.infer(&expr);
        assert_eq!(
            cg.unifier.resolve(&ty),
            TirType::Tuple(vec![TirType::Int, TirType::Bool, TirType::Str])
        );
    }

    #[test]
    fn test_set_builder_constraints() {
        let mut cg = ConstraintGenerator::new();
        let bound = TirBoundVar {
            name: "x".to_string(),
            name_id: intern_name("x"),
            domain: Some(Box::new(set_of_ints())),
            pattern: None,
        };
        // {x > 0 : x \in {1,2}} has type Set(Bool) since body is Bool
        let expr = TirExpr::SetBuilder {
            body: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(name_ref("x", TirType::Dyn)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
            vars: vec![bound],
        };
        let ty = cg.infer(&expr);
        assert_eq!(
            cg.unifier.resolve(&ty),
            TirType::Set(Box::new(TirType::Bool))
        );
    }

    #[test]
    fn test_variable_type_propagation() {
        let mut cg = ConstraintGenerator::new();
        // Add a variable "v" with a fresh type.
        let v_ty = cg.add_variable("v");
        // Use: v + 1 should constrain v to Int.
        let expr = TirExpr::ArithBinOp {
            left: Box::new(name_ref("v", TirType::Dyn)),
            op: TirArithOp::Add,
            right: Box::new(int_const(1)),
        };
        let result_ty = cg.infer(&expr);
        assert_eq!(cg.unifier.resolve(&result_ty), TirType::Int);
        assert_eq!(cg.unifier.resolve(&v_ty), TirType::Int);
    }

    #[test]
    fn test_choose_type_inference() {
        let mut cg = ConstraintGenerator::new();
        let bound = TirBoundVar {
            name: "x".to_string(),
            name_id: intern_name("x"),
            domain: Some(Box::new(set_of_ints())),
            pattern: None,
        };
        // CHOOSE x \in {1,2} : x > 0
        let expr = TirExpr::Choose {
            var: bound,
            body: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(name_ref("x", TirType::Dyn)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
        };
        let ty = cg.infer(&expr);
        assert_eq!(cg.unifier.resolve(&ty), TirType::Int);
    }
}
