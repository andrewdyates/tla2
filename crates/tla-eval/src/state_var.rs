// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State variable resolution pass.
//!
//! Converts `Expr::Ident(name, _)` that refer to declared state variables into
//! `Expr::StateVar(name, idx, name_id)` using a `VarRegistry`.
//!
//! This enables O(1) state array lookup AND O(1) shadowing checks in the evaluator
//! by pre-computing both the index and NameId at transformation time (Part of #188).
//!
//! ## Shadowing (Fix for #399)
//!
//! This pass tracks names that shadow state variables:
//! - Operator parameters (e.g., `And(x, y, n, m)` where `x` might shadow a state var)
//! - Quantifier bounds (e.g., `\E x \in S: ...`)
//! - LET-defined names (e.g., `LET exp == ... IN ...`)
//! - Lambda parameters
//!
//! When a name is shadowed, it is NOT converted to StateVar even if a state variable
//! with the same name exists.

use rustc_hash::FxHashSet;

use tla_core::ast::{
    BoundVar, CaseArm, ExceptPathElement, ExceptSpec, Expr, ModuleTarget, OperatorDef, Substitution,
};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::Spanned;

use crate::var_index::VarRegistry;

/// Resolve state variables in an operator definition.
///
/// FIX #399: The operator's parameters shadow any state variables with the same name.
/// For example, `And(x, y, n, m)` should not resolve parameter `x` as the state variable `x`.
pub fn resolve_state_vars_in_op_def(def: &mut OperatorDef, registry: &VarRegistry) {
    // Collect parameter names - these shadow state variables in the body
    let shadows: FxHashSet<&str> = def.params.iter().map(|p| p.name.node.as_str()).collect();
    resolve_state_vars_in_spanned_with_shadows(&mut def.body, registry, &shadows);
}

pub fn resolve_state_vars_in_substitution(sub: &mut Substitution, registry: &VarRegistry) {
    resolve_state_vars_in_spanned_with_shadows(&mut sub.to, registry, &FxHashSet::default());
}

// Internal functions that track shadows

fn resolve_state_vars_in_spanned_with_shadows(
    expr: &mut Spanned<Expr>,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    resolve_state_vars_in_expr_with_shadows(&mut expr.node, registry, shadows);
}

fn resolve_state_vars_in_expr_with_shadows(
    expr: &mut Expr,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    match expr {
        // === Literals ===
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => {}

        // === Names ===
        Expr::Ident(name, name_id) => {
            // Part of #2993: Pre-resolve NameId for ALL identifiers at load time,
            // eliminating runtime lookup_name_id() calls during evaluation.
            if *name_id == NameId::INVALID {
                *name_id = intern_name(name.as_str());
            }
            // FIX #399: Don't resolve to StateVar if this name is shadowed
            if !shadows.contains(name.as_str()) {
                if let Some(idx) = registry.get(name.as_str()) {
                    let nid = *name_id;
                    let n = name.clone();
                    *expr = Expr::StateVar(n, idx.0, nid);
                }
            }
        }
        Expr::StateVar(_, _, _) => {}

        // === Operators ===
        Expr::Apply(op, args) => {
            resolve_state_vars_in_spanned_with_shadows(op, registry, shadows);
            for a in args {
                resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
            }
        }
        Expr::ModuleRef(target, _op, args) => {
            resolve_state_vars_in_module_target_with_shadows(target, registry, shadows);
            for a in args {
                resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
            }
        }
        Expr::InstanceExpr(_module, subs) => {
            for sub in subs {
                resolve_state_vars_in_substitution_with_shadows(sub, registry, shadows);
            }
        }
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                resolve_state_vars_in_substitution_with_shadows(sub, registry, shadows);
            }
            resolve_state_vars_in_spanned_with_shadows(body, registry, shadows);
        }
        Expr::Lambda(params, body) => {
            // Lambda parameters shadow state variables in the body
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            for p in params.iter() {
                inner_shadows.insert(p.node.as_str());
            }
            resolve_state_vars_in_spanned_with_shadows(body, registry, &inner_shadows);
        }
        Expr::Label(label) => {
            resolve_state_vars_in_spanned_with_shadows(&mut label.body, registry, shadows);
        }

        // === Logic ===
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
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
        | Expr::Range(a, b) => {
            resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
            resolve_state_vars_in_spanned_with_shadows(b, registry, shadows);
        }

        Expr::Not(a)
        | Expr::Neg(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a) => {
            resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
        }

        // === Quantifiers ===
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            // Process domain expressions with current shadows
            for b in bounds.iter_mut() {
                resolve_state_vars_in_bound_var_domain_with_shadows(b, registry, shadows);
            }
            // Bound variables shadow state variables in the body
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            for b in bounds.iter() {
                inner_shadows.insert(b.name.node.as_str());
            }
            resolve_state_vars_in_spanned_with_shadows(body, registry, &inner_shadows);
        }
        Expr::Choose(bound, body) => {
            resolve_state_vars_in_bound_var_domain_with_shadows(bound, registry, shadows);
            // Bound variable shadows state variables in the body
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            inner_shadows.insert(bound.name.node.as_str());
            resolve_state_vars_in_spanned_with_shadows(body, registry, &inner_shadows);
        }

        // === Sets ===
        Expr::SetEnum(elems) | Expr::Tuple(elems) => {
            for e in elems {
                resolve_state_vars_in_spanned_with_shadows(e, registry, shadows);
            }
        }
        Expr::Times(factors) => {
            for f in factors {
                resolve_state_vars_in_spanned_with_shadows(f, registry, shadows);
            }
        }
        Expr::SetBuilder(value, bounds) => {
            // Process domain expressions with current shadows
            for b in bounds.iter_mut() {
                resolve_state_vars_in_bound_var_domain_with_shadows(b, registry, shadows);
            }
            // Bound variables shadow state variables in the value expression
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            for b in bounds.iter() {
                inner_shadows.insert(b.name.node.as_str());
            }
            resolve_state_vars_in_spanned_with_shadows(value, registry, &inner_shadows);
        }
        Expr::SetFilter(bound, pred) => {
            resolve_state_vars_in_bound_var_domain_with_shadows(bound, registry, shadows);
            // Bound variable shadows state variables in the predicate
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            inner_shadows.insert(bound.name.node.as_str());
            resolve_state_vars_in_spanned_with_shadows(pred, registry, &inner_shadows);
        }

        // === Functions ===
        Expr::FuncDef(bounds, body) => {
            // Process domain expressions with current shadows
            for b in bounds.iter_mut() {
                resolve_state_vars_in_bound_var_domain_with_shadows(b, registry, shadows);
            }
            // Bound variables shadow state variables in the body
            let mut inner_shadows: FxHashSet<&str> = shadows.clone();
            for b in bounds.iter() {
                inner_shadows.insert(b.name.node.as_str());
            }
            resolve_state_vars_in_spanned_with_shadows(body, registry, &inner_shadows);
        }
        Expr::FuncApply(f, x) => {
            resolve_state_vars_in_spanned_with_shadows(f, registry, shadows);
            resolve_state_vars_in_spanned_with_shadows(x, registry, shadows);
        }
        Expr::Except(base, specs) => {
            resolve_state_vars_in_spanned_with_shadows(base, registry, shadows);
            for spec in specs {
                resolve_state_vars_in_except_spec_with_shadows(spec, registry, shadows);
            }
        }
        Expr::FuncSet(a, b) => {
            resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
            resolve_state_vars_in_spanned_with_shadows(b, registry, shadows);
        }

        // === Records ===
        Expr::Record(fields) => {
            for (_k, v) in fields {
                resolve_state_vars_in_spanned_with_shadows(v, registry, shadows);
            }
        }
        Expr::RecordAccess(record, _field) => {
            resolve_state_vars_in_spanned_with_shadows(record, registry, shadows);
        }
        Expr::RecordSet(fields) => {
            for (_k, v) in fields {
                resolve_state_vars_in_spanned_with_shadows(v, registry, shadows);
            }
        }

        // === Control ===
        Expr::If(cond, a, b) => {
            resolve_state_vars_in_spanned_with_shadows(cond, registry, shadows);
            resolve_state_vars_in_spanned_with_shadows(a, registry, shadows);
            resolve_state_vars_in_spanned_with_shadows(b, registry, shadows);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                resolve_state_vars_in_case_arm_with_shadows(arm, registry, shadows);
            }
            if let Some(other) = other.as_mut() {
                resolve_state_vars_in_spanned_with_shadows(other, registry, shadows);
            }
        }
        Expr::Let(defs, body) => {
            // FIX #406: Sequential LET scoping - earlier def names shadow in later def bodies.
            // This matches TLC/SANY behavior where LET defs are processed sequentially.
            let mut accumulated_let_names: FxHashSet<&str> = FxHashSet::default();

            // Process LET definitions sequentially - each def's body sees:
            // 1. outer shadows
            // 2. previously-defined LET names in this LET block (sequential scoping)
            // 3. the current def's parameters
            for def in defs.iter_mut() {
                let mut inner_shadows: FxHashSet<&str> = shadows.clone();
                // Add previously-defined LET names (sequential scoping)
                inner_shadows.extend(accumulated_let_names.iter().copied());
                // Add current def's parameters
                for p in &def.params {
                    inner_shadows.insert(p.name.node.as_str());
                }
                resolve_state_vars_in_spanned_with_shadows(&mut def.body, registry, &inner_shadows);
                // After processing this def, add its name for subsequent defs
                accumulated_let_names.insert(def.name.node.as_str());
            }

            // LET-defined names shadow state variables in the IN body
            let mut body_shadows: FxHashSet<&str> = shadows.clone();
            body_shadows.extend(accumulated_let_names);
            resolve_state_vars_in_spanned_with_shadows(body, registry, &body_shadows);
        }
    }
}

fn resolve_state_vars_in_module_target_with_shadows(
    target: &mut ModuleTarget,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    match target {
        ModuleTarget::Named(_) => {}
        ModuleTarget::Parameterized(_name, params) => {
            for p in params {
                resolve_state_vars_in_spanned_with_shadows(p, registry, shadows);
            }
        }
        ModuleTarget::Chained(base) => {
            resolve_state_vars_in_spanned_with_shadows(base, registry, shadows);
        }
    }
}

fn resolve_state_vars_in_substitution_with_shadows(
    sub: &mut Substitution,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    resolve_state_vars_in_spanned_with_shadows(&mut sub.to, registry, shadows);
}

/// Resolve state vars in a bound variable's domain expression only.
/// The bound variable name itself is NOT a shadow yet - it becomes one in the body.
fn resolve_state_vars_in_bound_var_domain_with_shadows(
    bound: &mut BoundVar,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    if let Some(domain) = bound.domain.as_mut() {
        resolve_state_vars_in_spanned_with_shadows(domain, registry, shadows);
    }
}

fn resolve_state_vars_in_case_arm_with_shadows(
    arm: &mut CaseArm,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    resolve_state_vars_in_spanned_with_shadows(&mut arm.guard, registry, shadows);
    resolve_state_vars_in_spanned_with_shadows(&mut arm.body, registry, shadows);
}

fn resolve_state_vars_in_except_spec_with_shadows(
    spec: &mut ExceptSpec,
    registry: &VarRegistry,
    shadows: &FxHashSet<&str>,
) {
    for elem in &mut spec.path {
        if let ExceptPathElement::Index(i) = elem {
            resolve_state_vars_in_spanned_with_shadows(i, registry, shadows);
        }
    }
    resolve_state_vars_in_spanned_with_shadows(&mut spec.value, registry, shadows);
}
