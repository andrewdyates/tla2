// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort inference for VMT state variables.
#![allow(dead_code)]
//!
//! Infers SMT-LIB2 sorts (Bool, Int) from TLA+ TypeOK membership constraints
//! and Init assignment patterns.
//!
//! Part of #3755.

use tla_core::ast::{Expr, Module, Unit};
use tla_core::Spanned;

use super::vmt::{VmtSort, VmtVar};

/// Collect state variables and infer their sorts from the Init operator.
pub(super) fn collect_and_infer_vars(
    module: &Module,
    init_name: &str,
) -> Result<Vec<VmtVar>, String> {
    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                var_names.push(name.node.clone());
            }
        }
    }

    // Find Init body for sort inference.
    let init_body = module.units.iter().find_map(|u| {
        if let Unit::Operator(def) = &u.node {
            if def.name.node == init_name {
                return Some(&def.body);
            }
        }
        None
    });

    // Find TypeOK body for sort inference.
    let type_ok_body = module.units.iter().find_map(|u| {
        if let Unit::Operator(def) = &u.node {
            let lower = def.name.node.to_lowercase();
            if lower == "typeok" || lower == "typeinvariant" || lower == "type_ok" {
                return Some(&def.body);
            }
        }
        None
    });

    let vars = var_names
        .into_iter()
        .map(|name| {
            let sort = infer_var_sort(&name, init_body, type_ok_body);
            VmtVar { name, sort }
        })
        .collect();
    Ok(vars)
}

/// Infer the sort of a single variable from TypeOK or Init constraints.
fn infer_var_sort(
    var: &str,
    init_body: Option<&Spanned<Expr>>,
    type_ok_body: Option<&Spanned<Expr>>,
) -> VmtSort {
    // Try TypeOK first (membership constraints are most reliable).
    if let Some(body) = type_ok_body {
        if let Some(sort) = check_membership(var, body) {
            return sort;
        }
    }

    // Try Init (assignment patterns).
    if let Some(body) = init_body {
        if let Some(sort) = check_init_sort(var, body) {
            return sort;
        }
    }

    // Default to Int (most TLA+ specs use integers).
    VmtSort::Int
}

/// Check TypeOK-style membership constraints: `var \in BOOLEAN` or `var \in Int`.
fn check_membership(var: &str, expr: &Spanned<Expr>) -> Option<VmtSort> {
    match &expr.node {
        Expr::And(a, b) | Expr::Or(a, b) => {
            check_membership(var, a).or_else(|| check_membership(var, b))
        }
        Expr::In(elem, set) => {
            let is_var = matches!(
                &elem.node,
                Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var
            );
            if !is_var {
                return None;
            }
            match &set.node {
                Expr::Ident(name, _) if name == "BOOLEAN" => Some(VmtSort::Bool),
                Expr::Ident(name, _) if name == "Int" || name == "Nat" => Some(VmtSort::Int),
                Expr::Range(_, _) => Some(VmtSort::Int),
                _ => None,
            }
        }
        Expr::Label(label) => check_membership(var, &label.body),
        Expr::Let(_, body) => check_membership(var, body),
        _ => None,
    }
}

/// Check Init-style assignment: `var = TRUE/FALSE` -> Bool, `var = N` -> Int.
fn check_init_sort(var: &str, expr: &Spanned<Expr>) -> Option<VmtSort> {
    match &expr.node {
        Expr::And(a, b) | Expr::Or(a, b) => {
            check_init_sort(var, a).or_else(|| check_init_sort(var, b))
        }
        Expr::Eq(lhs, rhs) => {
            let is_var = matches!(
                &lhs.node,
                Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var
            );
            if !is_var {
                return None;
            }
            match &rhs.node {
                Expr::Bool(_) => Some(VmtSort::Bool),
                Expr::Int(_) => Some(VmtSort::Int),
                _ => None,
            }
        }
        Expr::In(elem, set) => {
            let is_var = matches!(
                &elem.node,
                Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var
            );
            if !is_var {
                return None;
            }
            match &set.node {
                Expr::Ident(name, _) if name == "BOOLEAN" => Some(VmtSort::Bool),
                Expr::Ident(name, _) if name == "Int" || name == "Nat" => Some(VmtSort::Int),
                Expr::Range(_, _) => Some(VmtSort::Int),
                _ => None,
            }
        }
        Expr::Label(label) => check_init_sort(var, &label.body),
        Expr::Let(_, body) => check_init_sort(var, body),
        _ => None,
    }
}

/// Infer the sort of a bound variable's domain.
pub(super) fn domain_sort(domain: &Spanned<Expr>) -> Result<VmtSort, String> {
    match &domain.node {
        Expr::Ident(name, _) if name == "BOOLEAN" => Ok(VmtSort::Bool),
        Expr::Ident(name, _) if name == "Int" || name == "Nat" => Ok(VmtSort::Int),
        Expr::Range(_, _) => Ok(VmtSort::Int),
        _ => Ok(VmtSort::Int), // Default to Int for unrecognized domains.
    }
}
