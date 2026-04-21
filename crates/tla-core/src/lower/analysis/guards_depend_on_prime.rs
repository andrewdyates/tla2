// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use crate::ast::{ExceptPathElement, Expr, Module, ModuleTarget, Unit};

use super::fixed_point::{propagate_truth, DependencyScan};

pub fn compute_guards_depend_on_prime(module: &mut Module) {
    let mut op_guards_prime: HashMap<String, bool> = HashMap::new();
    let mut scans: HashMap<String, DependencyScan> = HashMap::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let name = def.name.node.clone();
            let (has_guard_prime, scan) = analyze_expr_for_guard_primes(&def.body.node);
            op_guards_prime.insert(name.clone(), has_guard_prime);
            scans.insert(name, scan);
        }
    }

    propagate_truth(&mut op_guards_prime, &scans);

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            def.guards_depend_on_prime = op_guards_prime
                .get(&def.name.node)
                .copied()
                .unwrap_or(false);
        }
    }
}

fn analyze_expr_for_guard_primes(expr: &Expr) -> (bool, DependencyScan) {
    let mut guards_depend_on_prime = false;
    let mut scan = DependencyScan::default();
    analyze_guards_recursive(expr, &mut guards_depend_on_prime, &mut scan, false);
    (guards_depend_on_prime, scan)
}

fn analyze_guards_recursive(expr: &Expr, gp: &mut bool, scan: &mut DependencyScan, in_guard: bool) {
    match expr {
        Expr::And(a, b) => {
            if !is_primed_assignment(&a.node) {
                analyze_guards_recursive(&a.node, gp, scan, true);
            }
            if !is_primed_assignment(&b.node) {
                analyze_guards_recursive(&b.node, gp, scan, true);
            }
        }
        Expr::Or(a, b) => {
            analyze_guards_recursive(&a.node, gp, scan, in_guard);
            analyze_guards_recursive(&b.node, gp, scan, in_guard);
        }
        Expr::If(cond, then_expr, else_expr) => {
            analyze_guards_recursive(&cond.node, gp, scan, true);
            analyze_guards_recursive(&then_expr.node, gp, scan, in_guard);
            analyze_guards_recursive(&else_expr.node, gp, scan, in_guard);
        }
        Expr::Case(arms, default) => {
            for arm in arms {
                analyze_guards_recursive(&arm.guard.node, gp, scan, true);
                analyze_guards_recursive(&arm.body.node, gp, scan, in_guard);
            }
            if let Some(default) = default {
                analyze_guards_recursive(&default.node, gp, scan, in_guard);
            }
        }
        Expr::Prime(_) => {
            if in_guard {
                *gp = true;
            }
        }
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if in_guard {
                scan.local_refs.insert(name.clone());
            }
        }
        Expr::Apply(op, args) => {
            if let Expr::Ident(name, _) = &op.node {
                if in_guard {
                    scan.local_refs.insert(name.clone());
                }
            } else {
                analyze_guards_recursive(&op.node, gp, scan, in_guard);
            }
            for arg in args {
                analyze_guards_recursive(&arg.node, gp, scan, in_guard);
            }
        }
        Expr::Implies(a, b) => {
            analyze_guards_recursive(&a.node, gp, scan, true);
            analyze_guards_recursive(&b.node, gp, scan, in_guard);
        }
        Expr::Equiv(a, b) => {
            analyze_guards_recursive(&a.node, gp, scan, true);
            analyze_guards_recursive(&b.node, gp, scan, true);
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    analyze_guards_recursive(&domain.node, gp, scan, in_guard);
                }
            }
            analyze_guards_recursive(&body.node, gp, scan, in_guard);
        }
        Expr::Let(defs, body) => {
            for def in defs {
                analyze_guards_recursive(&def.body.node, gp, scan, in_guard);
            }
            analyze_guards_recursive(&body.node, gp, scan, in_guard);
        }
        Expr::Eq(a, b)
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
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::FuncSet(a, b) => {
            analyze_guards_recursive(&a.node, gp, scan, in_guard);
            analyze_guards_recursive(&b.node, gp, scan, in_guard);
        }
        Expr::Not(e)
        | Expr::Neg(e)
        | Expr::Domain(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Unchanged(e) => analyze_guards_recursive(&e.node, gp, scan, in_guard),
        // ENABLED is state-level: primes inside are scoped (#1640).
        Expr::Enabled(_) => {}
        Expr::FuncDef(bounds, body) | Expr::SetBuilder(body, bounds) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    analyze_guards_recursive(&domain.node, gp, scan, in_guard);
                }
            }
            analyze_guards_recursive(&body.node, gp, scan, in_guard);
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            if let Some(domain) = &bound.domain {
                analyze_guards_recursive(&domain.node, gp, scan, in_guard);
            }
            analyze_guards_recursive(&body.node, gp, scan, in_guard);
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                analyze_guards_recursive(&elem.node, gp, scan, in_guard);
            }
        }
        Expr::FuncApply(func, arg) => {
            analyze_guards_recursive(&func.node, gp, scan, in_guard);
            analyze_guards_recursive(&arg.node, gp, scan, in_guard);
        }
        Expr::RecordAccess(record, _) => analyze_guards_recursive(&record.node, gp, scan, in_guard),
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, expr) in fields {
                analyze_guards_recursive(&expr.node, gp, scan, in_guard);
            }
        }
        Expr::Except(base, specs) => {
            analyze_guards_recursive(&base.node, gp, scan, in_guard);
            for spec in specs {
                for elem in &spec.path {
                    if let ExceptPathElement::Index(expr) = elem {
                        analyze_guards_recursive(&expr.node, gp, scan, in_guard);
                    }
                }
                analyze_guards_recursive(&spec.value.node, gp, scan, in_guard);
            }
        }
        Expr::Lambda(_, body) => analyze_guards_recursive(&body.node, gp, scan, in_guard),
        Expr::WeakFair(subscript, action) | Expr::StrongFair(subscript, action) => {
            analyze_guards_recursive(&subscript.node, gp, scan, in_guard);
            analyze_guards_recursive(&action.node, gp, scan, in_guard);
        }
        Expr::InstanceExpr(_, subs) => {
            for sub in subs {
                analyze_guards_recursive(&sub.to.node, gp, scan, in_guard);
            }
        }
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                analyze_guards_recursive(&sub.to.node, gp, scan, in_guard);
            }
            analyze_guards_recursive(&body.node, gp, scan, in_guard);
        }
        Expr::ModuleRef(target, _, args) => {
            analyze_module_target(target, gp, scan, in_guard);
            for arg in args {
                analyze_guards_recursive(&arg.node, gp, scan, in_guard);
            }
        }
        Expr::Label(label) => analyze_guards_recursive(&label.body.node, gp, scan, in_guard),
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => {}
    }
}

fn analyze_module_target(
    target: &ModuleTarget,
    gp: &mut bool,
    scan: &mut DependencyScan,
    in_guard: bool,
) {
    match target {
        ModuleTarget::Named(_) => {}
        ModuleTarget::Parameterized(_, params) => {
            // Guard-sensitive primes can also arrive via INSTANCE substitutions.
            for param in params {
                analyze_guards_recursive(&param.node, gp, scan, in_guard);
            }
        }
        ModuleTarget::Chained(base) => analyze_guards_recursive(&base.node, gp, scan, in_guard),
    }
}

fn is_primed_assignment(expr: &Expr) -> bool {
    match expr {
        Expr::Eq(a, _) | Expr::In(a, _) => {
            if let Expr::Prime(inner) = &a.node {
                matches!(&inner.node, Expr::Ident(_, _))
            } else {
                false
            }
        }
        _ => false,
    }
}
