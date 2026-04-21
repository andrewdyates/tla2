// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use crate::ast::{ExceptPathElement, Expr, Module, ModuleTarget, Unit};

use super::fixed_point::{propagate_truth, DependencyScan};

/// Compute the `contains_prime` flag for all operators in a module.
///
/// This must be called after lowering to set the flag correctly, as operators
/// can reference each other and the flag needs to be computed transitively.
pub fn compute_contains_prime(module: &mut Module) {
    let mut op_contains_prime: HashMap<String, bool> = HashMap::new();
    let mut scans: HashMap<String, DependencyScan> = HashMap::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let name = def.name.node.clone();
            let (has_direct_prime, scan) = analyze_expr_for_primes(&def.body.node);
            op_contains_prime.insert(name.clone(), has_direct_prime);
            scans.insert(name, scan);
        }
    }

    propagate_truth(&mut op_contains_prime, &scans);

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            def.contains_prime = op_contains_prime
                .get(&def.name.node)
                .copied()
                .unwrap_or(false);
        }
    }
}

/// Analyze an expression for direct prime usage and local operator references.
fn analyze_expr_for_primes(expr: &Expr) -> (bool, DependencyScan) {
    let mut has_prime = false;
    let mut scan = DependencyScan::default();
    visit(expr, &mut has_prime, &mut scan);
    (has_prime, scan)
}

fn visit(expr: &Expr, has_prime: &mut bool, scan: &mut DependencyScan) {
    match expr {
        Expr::Prime(_) => *has_prime = true,

        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            scan.local_refs.insert(name.clone());
        }
        Expr::Apply(op_expr, args) => {
            if let Expr::Ident(name, _) = &op_expr.node {
                scan.local_refs.insert(name.clone());
            }
            visit(&op_expr.node, has_prime, scan);
            for arg in args {
                visit(&arg.node, has_prime, scan);
            }
        }
        Expr::ModuleRef(target, _, args) => {
            visit_module_target(target, has_prime, scan);
            for arg in args {
                visit(&arg.node, has_prime, scan);
            }
        }

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
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::FuncSet(a, b) => {
            visit(&a.node, has_prime, scan);
            visit(&b.node, has_prime, scan);
        }
        Expr::Not(e)
        | Expr::Neg(e)
        | Expr::Domain(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Unchanged(e) => visit(&e.node, has_prime, scan),
        // ENABLED is a state-level operator: primes inside are scoped
        // to ENABLED and do not make the enclosing operator action-level.
        // Without this, `Inner == ENABLED(x' = x + 1)` would get
        // `contains_prime = true`, breaking OR short-circuit (#1640).
        Expr::Enabled(_) => {}
        Expr::If(cond, then_expr, else_expr) => {
            visit(&cond.node, has_prime, scan);
            visit(&then_expr.node, has_prime, scan);
            visit(&else_expr.node, has_prime, scan);
        }
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body)
        | Expr::SetBuilder(body, bounds) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    visit(&domain.node, has_prime, scan);
                }
            }
            visit(&body.node, has_prime, scan);
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            if let Some(domain) = &bound.domain {
                visit(&domain.node, has_prime, scan);
            }
            visit(&body.node, has_prime, scan);
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                visit(&elem.node, has_prime, scan);
            }
        }
        Expr::FuncApply(func, arg) => {
            visit(&func.node, has_prime, scan);
            visit(&arg.node, has_prime, scan);
        }
        Expr::RecordAccess(record, _) => visit(&record.node, has_prime, scan),
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, expr) in fields {
                visit(&expr.node, has_prime, scan);
            }
        }
        Expr::Except(base, specs) => {
            visit(&base.node, has_prime, scan);
            for spec in specs {
                for elem in &spec.path {
                    match elem {
                        ExceptPathElement::Index(expr) => visit(&expr.node, has_prime, scan),
                        ExceptPathElement::Field(_) => {}
                    }
                }
                visit(&spec.value.node, has_prime, scan);
            }
        }
        Expr::Case(arms, default) => {
            for arm in arms {
                visit(&arm.guard.node, has_prime, scan);
                visit(&arm.body.node, has_prime, scan);
            }
            if let Some(default) = default {
                visit(&default.node, has_prime, scan);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                visit(&def.body.node, has_prime, scan);
            }
            visit(&body.node, has_prime, scan);
        }
        Expr::Lambda(_, body) => visit(&body.node, has_prime, scan),
        Expr::WeakFair(subscript, action) | Expr::StrongFair(subscript, action) => {
            visit(&subscript.node, has_prime, scan);
            visit(&action.node, has_prime, scan);
        }
        Expr::InstanceExpr(_, subs) => {
            for sub in subs {
                visit(&sub.to.node, has_prime, scan);
            }
        }
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                visit(&sub.to.node, has_prime, scan);
            }
            visit(&body.node, has_prime, scan);
        }
        Expr::Label(label) => visit(&label.body.node, has_prime, scan),
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => {}
    }
}

fn visit_module_target(target: &ModuleTarget, has_prime: &mut bool, scan: &mut DependencyScan) {
    match target {
        ModuleTarget::Named(_) => {}
        ModuleTarget::Parameterized(_, params) => {
            // `P(x')!Safe` carries the substitution in the target, not in args.
            for param in params {
                visit(&param.node, has_prime, scan);
            }
        }
        ModuleTarget::Chained(base) => visit(&base.node, has_prime, scan),
    }
}
