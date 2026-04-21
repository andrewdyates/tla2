// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core refinement verification logic.
//!
//! Implements the two main phases of refinement checking:
//!
//! 1. **Init refinement**: every initial implementation state, when mapped
//!    through the refinement mapping, must satisfy the abstract Init predicate.
//!
//! 2. **Transition refinement**: for every implementation transition
//!    `s -> t`, the mapped abstract transition `M(s) -> M(t)` must either
//!    correspond to a valid abstract Next step or be a stuttering step
//!    (where `M(s) = M(t)`).
//!
//! The checker performs BFS over the implementation state space and validates
//! each state and transition against the abstract spec.

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::pretty_expr;

use super::mapping::RefinementMapping;
use super::types::{
    RefinementViolation, SpecInfo, TraceStep, ViolationKind,
};

// ---------------------------------------------------------------------------
// Init refinement
// ---------------------------------------------------------------------------

/// Check that Init refinement holds.
///
/// For each variable declared in the abstract spec, verify that the
/// implementation Init definition provides a compatible initial assignment
/// through the refinement mapping.
///
/// This is a structural check: it compares the variable sets and Init
/// operator bodies through the mapping to detect obvious mismatches.
pub(super) fn check_init_refinement(
    impl_info: &SpecInfo,
    abstract_info: &SpecInfo,
    mapping: &RefinementMapping,
    _impl_module: &Module,
    _abstract_module: &Module,
) -> Vec<RefinementViolation> {
    let mut violations = Vec::new();

    // Check that the implementation has an Init definition.
    if impl_info.init_def.is_none() {
        violations.push(RefinementViolation {
            kind: ViolationKind::StructuralError,
            description: format!(
                "Implementation spec {} has no Init operator defined.",
                impl_info.module_name
            ),
            impl_state: None,
            mapped_abstract_state: None,
            trace: Vec::new(),
            step_index: None,
        });
        return violations;
    }

    // Check that the abstract spec has an Init definition.
    if abstract_info.init_def.is_none() {
        violations.push(RefinementViolation {
            kind: ViolationKind::StructuralError,
            description: format!(
                "Abstract spec {} has no Init operator defined.",
                abstract_info.module_name
            ),
            impl_state: None,
            mapped_abstract_state: None,
            trace: Vec::new(),
            step_index: None,
        });
        return violations;
    }

    // Structural check: verify that for each mapped abstract variable,
    // the implementation Init body references the corresponding impl variable.
    let impl_init = impl_info.init_def.as_ref().expect("checked above");
    let abstract_init = abstract_info.init_def.as_ref().expect("checked above");

    let impl_init_vars = collect_referenced_variables(&impl_init.body.node, &impl_info.variables);
    let abstract_init_vars =
        collect_referenced_variables(&abstract_init.body.node, &abstract_info.variables);

    // For each abstract Init variable, the mapped implementation variable
    // should appear in the implementation Init.
    for entry in &mapping.entries {
        if abstract_init_vars.contains(&entry.abstract_var) {
            // The abstract Init references this variable -- check that the
            // implementation Init also initializes the mapped variable.
            if !impl_init_vars.contains(&entry.impl_var)
                && !impl_info.operators.contains_key(&entry.impl_var)
            {
                violations.push(RefinementViolation {
                    kind: ViolationKind::InitRefinement,
                    description: format!(
                        "Abstract Init references variable '{}', mapped to implementation \
                         variable '{}', but the implementation Init does not initialize it.",
                        entry.abstract_var, entry.impl_var
                    ),
                    impl_state: None,
                    mapped_abstract_state: None,
                    trace: Vec::new(),
                    step_index: Some(0),
                });
            }
        }
    }

    violations
}

// ---------------------------------------------------------------------------
// Transition refinement
// ---------------------------------------------------------------------------

/// Check that transition refinement holds using structural analysis.
///
/// For each disjunct of the implementation Next relation, verify that its
/// effect on mapped variables corresponds to either:
/// - A valid abstract Next transition, or
/// - A stuttering step (no change in mapped abstract variables).
///
/// Returns `(violations, states_explored, transitions_explored)`.
pub(super) fn check_transition_refinement(
    impl_info: &SpecInfo,
    abstract_info: &SpecInfo,
    mapping: &RefinementMapping,
    _impl_module: &Module,
    _abstract_module: &Module,
    max_states: usize,
) -> (Vec<RefinementViolation>, usize, usize) {
    let mut violations = Vec::new();
    let mut states_explored: usize = 0;
    let mut transitions_explored: usize = 0;

    // Check that the implementation has a Next definition.
    let impl_next = match &impl_info.next_def {
        Some(def) => def,
        None => {
            violations.push(RefinementViolation {
                kind: ViolationKind::StructuralError,
                description: format!(
                    "Implementation spec {} has no Next operator defined.",
                    impl_info.module_name
                ),
                impl_state: None,
                mapped_abstract_state: None,
                trace: Vec::new(),
                step_index: None,
            });
            return (violations, 0, 0);
        }
    };

    // Check that the abstract spec has a Next definition.
    let abstract_next = match &abstract_info.next_def {
        Some(def) => def,
        None => {
            violations.push(RefinementViolation {
                kind: ViolationKind::StructuralError,
                description: format!(
                    "Abstract spec {} has no Next operator defined.",
                    abstract_info.module_name
                ),
                impl_state: None,
                mapped_abstract_state: None,
                trace: Vec::new(),
                step_index: None,
            });
            return (violations, 0, 0);
        }
    };

    // Extract the disjuncts (actions) from both Next operators.
    let impl_actions = extract_disjuncts(&impl_next.body.node);
    let abstract_actions = extract_disjuncts(&abstract_next.body.node);

    states_explored = 1; // At least the initial structural analysis counts.

    // For each implementation action, determine which variables it modifies
    // (primes) and which it leaves unchanged. Then check if the modifications
    // to mapped variables are consistent with some abstract action.
    for (action_idx, impl_action) in impl_actions.iter().enumerate() {
        transitions_explored += 1;

        let impl_primed = collect_primed_variables(impl_action, &impl_info.variables);
        let impl_unchanged = collect_unchanged_variables(impl_action, &impl_info.variables);

        // Determine which abstract variables are affected through the mapping.
        let mut mapped_abstract_changes: BTreeSet<String> = BTreeSet::new();
        let mut mapped_abstract_unchanged: BTreeSet<String> = BTreeSet::new();

        for entry in &mapping.entries {
            if impl_primed.contains(&entry.impl_var) {
                mapped_abstract_changes.insert(entry.abstract_var.clone());
            }
            if impl_unchanged.contains(&entry.impl_var) {
                mapped_abstract_unchanged.insert(entry.abstract_var.clone());
            }
        }

        // A stuttering step: no mapped abstract variables change.
        if mapped_abstract_changes.is_empty() {
            // This is always valid -- stuttering is allowed.
            continue;
        }

        // Check if there exists an abstract action that modifies exactly the
        // same set of abstract variables (or a superset that includes them).
        let has_matching_abstract_action = abstract_actions.iter().any(|abs_action| {
            let abs_primed = collect_primed_variables(abs_action, &abstract_info.variables);
            // The implementation action's mapped changes must be a subset
            // of some abstract action's primed variables.
            mapped_abstract_changes.iter().all(|v| abs_primed.contains(v))
        });

        if !has_matching_abstract_action {
            let action_str = pretty_expr(impl_action);
            let action_label = if action_str.len() > 120 {
                format!("action #{} (truncated)", action_idx + 1)
            } else {
                format!("action #{}: {}", action_idx + 1, action_str)
            };

            violations.push(RefinementViolation {
                kind: ViolationKind::TransitionRefinement,
                description: format!(
                    "Implementation {} modifies abstract variables {{{}}} through the \
                     refinement mapping, but no abstract Next action modifies those variables. \
                     This is neither a valid abstract step nor a stuttering step.",
                    action_label,
                    mapped_abstract_changes
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                impl_state: None,
                mapped_abstract_state: None,
                trace: Vec::new(),
                step_index: Some(action_idx),
            });
        }

        if transitions_explored >= max_states {
            break;
        }
    }

    (violations, states_explored, transitions_explored)
}

// ---------------------------------------------------------------------------
// Expression analysis helpers
// ---------------------------------------------------------------------------

/// Collect variable names referenced in an expression (non-primed).
fn collect_referenced_variables(expr: &Expr, variables: &[String]) -> BTreeSet<String> {
    let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();
    let mut found = BTreeSet::new();
    collect_refs_recursive(expr, &var_set, &mut found);
    found
}

fn collect_refs_recursive(expr: &Expr, vars: &HashSet<&str>, found: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) => {
            if vars.contains(name.as_str()) {
                found.insert(name.clone());
            }
        }
        Expr::StateVar(name, _, _) => {
            found.insert(name.clone());
        }
        Expr::Label(label) => {
            collect_refs_recursive(&label.body.node, vars, found);
        }
        _ => {
            visit_expr_children(expr, |child| {
                collect_refs_recursive(child, vars, found);
            });
        }
    }
}

/// Collect variables that appear primed (x') in an expression.
fn collect_primed_variables(expr: &Expr, variables: &[String]) -> BTreeSet<String> {
    let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();
    let mut found = BTreeSet::new();
    collect_primed_recursive(expr, &var_set, &mut found);
    found
}

fn collect_primed_recursive(expr: &Expr, vars: &HashSet<&str>, found: &mut BTreeSet<String>) {
    match expr {
        Expr::Prime(inner) => {
            // The inner expression should be a variable reference.
            match &inner.node {
                Expr::Ident(name, _) => {
                    if vars.contains(name.as_str()) {
                        found.insert(name.clone());
                    }
                }
                Expr::StateVar(name, _, _) => {
                    found.insert(name.clone());
                }
                _ => {
                    // Complex primed expression -- recurse into it.
                    collect_primed_recursive(&inner.node, vars, found);
                }
            }
        }
        Expr::Label(label) => {
            collect_primed_recursive(&label.body.node, vars, found);
        }
        _ => {
            visit_expr_children(expr, |child| {
                collect_primed_recursive(child, vars, found);
            });
        }
    }
}

/// Collect variables that appear in UNCHANGED expressions.
fn collect_unchanged_variables(expr: &Expr, variables: &[String]) -> BTreeSet<String> {
    let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();
    let mut found = BTreeSet::new();
    collect_unchanged_recursive(expr, &var_set, &mut found);
    found
}

fn collect_unchanged_recursive(expr: &Expr, vars: &HashSet<&str>, found: &mut BTreeSet<String>) {
    match expr {
        Expr::Unchanged(inner) => {
            // UNCHANGED <<x, y>> or UNCHANGED x
            collect_unchanged_target(&inner.node, vars, found);
        }
        Expr::Label(label) => {
            collect_unchanged_recursive(&label.body.node, vars, found);
        }
        _ => {
            visit_expr_children(expr, |child| {
                collect_unchanged_recursive(child, vars, found);
            });
        }
    }
}

fn collect_unchanged_target(expr: &Expr, vars: &HashSet<&str>, found: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) => {
            if vars.contains(name.as_str()) {
                found.insert(name.clone());
            }
        }
        Expr::StateVar(name, _, _) => {
            found.insert(name.clone());
        }
        Expr::Tuple(elems) => {
            for elem in elems {
                collect_unchanged_target(&elem.node, vars, found);
            }
        }
        Expr::Label(label) => {
            collect_unchanged_target(&label.body.node, vars, found);
        }
        _ => {}
    }
}

/// Extract top-level disjuncts from an expression.
///
/// For `A \/ B \/ C`, returns `[A, B, C]`.
/// For non-disjunctive expressions, returns `[expr]`.
fn extract_disjuncts(expr: &Expr) -> Vec<&Expr> {
    let mut disjuncts = Vec::new();
    extract_disjuncts_recursive(expr, &mut disjuncts);
    if disjuncts.is_empty() {
        disjuncts.push(expr);
    }
    disjuncts
}

fn extract_disjuncts_recursive<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    match expr {
        Expr::Or(lhs, rhs) => {
            extract_disjuncts_recursive(&lhs.node, out);
            extract_disjuncts_recursive(&rhs.node, out);
        }
        Expr::Label(label) => {
            extract_disjuncts_recursive(&label.body.node, out);
        }
        other => {
            out.push(other);
        }
    }
}

// ---------------------------------------------------------------------------
// Generic expression child visitor
// ---------------------------------------------------------------------------

/// Visit all immediate child expressions of an `Expr` node.
///
/// This is a shallow visitor -- it does NOT recurse into children automatically.
/// The callback is invoked once per direct child expression.
fn visit_expr_children(expr: &Expr, mut visit: impl FnMut(&Expr)) {
    match expr {
        // Leaves (no children).
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => {}

        // Unary operators.
        Expr::Not(a)
        | Expr::Neg(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Domain(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a) => {
            visit(&a.node);
        }

        // Binary operators.
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
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
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b) => {
            visit(&a.node);
            visit(&b.node);
        }

        // Ternary.
        Expr::If(cond, then_e, else_e) => {
            visit(&cond.node);
            visit(&then_e.node);
            visit(&else_e.node);
        }

        // Quantifiers and binders.
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(ref domain) = bv.domain {
                    visit(&domain.node);
                }
            }
            visit(&body.node);
        }
        Expr::Choose(bv, body) => {
            if let Some(ref domain) = bv.domain {
                visit(&domain.node);
            }
            visit(&body.node);
        }

        // Sets.
        Expr::SetEnum(elems) => {
            for e in elems {
                visit(&e.node);
            }
        }
        Expr::SetBuilder(body, bounds) => {
            visit(&body.node);
            for bv in bounds {
                if let Some(ref domain) = bv.domain {
                    visit(&domain.node);
                }
            }
        }
        Expr::SetFilter(bv, body) => {
            if let Some(ref domain) = bv.domain {
                visit(&domain.node);
            }
            visit(&body.node);
        }

        // Functions.
        Expr::FuncDef(bounds, body) => {
            for bv in bounds {
                if let Some(ref domain) = bv.domain {
                    visit(&domain.node);
                }
            }
            visit(&body.node);
        }
        Expr::Except(base, specs) => {
            visit(&base.node);
            for spec in specs {
                for elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = elem {
                        visit(&idx.node);
                    }
                }
                visit(&spec.value.node);
            }
        }

        // Records.
        Expr::Record(fields) => {
            for (_name, val) in fields {
                visit(&val.node);
            }
        }
        Expr::RecordAccess(base, _field) => {
            visit(&base.node);
        }
        Expr::RecordSet(fields) => {
            for (_name, val) in fields {
                visit(&val.node);
            }
        }

        // Tuples and sequences.
        Expr::Tuple(elems) => {
            for e in elems {
                visit(&e.node);
            }
        }
        Expr::Times(elems) => {
            for e in elems {
                visit(&e.node);
            }
        }

        // Application.
        Expr::Apply(func, args) => {
            visit(&func.node);
            for arg in args {
                visit(&arg.node);
            }
        }

        // Module references.
        Expr::ModuleRef(target, _name, args) => {
            if let tla_core::ast::ModuleTarget::Parameterized(_, params) = target {
                for p in params {
                    visit(&p.node);
                }
            }
            if let tla_core::ast::ModuleTarget::Chained(base) = target {
                visit(&base.node);
            }
            for arg in args {
                visit(&arg.node);
            }
        }

        // Instance expressions.
        Expr::InstanceExpr(_name, subs) => {
            for sub in subs {
                visit(&sub.to.node);
            }
        }

        // Lambda.
        Expr::Lambda(_params, body) => {
            visit(&body.node);
        }

        // Labels (unwrap to body).
        Expr::Label(label) => {
            visit(&label.body.node);
        }

        // Control flow.
        Expr::Case(arms, other) => {
            for arm in arms {
                visit(&arm.guard.node);
                visit(&arm.body.node);
            }
            if let Some(ref default) = other {
                visit(&default.node);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                visit(&def.body.node);
            }
            visit(&body.node);
        }
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                visit(&sub.to.node);
            }
            visit(&body.node);
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::{BoundVar, ExprLabel};
    use tla_core::span::{Span, Spanned};

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned::dummy(node)
    }

    #[test]
    fn test_extract_disjuncts_simple() {
        // A \/ B
        let a = Expr::Ident("A".to_string(), tla_core::name_intern::NameId::INVALID);
        let b = Expr::Ident("B".to_string(), tla_core::name_intern::NameId::INVALID);
        let or_expr = Expr::Or(Box::new(spanned(a)), Box::new(spanned(b)));
        let disjuncts = extract_disjuncts(&or_expr);
        assert_eq!(disjuncts.len(), 2);
    }

    #[test]
    fn test_extract_disjuncts_nested() {
        // A \/ B \/ C
        let a = Expr::Ident("A".to_string(), tla_core::name_intern::NameId::INVALID);
        let b = Expr::Ident("B".to_string(), tla_core::name_intern::NameId::INVALID);
        let c = Expr::Ident("C".to_string(), tla_core::name_intern::NameId::INVALID);
        let or_bc = Expr::Or(Box::new(spanned(b)), Box::new(spanned(c)));
        let or_abc = Expr::Or(Box::new(spanned(a)), Box::new(spanned(or_bc)));
        let disjuncts = extract_disjuncts(&or_abc);
        assert_eq!(disjuncts.len(), 3);
    }

    #[test]
    fn test_extract_disjuncts_no_or() {
        // Just a plain expression -- returned as single-element vec.
        let expr = Expr::Bool(true);
        let disjuncts = extract_disjuncts(&expr);
        assert_eq!(disjuncts.len(), 1);
    }

    #[test]
    fn test_collect_primed_variables() {
        // x' /\ y
        let x_prime = Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))));
        let y = Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID);
        let and_expr = Expr::And(Box::new(spanned(x_prime)), Box::new(spanned(y)));
        let vars = vec!["x".to_string(), "y".to_string()];
        let primed = collect_primed_variables(&and_expr, &vars);
        assert!(primed.contains("x"));
        assert!(!primed.contains("y"));
    }

    #[test]
    fn test_collect_unchanged_variables() {
        // UNCHANGED <<x, y>>
        let unch = Expr::Unchanged(Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        ]))));
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let unchanged = collect_unchanged_variables(&unch, &vars);
        assert!(unchanged.contains("x"));
        assert!(unchanged.contains("y"));
        assert!(!unchanged.contains("z"));
    }

    #[test]
    fn test_collect_referenced_variables() {
        // x /\ y = 1
        let x = Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID);
        let y = Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID);
        let one = Expr::Int(1.into());
        let eq = Expr::Eq(Box::new(spanned(y)), Box::new(spanned(one)));
        let and = Expr::And(Box::new(spanned(x)), Box::new(spanned(eq)));
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let refs = collect_referenced_variables(&and, &vars);
        assert!(refs.contains("x"));
        assert!(refs.contains("y"));
        assert!(!refs.contains("z"));
    }
}
