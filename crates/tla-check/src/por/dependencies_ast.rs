// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AST-level dependency extraction for canonical POR action analysis.

use tla_core::ast::{CaseArm, ExceptPathElement, ExceptSpec, Expr, ModuleTarget};
use tla_core::Spanned;

use crate::var_index::VarIndex;

use super::dependencies::ActionDependencies;

/// Extract dependencies from a canonical action expression.
pub(super) fn extract_action_dependencies(expr: &Spanned<Expr>) -> ActionDependencies {
    let mut deps = ActionDependencies::new();
    extract_dependencies_ast_expr(&expr.node, &mut deps);
    deps
}

/// Extract dependencies from an AST expression (fallback case)
pub(crate) fn extract_dependencies_ast_expr(expr: &Expr, deps: &mut ActionDependencies) {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => {}
        Expr::Ident(_, _) => {}
        Expr::StateVar(_, idx, _) => {
            deps.add_read(VarIndex(*idx));
        }
        Expr::OpRef(_) => {}

        Expr::Apply(op, args) => {
            extract_dependencies_ast_expr(&op.node, deps);
            for arg in args {
                extract_dependencies_ast_expr(&arg.node, deps);
            }
        }
        Expr::ModuleRef(target, _, args) => {
            match target {
                ModuleTarget::Parameterized(_, params) => {
                    for p in params {
                        extract_dependencies_ast_expr(&p.node, deps);
                    }
                }
                ModuleTarget::Chained(base) => {
                    extract_dependencies_ast_expr(&base.node, deps);
                }
                ModuleTarget::Named(_) => {}
            }
            for arg in args {
                extract_dependencies_ast_expr(&arg.node, deps);
            }
        }
        Expr::InstanceExpr(_, _) => {}
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                extract_dependencies_ast_expr(&sub.to.node, deps);
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }
        Expr::Lambda(_, body) => {
            extract_dependencies_ast_expr(&body.node, deps);
        }

        Expr::And(left, right)
        | Expr::Or(left, right)
        | Expr::Implies(left, right)
        | Expr::Equiv(left, right) => {
            extract_dependencies_ast_expr(&left.node, deps);
            extract_dependencies_ast_expr(&right.node, deps);
        }
        Expr::Not(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }

        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    extract_dependencies_ast_expr(&domain.node, deps);
                }
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }
        Expr::Choose(bound, body) => {
            if let Some(domain) = &bound.domain {
                extract_dependencies_ast_expr(&domain.node, deps);
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }

        Expr::SetEnum(elems) => {
            for e in elems {
                extract_dependencies_ast_expr(&e.node, deps);
            }
        }
        Expr::SetBuilder(body, bounds) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    extract_dependencies_ast_expr(&domain.node, deps);
                }
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }
        Expr::SetFilter(bound, body) => {
            if let Some(domain) = &bound.domain {
                extract_dependencies_ast_expr(&domain.node, deps);
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }
        Expr::In(left, right)
        | Expr::NotIn(left, right)
        | Expr::Subseteq(left, right)
        | Expr::Union(left, right)
        | Expr::Intersect(left, right)
        | Expr::SetMinus(left, right) => {
            extract_dependencies_ast_expr(&left.node, deps);
            extract_dependencies_ast_expr(&right.node, deps);
        }
        Expr::Powerset(inner) | Expr::BigUnion(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }

        Expr::FuncDef(bounds, body) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    extract_dependencies_ast_expr(&domain.node, deps);
                }
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }
        Expr::FuncApply(func, arg) => {
            extract_dependencies_ast_expr(&func.node, deps);
            extract_dependencies_ast_expr(&arg.node, deps);
        }
        Expr::Domain(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }
        Expr::Except(base, specs) => {
            extract_dependencies_ast_expr(&base.node, deps);
            for ExceptSpec { path, value } in specs {
                for elem in path {
                    if let ExceptPathElement::Index(idx) = elem {
                        extract_dependencies_ast_expr(&idx.node, deps);
                    }
                }
                extract_dependencies_ast_expr(&value.node, deps);
            }
        }
        Expr::FuncSet(domain, range) => {
            extract_dependencies_ast_expr(&domain.node, deps);
            extract_dependencies_ast_expr(&range.node, deps);
        }

        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, value) in fields {
                extract_dependencies_ast_expr(&value.node, deps);
            }
        }
        Expr::RecordAccess(record, _) => {
            extract_dependencies_ast_expr(&record.node, deps);
        }

        Expr::Tuple(elems) | Expr::Times(elems) => {
            for e in elems {
                extract_dependencies_ast_expr(&e.node, deps);
            }
        }

        Expr::Prime(inner) => {
            if let Expr::StateVar(_, idx, _) = &inner.node {
                deps.add_write(VarIndex(*idx));
            } else {
                extract_dependencies_ast_expr(&inner.node, deps);
            }
        }
        Expr::Always(inner) | Expr::Eventually(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }
        Expr::LeadsTo(left, right)
        | Expr::WeakFair(left, right)
        | Expr::StrongFair(left, right) => {
            extract_dependencies_ast_expr(&left.node, deps);
            extract_dependencies_ast_expr(&right.node, deps);
        }

        Expr::Enabled(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }
        Expr::Unchanged(inner) => {
            extract_unchanged_dependencies(&inner.node, deps);
        }

        Expr::If(cond, then_e, else_e) => {
            extract_dependencies_ast_expr(&cond.node, deps);
            extract_dependencies_ast_expr(&then_e.node, deps);
            extract_dependencies_ast_expr(&else_e.node, deps);
        }
        Expr::Case(arms, other) => {
            for CaseArm { guard, body } in arms {
                extract_dependencies_ast_expr(&guard.node, deps);
                extract_dependencies_ast_expr(&body.node, deps);
            }
            if let Some(other) = other {
                extract_dependencies_ast_expr(&other.node, deps);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                extract_dependencies_ast_expr(&def.body.node, deps);
            }
            extract_dependencies_ast_expr(&body.node, deps);
        }

        Expr::Eq(left, right) => {
            // Detect identity assignments: `x' = x` where both sides refer
            // to the same state variable. This is semantically equivalent to
            // `UNCHANGED x` — the identity function — and commutes with all
            // operations. Record as an identity write instead of a real write
            // to enable POR for specs that use explicit `x' = x` instead of
            // `UNCHANGED x`. Part of #3993.
            if let Some(identity_var) = detect_identity_assignment(left, right) {
                deps.add_unchanged(identity_var);
            }
            // Part of #3993 Phase 11: detect identity through IF/THEN/ELSE and CASE.
            // `x' = IF cond THEN x ELSE x` is equivalent to UNCHANGED x.
            else if let Some(identity_var) = detect_identity_through_if(left, right) {
                // The condition expression may read state variables — track those reads.
                extract_condition_reads_from_branching(right, deps);
                deps.add_unchanged(identity_var);
            }
            // Part of #3993 Phase 11: detect EXCEPT identity pattern.
            // `f' = [f EXCEPT ![k] = f[k]]` means the action reads f[k] and
            // writes back the same value — a no-op on f. Treat as identity.
            else if let Some(identity_var) = detect_except_identity(left, right) {
                deps.add_unchanged(identity_var);
            }
            // Part of #3993 Phase 11: constant write detection.
            // `x' = 0` (state-independent RHS) means the action writes x but
            // does NOT read x. Record as a write without an implicit read.
            else if let Some(write_var) = detect_constant_write(left, right) {
                deps.add_write(write_var);
                // Do NOT add a read for the written variable — the value is constant.
                // Still extract reads from the LHS Prime(StateVar) and RHS constant
                // (no state reads from constants by definition).
            } else {
                extract_dependencies_ast_expr(&left.node, deps);
                extract_dependencies_ast_expr(&right.node, deps);
            }
        }
        Expr::Neq(left, right)
        | Expr::Lt(left, right)
        | Expr::Leq(left, right)
        | Expr::Gt(left, right)
        | Expr::Geq(left, right)
        | Expr::Add(left, right)
        | Expr::Sub(left, right)
        | Expr::Mul(left, right)
        | Expr::Div(left, right)
        | Expr::IntDiv(left, right)
        | Expr::Mod(left, right)
        | Expr::Pow(left, right)
        | Expr::Range(left, right) => {
            extract_dependencies_ast_expr(&left.node, deps);
            extract_dependencies_ast_expr(&right.node, deps);
        }
        Expr::Neg(inner) => {
            extract_dependencies_ast_expr(&inner.node, deps);
        }

        Expr::Label(label) => {
            extract_dependencies_ast_expr(&label.body.node, deps);
        }
    }
}

/// Extract dependencies from an UNCHANGED expression.
///
/// `UNCHANGED x` means `x' = x` — the identity function on `x`. For POR
/// independence analysis, the identity function commutes with all operations:
///
/// - It commutes with reads (reading x is unaffected by x' = x).
/// - It commutes with real writes (A: x' = expr, B: x' = x → both orders
///   yield x = expr because UNCHANGED preserves whatever value is there).
/// - It commutes with other identity writes (both preserve x).
///
/// Therefore, UNCHANGED x is recorded only as an identity write — NOT as
/// a read. The "read" in `x' = x` is vacuous for commutativity: the action
/// doesn't observe x to make a decision, it just preserves the value.
///
/// This is the key insight that enables POR for typical TLA+ specs where
/// every action must mention all variables via UNCHANGED.
fn extract_unchanged_dependencies(expr: &Expr, deps: &mut ActionDependencies) {
    match expr {
        Expr::StateVar(_, idx, _) => {
            let var = VarIndex(*idx);
            // Only record as identity write. Do NOT add_read — the "read"
            // in UNCHANGED x is vacuous for commutativity purposes.
            deps.add_unchanged(var);
        }
        Expr::Tuple(items) | Expr::Times(items) => {
            for item in items {
                extract_unchanged_dependencies(&item.node, deps);
            }
        }
        Expr::Label(label) => {
            extract_unchanged_dependencies(&label.body.node, deps);
        }
        _ => {
            extract_dependencies_ast_expr(expr, deps);
        }
    }
}

/// Detect the identity assignment pattern `x' = x` (or `x = x'`).
///
/// Returns `Some(VarIndex)` when the equality compares a primed state variable
/// with the same unprimed state variable — meaning the action preserves that
/// variable's value. This is semantically equivalent to `UNCHANGED x`.
///
/// The `EXCEPT` identity pattern (`f' = [f EXCEPT ![k] = f[k]]`) is handled
/// separately by `detect_except_identity`. This function only handles the
/// simple `x' = x` scalar case.
///
/// Part of #3993: many TLA+ specs use explicit `x' = x` instead of `UNCHANGED x`.
/// Without this detection, POR treats them as real writes, making virtually all
/// actions dependent and defeating reduction.
fn detect_identity_assignment(left: &Spanned<Expr>, right: &Spanned<Expr>) -> Option<VarIndex> {
    // Pattern 1: x' = x  (Prime(StateVar(idx)) = StateVar(idx))
    if let Expr::Prime(primed) = &left.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if let Expr::StateVar(_, rhs_idx, _) = &right.node {
                if prime_idx == rhs_idx {
                    return Some(VarIndex(*prime_idx));
                }
            }
        }
    }

    // Pattern 2: x = x'  (StateVar(idx) = Prime(StateVar(idx)))
    // TLA+ equality is symmetric; some specs may write it this way.
    if let Expr::Prime(primed) = &right.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if let Expr::StateVar(_, lhs_idx, _) = &left.node {
                if prime_idx == lhs_idx {
                    return Some(VarIndex(*prime_idx));
                }
            }
        }
    }

    None
}

/// Detect identity assignment through IF/THEN/ELSE:
/// `x' = IF cond THEN x ELSE x` is equivalent to `x' = x`.
///
/// This pattern arises in PlusCal-generated and hand-written specs where
/// an assignment conditionally updates a variable:
///   `x' = IF cond THEN expr ELSE x`
/// When BOTH branches resolve to the unprimed variable, it's an identity.
///
/// Part of #3993 Phase 11: strengthen identity detection through branching.
fn detect_identity_through_if(left: &Spanned<Expr>, right: &Spanned<Expr>) -> Option<VarIndex> {
    // Pattern: x' = IF cond THEN x ELSE x
    if let Expr::Prime(primed) = &left.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if is_identity_preserving_expr(&right.node, *prime_idx) {
                return Some(VarIndex(*prime_idx));
            }
        }
    }

    // Symmetric: IF cond THEN x ELSE x = x'
    if let Expr::Prime(primed) = &right.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if is_identity_preserving_expr(&left.node, *prime_idx) {
                return Some(VarIndex(*prime_idx));
            }
        }
    }

    None
}

/// Check if an expression always evaluates to the current value of a state
/// variable, making it an identity-preserving expression.
///
/// Returns true for:
/// - `StateVar(idx)` — direct reference to the variable
/// - `IF cond THEN <identity> ELSE <identity>` — both branches preserve
/// - `CASE ... -> <identity> [] ... -> <identity> [] OTHER -> <identity>`
/// - `LET ... IN <identity>` — body preserves through let bindings
///
/// Part of #3993 Phase 11.
fn is_identity_preserving_expr(expr: &Expr, var_idx: u16) -> bool {
    match expr {
        Expr::StateVar(_, idx, _) => *idx == var_idx,

        Expr::If(_, then_e, else_e) => {
            is_identity_preserving_expr(&then_e.node, var_idx)
                && is_identity_preserving_expr(&else_e.node, var_idx)
        }

        Expr::Case(arms, other) => {
            let arms_identity = arms
                .iter()
                .all(|arm| is_identity_preserving_expr(&arm.body.node, var_idx));
            let other_identity = other
                .as_ref()
                .map_or(true, |o| is_identity_preserving_expr(&o.node, var_idx));
            arms_identity && other_identity
        }

        Expr::Let(_, body) => is_identity_preserving_expr(&body.node, var_idx),

        Expr::Label(label) => is_identity_preserving_expr(&label.body.node, var_idx),

        _ => false,
    }
}

/// Detect the EXCEPT identity pattern: `f' = [f EXCEPT ![k] = f[k]]`.
///
/// This means the action updates function `f` at key `k` with the current
/// value of `f[k]` — a no-op. The function is preserved unchanged.
///
/// Returns `Some(VarIndex)` when ALL EXCEPT specs are identity updates:
/// each spec has a single `Index(key_expr)` path element and its value is
/// `FuncApply(StateVar(idx), key_expr)` where `key_expr` structurally
/// matches the path key. Mixed EXCEPT specs (some identity, some not) are
/// conservatively treated as non-identity (returns `None`).
///
/// Part of #3993 Phase 11: many TLA+ specs use `[f EXCEPT ![k] = f[k]]`
/// in action conjuncts to express "f is unchanged at key k". Without this
/// detection, POR treats these as real writes, blocking independence.
fn detect_except_identity(left: &Spanned<Expr>, right: &Spanned<Expr>) -> Option<VarIndex> {
    // Pattern: f' = [f EXCEPT ![k] = f[k]]
    if let Expr::Prime(primed) = &left.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if let Expr::Except(base, specs) = &right.node {
                if let Expr::StateVar(_, base_idx, _) = &base.node {
                    if *prime_idx == *base_idx && is_except_all_identity(*base_idx, specs) {
                        return Some(VarIndex(*prime_idx));
                    }
                }
            }
        }
    }

    // Symmetric: [f EXCEPT ![k] = f[k]] = f'
    if let Expr::Prime(primed) = &right.node {
        if let Expr::StateVar(_, prime_idx, _) = &primed.node {
            if let Expr::Except(base, specs) = &left.node {
                if let Expr::StateVar(_, base_idx, _) = &base.node {
                    if *prime_idx == *base_idx && is_except_all_identity(*base_idx, specs) {
                        return Some(VarIndex(*prime_idx));
                    }
                }
            }
        }
    }

    None
}

/// Check whether ALL EXCEPT specs are identity updates for the given
/// state variable. An identity EXCEPT spec has the form:
///   `![k] = f[k]`
/// i.e., a single `Index(key_expr)` path element and a value of
/// `FuncApply(StateVar(var_idx), key_expr)` where key_expr matches
/// structurally.
///
/// Part of #3993 Phase 11.
fn is_except_all_identity(var_idx: u16, specs: &[ExceptSpec]) -> bool {
    if specs.is_empty() {
        return false; // Degenerate case — treat as non-identity
    }

    specs.iter().all(|spec| {
        // Only handle single-element index paths: ![k]
        // Multi-element paths like ![k1][k2] or field paths like !.field
        // are not handled (conservative: return false).
        if spec.path.len() != 1 {
            return false;
        }

        let key_expr = match &spec.path[0] {
            ExceptPathElement::Index(idx) => &idx.node,
            ExceptPathElement::Field(_) => return false, // Record field — not handled
        };

        // Value must be FuncApply(StateVar(var_idx), key_expr) — i.e., f[k]
        if let Expr::FuncApply(func, arg) = &spec.value.node {
            if let Expr::StateVar(_, func_idx, _) = &func.node {
                *func_idx == var_idx && exprs_structurally_equal(key_expr, &arg.node)
            } else {
                false
            }
        } else {
            false
        }
    })
}

/// Conservative structural equality check for AST expressions.
///
/// Returns `true` when `a` and `b` have the same shape and leaf values.
/// Only handles simple, commonly-occurring expression forms; returns
/// `false` for anything complex (conservative for soundness).
///
/// Part of #3993 Phase 11: used by EXCEPT identity detection to compare
/// the key expression in the path with the key expression in the value.
fn exprs_structurally_equal(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Bool(x), Expr::Bool(y)) => x == y,
        (Expr::Int(x), Expr::Int(y)) => x == y,
        (Expr::String(x), Expr::String(y)) => x == y,
        (Expr::Ident(name_a, _), Expr::Ident(name_b, _)) => name_a == name_b,
        (Expr::StateVar(_, idx_a, _), Expr::StateVar(_, idx_b, _)) => idx_a == idx_b,
        (Expr::OpRef(a), Expr::OpRef(b)) => a == b,
        (Expr::Add(la, ra), Expr::Add(lb, rb))
        | (Expr::Sub(la, ra), Expr::Sub(lb, rb))
        | (Expr::Mul(la, ra), Expr::Mul(lb, rb))
        | (Expr::Div(la, ra), Expr::Div(lb, rb)) => {
            exprs_structurally_equal(&la.node, &lb.node)
                && exprs_structurally_equal(&ra.node, &rb.node)
        }
        (Expr::Neg(ia), Expr::Neg(ib)) => exprs_structurally_equal(&ia.node, &ib.node),
        (Expr::FuncApply(fa, aa), Expr::FuncApply(fb, ab)) => {
            exprs_structurally_equal(&fa.node, &fb.node)
                && exprs_structurally_equal(&aa.node, &ab.node)
        }
        (Expr::Tuple(ea), Expr::Tuple(eb)) => {
            ea.len() == eb.len()
                && ea
                    .iter()
                    .zip(eb.iter())
                    .all(|(x, y)| exprs_structurally_equal(&x.node, &y.node))
        }
        // Conservative: anything else is not structurally equal
        _ => false,
    }
}

/// Detect a constant write pattern: `x' = <constant>` where the RHS
/// does not depend on any state variable.
///
/// Returns `Some(VarIndex)` when the LHS is a primed state variable and
/// the RHS is state-independent. This means the action writes to x but
/// does not READ x — the write value is determined entirely by constants.
///
/// This matters for POR because a normal `x' = x + 1` records both a
/// write AND a read of x. But `x' = 0` only needs a write, not a read.
/// Fewer read dependencies means more chances for independence.
///
/// Part of #3993 Phase 11.
fn detect_constant_write(left: &Spanned<Expr>, right: &Spanned<Expr>) -> Option<VarIndex> {
    // Pattern: x' = <constant>
    if let Expr::Prime(primed) = &left.node {
        if let Expr::StateVar(_, idx, _) = &primed.node {
            if is_state_independent_expr(&right.node) {
                return Some(VarIndex(*idx));
            }
        }
    }

    // Symmetric: <constant> = x'
    if let Expr::Prime(primed) = &right.node {
        if let Expr::StateVar(_, idx, _) = &primed.node {
            if is_state_independent_expr(&left.node) {
                return Some(VarIndex(*idx));
            }
        }
    }

    None
}

/// Extract state variable reads from condition expressions in branching
/// constructs (IF/CASE) that were classified as identity-preserving.
///
/// When `x' = IF cond THEN x ELSE x` is detected as an identity write,
/// we still need to track any state variable reads in `cond` because
/// the guard expression observes state.
///
/// Part of #3993 Phase 11.
fn extract_condition_reads_from_branching(expr: &Spanned<Expr>, deps: &mut ActionDependencies) {
    match &expr.node {
        Expr::If(cond, then_e, else_e) => {
            // The condition reads state variables
            extract_dependencies_ast_expr(&cond.node, deps);
            // Recurse into branches in case they are nested IF/CASE
            extract_condition_reads_from_branching(then_e, deps);
            extract_condition_reads_from_branching(else_e, deps);
        }
        Expr::Case(arms, other) => {
            for CaseArm { guard, body } in arms {
                extract_dependencies_ast_expr(&guard.node, deps);
                extract_condition_reads_from_branching(body, deps);
            }
            if let Some(other) = other {
                extract_condition_reads_from_branching(other, deps);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                extract_dependencies_ast_expr(&def.body.node, deps);
            }
            extract_condition_reads_from_branching(body, deps);
        }
        Expr::Label(label) => {
            extract_condition_reads_from_branching(&label.body, deps);
        }
        // Terminal identity expression (StateVar) — no additional reads needed
        _ => {}
    }
}

/// Check if an expression is state-independent (a pure constant that does
/// not read any state variable). Used to classify "constant writes" like
/// `x' = 0` or `x' = TRUE` which don't conflict with reads of x from
/// other actions (since the write value doesn't depend on x's current value).
///
/// Note: constant writes still conflict with other writes to the same variable
/// and with reads of x (because they change x's value). The optimization is
/// that two actions both doing constant writes to DIFFERENT variables are
/// independent even if one reads the other's write target — wait, that's
/// the same as the normal independence check. The real win: a constant write
/// `x' = 0` does NOT add a READ dependency on x, unlike `x' = x + 1`.
///
/// Part of #3993 Phase 11.
fn is_state_independent_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => true,
        Expr::Ident(_, _) | Expr::OpRef(_) => {
            // Identifiers could refer to constants or operators — conservatively
            // treat as potentially state-dependent since we can't resolve here.
            false
        }
        Expr::StateVar(_, _, _) => false,
        Expr::Prime(_) => false,

        Expr::Tuple(elems) | Expr::SetEnum(elems) | Expr::Times(elems) => {
            elems.iter().all(|e| is_state_independent_expr(&e.node))
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            fields.iter().all(|(_, v)| is_state_independent_expr(&v.node))
        }

        Expr::Not(inner) | Expr::Neg(inner) => is_state_independent_expr(&inner.node),

        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::IntDiv(l, r)
        | Expr::Mod(l, r)
        | Expr::Pow(l, r)
        | Expr::Range(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Leq(l, r)
        | Expr::Gt(l, r)
        | Expr::Geq(l, r) => {
            is_state_independent_expr(&l.node) && is_state_independent_expr(&r.node)
        }

        Expr::If(cond, then_e, else_e) => {
            is_state_independent_expr(&cond.node)
                && is_state_independent_expr(&then_e.node)
                && is_state_independent_expr(&else_e.node)
        }

        Expr::Label(label) => is_state_independent_expr(&label.body.node),

        // Conservative: anything else could read state.
        _ => false,
    }
}
