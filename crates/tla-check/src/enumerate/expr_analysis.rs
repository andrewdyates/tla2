// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression analysis predicates and collectors for the enumerate module.
//!
//! This module contains pure, stateless functions that walk `Expr` AST trees
//! to check structural properties (contains primes? contains OR? references
//! state vars? is a guard?) or collect sets of names (bound names, primed var
//! refs, state var refs). These functions are used by the core enumeration
//! logic, guard checking, operator expansion, and symbolic assignment analysis.

use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::sync::Arc;
use smallvec::SmallVec;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::eval::EvalCtx;
use crate::expr_visitor::{walk_spanned_expr, ExprVisitor};

// Part of #3063/#3962: Thread-local caches for structural AST analysis.
// These queries walk the immutable AST to check structural properties (contains primes,
// is action-level, needs prime binding). Since the AST and operator definitions are
// fixed during model checking, the results are deterministic per AST node pointer.
// Caching eliminates 4.4% of per-state overhead (302 walk_expr samples in profiling).
//
// Part of #3962 Wave 25: Consolidated 3 separate thread_locals into a single struct.
// Previously each was a separate `_tlv_get_addr` call on macOS (~5ns each). All three
// are cleared together in `clear_expr_analysis_caches()` and keyed by the same type.
// Now 1 TLS access covers all three caches.
struct ExprAnalysisCaches {
    might_need_prime_binding: FxHashMap<usize, bool>,
    expr_is_action_level: FxHashMap<usize, bool>,
    /// Part of #3073: Cache is_operator_reference_guard_unsafe results per AST node pointer.
    /// This visitor walks the AST to check if an expression contains an operator reference
    /// that could hide action-level content. The result depends only on the immutable AST
    /// and operator definitions, so it's deterministic per AST node pointer.
    /// Profiling showed 310+ samples (2% CPU) spent in this uncached visitor on MultiPaxos.
    is_operator_ref_guard_unsafe: FxHashMap<usize, bool>,
}

thread_local! {
    static EXPR_ANALYSIS_CACHES: RefCell<ExprAnalysisCaches> = RefCell::new(ExprAnalysisCaches {
        might_need_prime_binding: FxHashMap::default(),
        expr_is_action_level: FxHashMap::default(),
        is_operator_ref_guard_unsafe: FxHashMap::default(),
    });
}

/// Clear all thread-local expression analysis caches.
///
/// Must be called between model checking runs to prevent stale entries from
/// being returned when AST memory addresses are reused. These caches are
/// keyed by raw pointer (`usize`) without run discrimination, so stale
/// entries from a previous AST could silently return incorrect results.
pub(crate) fn clear_expr_analysis_caches() {
    EXPR_ANALYSIS_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        c.expr_is_action_level.clear();
        c.might_need_prime_binding.clear();
        c.is_operator_ref_guard_unsafe.clear();
    });
}

/// Check if an expression is an action-level expression that should use AST substitution
/// rather than call-by-value semantics. This checks for primed variables and UNCHANGED
/// in the expression itself AND in operator bodies that it calls.
/// Part of #141: Detect action arguments for higher-order action operators.
/// Delegated to generic visitor in expr_visitor.rs (Part of #1192 Wave 2).
/// Part of #3063: Cached per AST node pointer — result is deterministic since
/// AST and operator definitions are immutable during model checking.
pub(super) fn expr_is_action_level(ctx: &EvalCtx, expr: &Expr) -> bool {
    let key = expr as *const Expr as usize;
    EXPR_ANALYSIS_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        if let Some(&result) = c.expr_is_action_level.get(&key) {
            return result;
        }
        let result = crate::expr_visitor::expr_is_action_level_v(ctx, expr);
        c.expr_is_action_level.insert(key, result);
        result
    })
}

/// Collect state variable names referenced in an expression.
///
/// This is used for early filter evaluation: we can evaluate a filter as soon as
/// all its referenced variables are bound, rather than waiting for all variables.
pub(crate) fn collect_state_var_refs(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    state_vars: &[Arc<str>],
    refs: &mut FxHashSet<Arc<str>>,
) {
    let mut visitor = CollectStateVarRefsVisitor {
        ctx,
        state_vars,
        refs,
        visited_ops: FxHashSet::default(),
    };
    let _ = walk_spanned_expr(&mut visitor, expr);
}

struct CollectStateVarRefsVisitor<'a, 'b> {
    ctx: &'a EvalCtx,
    state_vars: &'a [Arc<str>],
    refs: &'b mut FxHashSet<Arc<str>>,
    visited_ops: FxHashSet<String>,
}

impl ExprVisitor for CollectStateVarRefsVisitor<'_, '_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                // O(1) registry lookup instead of O(n) linear scan over state_vars
                if let Some(idx) = self.ctx.var_registry().get(name) {
                    self.refs
                        .insert(Arc::clone(&self.state_vars[idx.as_usize()]));
                }
                if let Some(def) = self.ctx.get_op(name) {
                    // Part of #2464: Recurse into ALL operator bodies (including parameterized
                    // ones) to discover transitive state-var dependencies. Previously only
                    // zero-arg operators were traced, causing filters like WellFormed(head)
                    // to miss state vars accessed inside the operator body (e.g., `mem`
                    // accessed via LET RECURSIVE). This led to incorrect trigger_idx
                    // computation and early filter evaluation before all deps were bound.
                    if self.visited_ops.insert(name.clone()) {
                        let _ = walk_spanned_expr(self, &def.body);
                        self.visited_ops.remove(name);
                    }
                }
                Some(false)
            }
            // Preserve legacy behavior: Tuple and InstanceExpr are not traversed here.
            Expr::Tuple(_) | Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }

    fn should_short_circuit(&self, _partial: &Self::Output) -> bool {
        false
    }
}

/// Check if an expression contains primed variables.
pub(crate) fn expr_contains_prime(expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_prime_v(expr)
}

/// Flatten an And expression tree into a list of conjuncts (iterative to avoid stack overflow)
#[cfg(test)]
pub(super) fn flatten_and(expr: &Expr) -> Vec<&Expr> {
    let mut result = Vec::new();
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current {
            Expr::And(a, b) => {
                stack.push(&b.node);
                stack.push(&a.node);
            }
            _ => result.push(current),
        }
    }
    result
}

/// Flatten an And tree into a list of conjunct references (iterative to avoid stack overflow).
/// Phase H (#3073): returns references instead of clones — eliminates deep AST cloning
/// that was 18% of MultiPaxos runtime per profiling (designs/2026-03-08-3063-phase-g).
/// Part of #3897: Uses SmallVec<[_; 8]> to avoid heap allocation for typical conjunct lists.
pub(super) fn flatten_and_spanned<'a>(
    expr: &'a Spanned<Expr>,
    out: &mut SmallVec<[&'a Spanned<Expr>; 8]>,
) {
    let mut stack: SmallVec<[&Spanned<Expr>; 8]> = SmallVec::new();
    stack.push(expr);
    while let Some(current) = stack.pop() {
        match &current.node {
            Expr::And(a, b) => {
                // Push right first so left is processed first (maintains order)
                stack.push(b);
                stack.push(a);
            }
            _ => out.push(current),
        }
    }
}

#[cfg(test)]
pub(super) fn expr_contains_ident(expr: &Expr, name: &str) -> bool {
    crate::expr_visitor::expr_contains_ident_v(expr, name)
}

#[cfg(test)]
pub(super) fn expr_contains_exists(expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_exists_v(expr)
}

/// Check if an expression contains primed variables, following operator calls.
/// Delegated to generic visitor in expr_visitor.rs (Part of #1192 Wave 2).
pub(super) fn expr_contains_prime_ctx(ctx: &EvalCtx, expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_prime_ctx_v(ctx, expr)
}

/// Check if an expression contains ANY primed variables, regardless of context.
/// This is used for implication LHS where even `x' = expr` patterns are boolean conditions.
pub(crate) fn expr_contains_any_prime(expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_any_prime_v(expr)
}

fn expr_contains_prime_not_assignment(expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_prime_not_assignment_v(expr)
}

/// Check if an expression might contain an action predicate via operator reference.
/// This catches cases like `HCnxt => t >= 1` where HCnxt is an operator that contains primes,
/// and bare operator references like `UpdateOpOrder` that might contain `Serializable'`.
///
/// IMPORTANT: Comparison expressions like `rcvd01(self) >= N - T` might contain hidden primed
/// variables in operator bodies (e.g., `rcvd01(self) == Cardinality({m \in rcvd'[self] : ...})`).
/// We must check if any operand contains an operator application that might expand to primed vars.
pub(super) fn might_contain_action_predicate(expr: &Expr) -> bool {
    match expr {
        // Implications might have action predicates in LHS (e.g., HCnxt => t >= 1)
        Expr::Implies(a, _) => {
            matches!(&a.node, Expr::Ident(_, _) | Expr::Apply(_, _))
                || expr_contains_prime_not_assignment(&a.node)
        }
        // Equivalences might have action predicates on either side
        Expr::Equiv(a, b) => {
            matches!(&a.node, Expr::Ident(_, _) | Expr::Apply(_, _))
                || matches!(&b.node, Expr::Ident(_, _) | Expr::Apply(_, _))
                || expr_contains_prime_not_assignment(&a.node)
                || expr_contains_prime_not_assignment(&b.node)
        }
        // Bare operator references might expand to contain action predicates (primed expressions).
        // E.g., `UpdateOpOrder` containing `Serializable'` which validates opOrder' constraints.
        // We conservatively assume all operator references might contain action predicates
        // since we can't cheaply determine this without expanding the operator body.
        Expr::Ident(_, _) | Expr::Apply(_, _) => true,
        // Comparison and arithmetic expressions might contain operator applications that have
        // hidden primed variables in their bodies. Check recursively.
        // This catches patterns like `rcvd01(self) >= N - T` where rcvd01's body contains rcvd'.
        // Special case: x' = expr is an assignment, not a predicate to validate.
        // Don't re-evaluate assignments where LHS is a primed variable and RHS is non-primed.
        // This prevents RandomElement from being called again during validation.
        Expr::Eq(a, b) => {
            // Check if this is a simple assignment: x' = expr or expr = x'
            let is_prime_assignment = matches!(
                (&a.node, &b.node),
                (Expr::Prime(inner), _) if matches!(inner.node, Expr::Ident(_, _) | Expr::StateVar(_, _, _)) && !expr_contains_any_prime(&b.node)
            ) || matches!(
                (&a.node, &b.node),
                (_, Expr::Prime(inner)) if matches!(inner.node, Expr::Ident(_, _) | Expr::StateVar(_, _, _)) && !expr_contains_any_prime(&a.node)
            );
            if is_prime_assignment {
                // This is a simple primed variable assignment - don't re-validate
                false
            } else {
                // Not a simple assignment - check for action predicates
                expr_contains_operator_application(&a.node)
                    || expr_contains_operator_application(&b.node)
                    || expr_contains_prime_not_assignment(&a.node)
                    || expr_contains_prime_not_assignment(&b.node)
            }
        }
        Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Neq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b) => {
            expr_contains_operator_application(&a.node)
                || expr_contains_operator_application(&b.node)
                || expr_contains_prime_not_assignment(&a.node)
                || expr_contains_prime_not_assignment(&b.node)
        }
        Expr::Not(a) | Expr::Neg(a) => {
            expr_contains_operator_application(&a.node)
                || expr_contains_prime_not_assignment(&a.node)
        }
        // Part of #176: OR/AND expressions might contain operator applications with hidden primes.
        // This catches patterns like `\/ ... MsgCount(self) >= 1 ... \/ ...` where MsgCount
        // contains rcvd' but no syntactic prime is visible at the OR level.
        Expr::Or(a, b) | Expr::And(a, b) => {
            expr_contains_operator_application(&a.node)
                || expr_contains_operator_application(&b.node)
                || expr_contains_prime_not_assignment(&a.node)
                || expr_contains_prime_not_assignment(&b.node)
        }
        _ => expr_contains_prime_not_assignment(expr),
    }
}

/// Check if an expression contains an operator application (Apply or zero-arg Ident operator).
/// This is used to detect expressions that might have hidden primed variables in operator bodies.
fn expr_contains_operator_application(expr: &Expr) -> bool {
    crate::expr_visitor::expr_contains_operator_application_v(expr)
}

/// Check if an expression might need prime bindings because it references operators
/// that contain primed variables (based on the `contains_prime` field computed during
/// semantic analysis).
/// Delegated to generic visitor in expr_visitor.rs (Part of #1192 Wave 2).
/// Part of #3063: Cached per AST node pointer — result is deterministic since
/// AST and operator definitions are immutable during model checking.
pub(super) fn might_need_prime_binding(ctx: &EvalCtx, expr: &Expr) -> bool {
    let key = expr as *const Expr as usize;
    EXPR_ANALYSIS_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        if let Some(&result) = c.might_need_prime_binding.get(&key) {
            return result;
        }
        let result = crate::expr_visitor::might_need_prime_binding_v(ctx, expr);
        c.might_need_prime_binding.insert(key, result);
        result
    })
}

/// True if this expression contains an operator reference that could hide action-level content.
/// Delegated to generic visitor in expr_visitor.rs (Part of #1192 Wave 2).
/// Part of #3073: Cached per AST node pointer — result is deterministic since
/// AST and operator definitions are immutable during model checking.
pub(super) fn is_operator_reference_guard_unsafe(ctx: &EvalCtx, expr: &Expr) -> bool {
    let key = expr as *const Expr as usize;
    EXPR_ANALYSIS_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        if let Some(&result) = c.is_operator_ref_guard_unsafe.get(&key) {
            return result;
        }
        let result = crate::expr_visitor::is_operator_reference_guard_unsafe_v(ctx, expr);
        c.is_operator_ref_guard_unsafe.insert(key, result);
        result
    })
}

/// Check if an expression is a guard (doesn't contain primed variables)
pub(super) fn is_guard_expression(expr: &Expr) -> bool {
    crate::expr_visitor::is_guard_expression_v(expr)
}

/// Check if an expression references any state variables (non-primed).
/// This is used to prevent eager evaluation of expressions that depend on current state.
pub(super) fn expr_references_state_vars(expr: &Expr, vars: &[Arc<str>]) -> bool {
    crate::expr_visitor::expr_references_state_vars_v(expr, vars)
}

/// Check if an expression references any primed variables from the given set.
/// Delegated to generic visitor in expr_visitor.rs (Part of #1192 Wave 2).
pub(super) fn expr_references_primed_vars(
    ctx: &EvalCtx,
    expr: &Expr,
    vars: &FxHashSet<Arc<str>>,
) -> bool {
    crate::expr_visitor::expr_references_primed_vars_v(ctx, expr, vars)
}

/// Collect primed variable names referenced in an expression.
/// Returns the names of variables (without ') that appear as x' in the expression.
pub(super) fn get_primed_var_refs(expr: &Expr) -> FxHashSet<Arc<str>> {
    crate::expr_visitor::get_primed_var_refs_v(expr).into_iter().collect()
}

/// Context-aware version of get_primed_var_refs that follows operator references.
/// This is necessary for topological sorting when expressions contain operator calls
/// (like `IF ActionX THEN 5 ELSE y` where ActionX = `x < 1 /\ x' = x + 1`).
pub(super) fn get_primed_var_refs_with_ctx(ctx: &EvalCtx, expr: &Expr) -> FxHashSet<Arc<str>> {
    crate::expr_visitor::get_primed_var_refs_with_ctx_v(ctx, expr)
}

#[cfg(test)]
mod tests {
    use super::flatten_and_spanned;
    use smallvec::SmallVec;
    use tla_core::ast::Expr;
    use tla_core::name_intern::NameId;
    use tla_core::Spanned;

    #[test]
    fn test_flatten_and_spanned_preserves_order_and_borrows_original_nodes() {
        let a = Spanned::dummy(Expr::Ident("a".to_string(), NameId::INVALID));
        let b = Spanned::dummy(Expr::Ident("b".to_string(), NameId::INVALID));
        let c = Spanned::dummy(Expr::Ident("c".to_string(), NameId::INVALID));
        let expr = Spanned::dummy(Expr::And(
            Box::new(Spanned::dummy(Expr::And(Box::new(a), Box::new(b)))),
            Box::new(c),
        ));

        let mut parts = SmallVec::new();
        flatten_and_spanned(&expr, &mut parts);

        assert_eq!(parts.len(), 3);
        assert!(matches!(
            &parts[0].node,
            Expr::Ident(name, _) if name == "a"
        ));
        assert!(matches!(
            &parts[1].node,
            Expr::Ident(name, _) if name == "b"
        ));
        assert!(matches!(
            &parts[2].node,
            Expr::Ident(name, _) if name == "c"
        ));

        let Expr::And(left_and, right_leaf) = &expr.node else {
            panic!("invariant: test expression must be an And")
        };
        let Expr::And(left_leaf, middle_leaf) = &left_and.node else {
            panic!("invariant: left branch must be an And")
        };

        assert!(std::ptr::eq(parts[0], left_leaf.as_ref()));
        assert!(std::ptr::eq(parts[1], middle_leaf.as_ref()));
        assert!(std::ptr::eq(parts[2], right_leaf.as_ref()));
    }

    /// Verify that `clear_expr_analysis_caches` empties all three thread-local caches.
    /// This prevents stale entries from being returned when AST memory addresses are
    /// reused across model checking runs.
    #[test]
    fn test_clear_expr_analysis_caches_empties_all() {
        use super::*;

        // Populate each cache with a dummy entry.
        EXPR_ANALYSIS_CACHES.with(|caches| {
            let mut c = caches.borrow_mut();
            c.expr_is_action_level.insert(0xDEAD, false);
            c.might_need_prime_binding.insert(0xBEEF, true);
            c.is_operator_ref_guard_unsafe.insert(0xCAFE, false);
        });

        // Verify non-empty.
        EXPR_ANALYSIS_CACHES.with(|caches| {
            let c = caches.borrow();
            assert!(!c.expr_is_action_level.is_empty());
            assert!(!c.might_need_prime_binding.is_empty());
            assert!(!c.is_operator_ref_guard_unsafe.is_empty());
        });

        clear_expr_analysis_caches();

        // All three must be empty after clearing.
        EXPR_ANALYSIS_CACHES.with(|caches| {
            let c = caches.borrow();
            assert!(
                c.expr_is_action_level.is_empty(),
                "expr_is_action_level not cleared"
            );
            assert!(
                c.might_need_prime_binding.is_empty(),
                "might_need_prime_binding not cleared"
            );
            assert!(
                c.is_operator_ref_guard_unsafe.is_empty(),
                "is_operator_ref_guard_unsafe not cleared"
            );
        });
    }
}
