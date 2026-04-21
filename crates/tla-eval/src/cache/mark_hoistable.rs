// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bottom-up AST walk to identify bound-variable-invariant subexpressions.
//!
//! For each compound subexpression whose subtree does NOT reference any bound
//! name, we record its AST pointer as "hoistable" — the evaluator can cache
//! its result across quantifier loop iterations.
//!
//! Part of #3128: Extracted from quantifier_hoist.rs to stay under the
//! 500-line file limit.
//!
//! Gated by `HOIST_ENABLED` const in helpers/quantifiers.rs. Stage 1 allowlist
//! (see `is_stage1_hoistable`) restricts hoisting to pure structural expressions
//! to avoid the 5 regressions from complex evaluation forms.
use super::mark_hoistable_walkers::mark_hoistable_structural;
use rustc_hash::FxHashSet;
use std::cell::RefCell;
use std::rc::Rc;
use tla_core::ast::Expr;

thread_local! {
    /// Part of #3100: Cache `mark_hoistable` results by (body_ptr, bounds_ptr).
    ///
    /// The hoistable set depends on BOTH the quantifier body AND which bound
    /// variables are in scope. For multi-bound quantifiers like `\A x \in S, y \in T : body`,
    /// eval_forall recurses with bounds[1..], producing different bound name sets
    /// for the same body. Using body_ptr alone as cache key would return the
    /// outer set ({"x","y"}) for the inner call ({"y"}), which is a strict subset,
    /// causing fewer expressions to be hoisted and MORE redundant evaluation.
    ///
    /// bounds_ptr (from &[BoundVar]::as_ptr()) changes for each recursion depth
    /// since bounds[1..] has a different starting address than bounds[0..].
    #[allow(clippy::type_complexity)]
    pub(super) static MARK_HOISTABLE_CACHE: RefCell<rustc_hash::FxHashMap<(usize, usize), Rc<FxHashSet<usize>>>> = RefCell::new(rustc_hash::FxHashMap::default());
}

/// Walk the body AST bottom-up. For each compound subexpression whose subtree
/// does NOT reference any bound name, add its AST pointer to the hoistable set.
///
/// Returns the set of AST pointers (as `usize`) that are safe to cache within
/// the quantifier loop.
///
/// Part of #3100: Results are cached by `(body_ptr, bounds_ptr)`. The hoistable
/// set depends on both the body AST and the specific bound variables in scope.
/// For multi-bound quantifiers (`\A x \in S, y \in T : body`), eval_forall
/// recurses with `bounds[1..]`, which has a different slice pointer than the
/// original bounds. This ensures the cache correctly distinguishes different
/// recursion depths of the same quantifier.
pub(crate) fn mark_hoistable(
    body: &Expr,
    bound_names: &FxHashSet<&str>,
    cache_key: (usize, usize),
) -> Rc<FxHashSet<usize>> {
    let cached = MARK_HOISTABLE_CACHE.with(|cache| cache.borrow().get(&cache_key).map(Rc::clone));
    if let Some(result) = cached {
        return result;
    }
    let mut hoistable = FxHashSet::default();
    mark_hoistable_rec(body, bound_names, &mut hoistable);
    let rc = Rc::new(hoistable);
    MARK_HOISTABLE_CACHE.with(|cache| {
        cache.borrow_mut().insert(cache_key, Rc::clone(&rc));
    });
    rc
}

/// Returns `true` if the subtree references any name in `bound_names`.
/// As a side effect, adds non-referencing compound subtrees to `hoistable`.
pub(super) fn mark_hoistable_rec(
    expr: &Expr,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let refs = match expr {
        // Leaves: no children to recurse into
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            return bound_names.contains(name.as_str());
        }
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => return false,

        // Unary operators
        Expr::Not(a)
        | Expr::Neg(a)
        | Expr::Prime(a)
        | Expr::Unchanged(a)
        | Expr::Enabled(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Domain(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a) => mark_hoistable_rec(&a.node, bound_names, hoistable),

        // Binary operators
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
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b) => {
            mark_hoistable_rec(&a.node, bound_names, hoistable)
                | mark_hoistable_rec(&b.node, bound_names, hoistable)
        }

        // Structural: delegated to helpers
        _ => mark_hoistable_structural(expr, bound_names, hoistable),
    };
    if !refs && is_hoist_cacheable(expr) {
        hoistable.insert(expr as *const Expr as usize);
    }
    // Part of #3128: Non-analyzed compound expressions (FuncApply, Apply,
    // ModuleRef, Let, etc.) may have evaluation-time dependencies that
    // syntactic free-variable analysis cannot capture. If such an expression
    // returns refs=false (children don't reference bound names), propagate
    // refs=true upward so that parent expressions are NOT marked hoistable.
    // Part of #3364: set comprehensions/filter predicates are exempt from
    // poisoning when refs=false. Their bindings are explicit in the AST, so
    // mark_hoistable_multi_bound / mark_hoistable_single_bound can soundly
    // prove when the construct is invariant in the outer quantifier.
    //
    // Broader binding forms (FuncDef, Forall, Exists, Choose) were briefly
    // allowed here, but EWD998PCal regressed: the post-#3364 binary panicked in
    // the sequential property path while the pre-#3364 binary still passed with
    // TLC-parity state counts. Keep the Stage-2 lane limited to the bosco-
    // relevant set-construction forms until the remaining binding forms get a
    // separate soundness proof.
    if !refs && !is_hoist_safe(expr) {
        return true;
    }
    refs
}

/// Stage 1 hoist allowlist: expressions whose values are determined entirely by
/// their visible child ASTs with no internal binding/evaluation scopes.
///
/// Binding constructs (`Forall`, `Exists`, `Choose`, `FuncDef`, `SetBuilder`,
/// `SetFilter`) are intentionally excluded. The recursive `SafeAt`-style shape
/// covered by `test_hoist_recursive_let_function_capturing_outer_quantifier_not_cached`
/// showed that syntactic narrowing of bound-name sets was not sufficient to
/// make hoisting those forms sound: the debug hoist verifier observed a cached
/// `Forall` result diverging from a fresh evaluation.
///
/// Excluded forms (`Apply`, `FuncApply`, `ModuleRef`, `Let`, `Lambda`,
/// `SubstIn`, `InstanceExpr`, binding constructs, and temporal/action ops)
/// poison parent hoists because they may carry evaluation-time dependencies
/// not visible in the AST.
pub(crate) fn is_stage1_hoistable(expr: &Expr) -> bool {
    matches!(
        expr,
        // Unary pure operators
        Expr::Not(_)
        | Expr::Neg(_)
        | Expr::Domain(_)
        | Expr::Powerset(_)
        | Expr::BigUnion(_)
        // Binary pure operators
        | Expr::And(_, _)
        | Expr::Or(_, _)
        | Expr::Implies(_, _)
        | Expr::Equiv(_, _)
        | Expr::Eq(_, _)
        | Expr::Neq(_, _)
        | Expr::Lt(_, _)
        | Expr::Leq(_, _)
        | Expr::Gt(_, _)
        | Expr::Geq(_, _)
        | Expr::Add(_, _)
        | Expr::Sub(_, _)
        | Expr::Mul(_, _)
        | Expr::Div(_, _)
        | Expr::IntDiv(_, _)
        | Expr::Mod(_, _)
        | Expr::Pow(_, _)
        | Expr::In(_, _)
        | Expr::NotIn(_, _)
        | Expr::Subseteq(_, _)
        | Expr::Union(_, _)
        | Expr::Intersect(_, _)
        | Expr::SetMinus(_, _)
        | Expr::FuncSet(_, _)
        | Expr::Range(_, _)
        // Pure value constructors
        | Expr::If(_, _, _)
        | Expr::Tuple(_)
        | Expr::SetEnum(_)
        | Expr::Times(_)
        | Expr::Record(_)
        | Expr::RecordSet(_)
        | Expr::RecordAccess(_, _)
        | Expr::Case(_, _)
        | Expr::Except(_, _)
    )
}

/// Part of #3364: set-construction binding forms no longer poison structural
/// parents when their bodies are invariant in the outer quantifier. We do NOT
/// cache these nodes directly; they only make enclosing Stage-1 expressions
/// (such as bosco's `Union(SetBuilder, SetBuilder)`) eligible for caching.
fn is_nonpoisoning_binding_construct(expr: &Expr) -> bool {
    matches!(expr, Expr::SetBuilder(_, _) | Expr::SetFilter(_, _))
}

/// Returns true if the expression itself may be cached in the hoist map.
///
/// Stage 2 currently only removes poisoning from selected binding constructs;
/// it does not cache those constructs directly.
pub(crate) fn is_hoist_cacheable(expr: &Expr) -> bool {
    is_stage1_hoistable(expr)
}

/// Returns true if the expression should NOT poison an enclosing structural
/// parent when refs=false.
pub(crate) fn is_hoist_safe(expr: &Expr) -> bool {
    is_hoist_cacheable(expr) || is_nonpoisoning_binding_construct(expr)
}

#[cfg(test)]
#[path = "mark_hoistable_tests.rs"]
mod tests;
