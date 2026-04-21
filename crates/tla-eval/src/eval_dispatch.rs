// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive expression evaluation dispatch.
//!
//! Extracted from `core.rs` as part of #2764 / #1643. Contains:
//! - `eval`: Stack-safe recursive evaluation entry
//! - `eval_inner`: Inner eval implementation (debug profiling + dispatch)
//! - `eval_expr`: The main expression dispatch match

use super::profile_eval;
use super::EVAL_CALL_COUNT;
use super::{
    build_lazy_subst_bindings, eval_and, eval_apply, eval_arith, eval_big_union, eval_case,
    eval_choose, eval_comparison, eval_div, eval_domain, eval_enabled_op, eval_eq, eval_equiv,
    eval_except, eval_exists, eval_forall, eval_func_apply, eval_func_def, eval_func_set,
    eval_ident, eval_if, eval_implies, eval_in, eval_int_literal, eval_intersect, eval_lambda,
    eval_let, eval_mod, eval_module_ref_target, eval_neg, eval_neq, eval_not, eval_not_in, eval_or,
    eval_pow, eval_powerset, eval_prime, eval_range, eval_record, eval_record_access,
    eval_record_set, eval_set_builder, eval_set_enum, eval_set_filter, eval_set_minus,
    eval_state_var, eval_string_literal, eval_subseteq, eval_times, eval_tuple, eval_unchanged,
    eval_union, stack_safe, EvalCtx, EvalError, EvalResult,
};
use crate::value::{val_false, val_true, Value};
use num_integer::Integer;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Span, Spanned};

/// Part of #4114: Static empty eager_subst_bindings marker. SubstIn evaluations
/// set this as a marker to enable the eval_ident fast path. Previously allocated
/// `Arc::new(vec![])` on every SubstIn eval — now reuses a single Arc.
pub(crate) static EMPTY_EAGER_SUBST: std::sync::LazyLock<
    Arc<Vec<(tla_core::name_intern::NameId, Value, crate::cache::dep_tracking::OpEvalDeps)>>,
> = std::sync::LazyLock::new(|| Arc::new(vec![]));

/// Evaluate an expression in the given context (recursive evaluation).
///
/// Part of #250: This is now the fast path for recursive evaluation.
/// Use eval_entry() for top-level entry points that need cache management.
pub fn eval(ctx: &EvalCtx, expr: &Spanned<Expr>) -> EvalResult<Value> {
    // Part of #188, #250, #1275, #3063:
    // Shared stacker throttle (ctx.should_check_stack) checks every 64 evals in
    // release, every eval in debug. Counter is shared with compiled guard path.
    if ctx.should_check_stack() {
        eval_slow_path(ctx, expr)
    } else {
        eval_inner(ctx, expr)
    }
}

/// Slow path for eval(): TLS sync, profiling, and stack safety.
///
/// Part of #9062: Extracted from eval() to reduce the code size of the hot path.
/// This runs every 64th eval (release) or every eval (debug). Moving profiling
/// and TLS sync here means the fast path (63/64 calls) has zero profiling overhead
/// and minimal code size. The #[cold] hint tells LLVM to optimize the fast path
/// at this function's expense.
#[cold]
#[inline(never)]
fn eval_slow_path(ctx: &EvalCtx, expr: &Spanned<Expr>) -> EvalResult<Value> {
    // Sync hoist_active, hoist_state_generation, and in_enabled_scope shadows
    // from TLS every 64 evals. Avoids per-eval TLS lookups in eval_expr
    // (413M+ calls/run). Part of #3962: hoist_state_generation eliminates
    // 2 more TLS reads per eval_expr (lookup + store) when hoist is active.
    ctx.runtime_state
        .hoist_active
        .set(crate::cache::is_hoist_active());
    ctx.runtime_state
        .hoist_state_generation
        .set(crate::cache::quantifier_hoist::hoist_state_generation_tls());
    ctx.runtime_state
        .in_enabled_scope
        .set(crate::cache::lifecycle::in_enabled_scope());

    // Part of #9062: Profile counting moved here from eval_inner(). Previously
    // checked profile_eval() on every eval call (a OnceLock read + branch).
    // Now only checked on the 1/64 slow path, eliminating 63/64 branches.
    // Add 64 per slow-path invocation to maintain approximate total count
    // (this function is called every 64th eval in release builds).
    if profile_eval() {
        EVAL_CALL_COUNT.fetch_add(64, Ordering::Relaxed);
    }

    stack_safe(|| eval_inner(ctx, expr))
}

/// Inner eval implementation (wrapped by stacker in eval())
///
/// Part of #250: Simplified to remove IN_EVAL thread-local entirely.
/// Cache management is now handled by eval_entry() at external call sites.
/// Stack overflow protection is handled by stacker::maybe_grow in the outer eval().
/// Part of #2955: inline(always) to eliminate function-call overhead on hot path.
/// Part of #9062: profile_eval() check moved to eval_slow_path() — no longer
/// checked on every eval call, only on the 1/64 slow path.
#[inline(always)]
pub(super) fn eval_inner(ctx: &EvalCtx, expr: &Spanned<Expr>) -> EvalResult<Value> {
    // Part of #250: Direct evaluation - cache management moved to eval_entry()
    eval_expr(ctx, &expr.node, Some(expr.span))
}

/// Evaluate an expression with optional span for error reporting.
///
/// Part of #2955: inline(always) to eliminate dispatch-chain overhead.
/// Part of #9062: Restructured for I-cache efficiency:
/// - hoist_active fast check is a single Cell read; the expensive
///   is_dep_tracking_active() only runs when hoist is actually active.
/// - SubstIn arm extracted to a cold helper to reduce code size.
/// - Hoist store at end only fires when hoist is active (no dead code
///   in the common non-hoist path).
#[inline(always)]
pub(super) fn eval_expr(ctx: &EvalCtx, expr: &Expr, span: Option<Span>) -> EvalResult<Value> {
    // Part of #3147, #9062: Fast-check hoist_active shadow (single Cell read).
    // Only proceed to the expensive is_dep_tracking_active() check when hoist
    // is active. During BFS without quantifier hoisting, this is a single
    // Cell::get() returning false — no second Cell read needed.
    if ctx.runtime_state.hoist_active.get() {
        return eval_expr_with_hoist(ctx, expr, span);
    }

    // Hot path: no hoist active. Pure dispatch — no hoist cache lookup or store.
    eval_expr_dispatch(ctx, expr, span)
}

/// Hoist-enabled evaluation path. Only called when hoist_active is true.
///
/// Part of #9062: Extracted from eval_expr to keep the non-hoist path minimal.
/// This function is NOT #[cold] because quantifier-heavy specs may spend most
/// time here. But separating it means the non-hoist eval_expr is smaller and
/// more I-cache friendly.
#[inline(never)]
fn eval_expr_with_hoist(ctx: &EvalCtx, expr: &Expr, span: Option<Span>) -> EvalResult<Value> {
    let hoist_allowed = !crate::cache::is_dep_tracking_active(ctx);

    // Part of #3128: Check quantifier hoist cache before evaluating.
    if hoist_allowed {
        if let Some(cached) = crate::cache::quantifier_hoist_lookup_ctx(ctx, expr) {
            // Part of #3128: HOIST_VERIFY double-evaluation diagnostic.
            #[cfg(debug_assertions)]
            if crate::cache::HOIST_VERIFY {
                let _guard = crate::cache::suppress_hoist_lookup();
                let fresh = eval_expr_dispatch(ctx, expr, span);
                match fresh {
                    Ok(ref v) if v == &cached => {}
                    Ok(ref v) => {
                        unreachable!(
                            "HOIST VERIFY FAIL: expr={:p} kind={} cached={:?} fresh={:?}",
                            expr,
                            expr_kind_name(expr),
                            cached,
                            v
                        );
                    }
                    Err(ref e) => {
                        unreachable!(
                            "HOIST VERIFY FAIL: expr={:p} kind={} cached={:?} fresh=Err({:?})",
                            expr,
                            expr_kind_name(expr),
                            cached,
                            e
                        );
                    }
                }
            }
            return Ok(cached);
        }
    }

    let result = eval_expr_dispatch(ctx, expr, span);

    // Part of #3128: Store result in quantifier hoist cache if applicable.
    if hoist_allowed {
        if let Ok(ref val) = result {
            crate::cache::quantifier_hoist_store_ctx(ctx, expr, val);
        }
    }

    result
}

/// Core expression dispatch match.
///
/// Part of #9062: Extracted from eval_expr so the non-hoist hot path and the
/// hoist path share the same match without duplicating code. The match body
/// is the single largest code region in the evaluator (~50 arms). Keeping it
/// in one place maximizes I-cache reuse.
///
/// Part of #4153: Changed from #[inline(always)] to #[inline] to let LLVM
/// decide inlining based on call-site context. With #[inline(always)], the
/// entire ~160-line match was force-inlined into all 3 call sites (eval_expr,
/// eval_expr_with_hoist x2), tripling I-cache footprint. With #[inline], LLVM
/// can choose to inline into the hot eval_expr path while keeping a single
/// out-of-line copy for the hoist paths. The function's size (50 arms) means
/// LLVM typically won't inline it, but marking it #[inline] ensures the
/// definition is available in every codegen unit for cross-crate optimization.
/// Error-returning arms and rare paths are extracted to #[cold] helpers to
/// further reduce the hot-path code size within the match.
#[inline]
fn eval_expr_dispatch(ctx: &EvalCtx, expr: &Expr, span: Option<Span>) -> EvalResult<Value> {
    match expr {
        // === Literals ===
        Expr::Bool(b) => Ok(if *b { val_true() } else { val_false() }),
        Expr::Int(n) => eval_int_literal(n, span),
        Expr::String(s) => eval_string_literal(s.as_str(), span),

        // === Variables and zero-arg operators ===
        Expr::Ident(name, name_id) => eval_ident(ctx, name, *name_id, span),

        // === Pre-resolved state variable (O(1) lookup) ===
        Expr::StateVar(name, idx, name_id) => eval_state_var(ctx, name, *idx, *name_id, span),

        // === Operator application ===
        Expr::Apply(op_expr, args) => eval_apply(ctx, op_expr, args, span),

        // === Logic (high frequency during BFS) ===
        Expr::And(a, b) => eval_and(ctx, a, b),
        Expr::Or(a, b) => eval_or(ctx, a, b),
        Expr::Not(a) => eval_not(ctx, a),
        Expr::Implies(a, b) => eval_implies(ctx, a, b),
        Expr::Equiv(a, b) => eval_equiv(ctx, a, b),

        // === Comparison (high frequency during BFS) ===
        Expr::Eq(a, b) => eval_eq(ctx, a, b, span),
        Expr::Neq(a, b) => eval_neq(ctx, a, b, span),
        Expr::In(a, b) => eval_in(ctx, a, b, span),

        // === Control (high frequency during BFS) ===
        Expr::If(cond, then_branch, else_branch) => eval_if(ctx, cond, then_branch, else_branch),
        Expr::Let(defs, body) => eval_let(ctx, defs, body, span),

        // === Quantifiers ===
        // Clone ctx once at call site, use O(1) mutable stack binding inside
        Expr::Forall(bounds, body) => {
            let mut local_ctx = ctx.clone();
            eval_forall(&mut local_ctx, bounds, body, span)
        }
        Expr::Exists(bounds, body) => {
            let mut local_ctx = ctx.clone();
            eval_exists(&mut local_ctx, bounds, body, span)
        }
        Expr::Choose(bound, body) => eval_choose(ctx, bound, body, span),

        // === Primed variables (next-state lookup) ===
        Expr::Prime(inner) => eval_prime(ctx, inner, span),

        // === Action-level helper ===
        Expr::Unchanged(inner) => eval_unchanged(ctx, inner, span),

        // === Sets ===
        Expr::SetEnum(elems) => eval_set_enum(ctx, elems),
        Expr::SetBuilder(expr, bounds) => eval_set_builder(ctx, expr, bounds, span),
        Expr::SetFilter(bound, pred) => eval_set_filter(ctx, bound, pred, span),
        Expr::NotIn(a, b) => eval_not_in(ctx, a, b, span),
        Expr::Subseteq(a, b) => eval_subseteq(ctx, a, b, span),
        Expr::Union(a, b) => eval_union(ctx, a, b),
        Expr::Intersect(a, b) => eval_intersect(ctx, a, b, span),
        Expr::SetMinus(a, b) => eval_set_minus(ctx, a, b, span),
        Expr::Powerset(a) => eval_powerset(ctx, a),
        Expr::BigUnion(a) => eval_big_union(ctx, a, span),

        // === Functions ===
        Expr::FuncDef(bounds, body) => eval_func_def(ctx, bounds, body, span),
        Expr::FuncApply(func_expr, arg_expr) => eval_func_apply(ctx, func_expr, arg_expr, span),
        Expr::Domain(func_expr) => eval_domain(ctx, func_expr, span),
        Expr::Except(func_expr, specs) => eval_except(ctx, func_expr, specs, span),
        Expr::FuncSet(domain, range) => eval_func_set(ctx, domain, range),

        // === Records ===
        Expr::Record(fields) => eval_record(ctx, fields),
        Expr::RecordAccess(rec_expr, field) => eval_record_access(ctx, rec_expr, field, span),
        Expr::RecordSet(fields) => eval_record_set(ctx, fields),

        // === Tuples and Sequences ===
        Expr::Tuple(elems) => eval_tuple(ctx, elems),
        Expr::Times(factors) => eval_times(ctx, factors),

        // === Arithmetic ===
        Expr::Add(a, b) => eval_arith(ctx, a, b, i64::checked_add, |x, y| x + y, "+"),
        Expr::Sub(a, b) => eval_arith(ctx, a, b, i64::checked_sub, |x, y| x - y, "-"),
        Expr::Mul(a, b) => eval_arith(ctx, a, b, i64::checked_mul, |x, y| x * y, "*"),
        Expr::Div(a, b) => eval_div(ctx, a, b, i64::checked_div, |x, y| x / y, "/", span),
        Expr::IntDiv(a, b) => eval_div(
            ctx,
            a,
            b,
            |x, y| {
                if x == i64::MIN && y == -1 {
                    return None;
                }
                let q = x / y;
                if (x ^ y) < 0 && x % y != 0 {
                    Some(q - 1)
                } else {
                    Some(q)
                }
            },
            |x, y| x.div_floor(&y),
            "\\div",
            span,
        ),
        Expr::Mod(a, b) => eval_mod(ctx, a, b, span),
        Expr::Pow(a, b) => eval_pow(ctx, a, b, span),
        Expr::Neg(a) => eval_neg(ctx, a),
        Expr::Range(a, b) => eval_range(ctx, a, b),

        // === Remaining comparison ===
        Expr::Lt(a, b) => eval_comparison(ctx, a, b, std::cmp::Ordering::is_lt, "<"),
        Expr::Leq(a, b) => eval_comparison(ctx, a, b, std::cmp::Ordering::is_le, "\\leq"),
        Expr::Gt(a, b) => eval_comparison(ctx, a, b, std::cmp::Ordering::is_gt, ">"),
        Expr::Geq(a, b) => eval_comparison(ctx, a, b, std::cmp::Ordering::is_ge, "\\geq"),

        Expr::Case(arms, other) => eval_case(ctx, arms, other.as_deref(), span),

        // === ENABLED operator ===
        Expr::Enabled(action) => eval_enabled_op(ctx, action),

        // === SubstIn: deferred INSTANCE substitution ===
        // Part of #9062: Extracted to cold helper to reduce I-cache pressure.
        // SubstIn has ~20 lines of complex code (Arc ops, cache lookups,
        // context cloning) that bloats the match body. Most specs don't use
        // INSTANCE, so this arm is rarely taken during BFS.
        Expr::SubstIn(subs, body) => eval_subst_in(ctx, subs, body),

        // === Operator Reference (error: not directly evaluable) ===
        // Part of #4153: Extracted to cold helper — OpRef should never appear
        // during normal evaluation (only via higher-order ops).
        Expr::OpRef(op) => eval_opref_error(op, span),

        // === Lambda ===
        Expr::Lambda(params, body) => eval_lambda(ctx, params, body),
        Expr::Label(label) => eval(ctx, &label.body),

        // === Module Reference ===
        Expr::ModuleRef(target, op_name, args) => {
            eval_module_ref_target(ctx, target, op_name, args, span)
        }

        // === Instance Expression (error: should be registered at load time) ===
        // Part of #4153: Extracted to cold helper — should never reach eval.
        Expr::InstanceExpr(module, _subs) => eval_instance_expr_error(module, span),

        // === Temporal (not evaluated - model checking only) ===
        // Part of #4153: Extracted to cold helper — temporal ops are handled
        // by the model checker, never the expression evaluator.
        Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _)
        | Expr::StrongFair(_, _) => eval_temporal_error(span),
    }
}

/// Cold path: evaluate SubstIn (deferred INSTANCE substitution).
///
/// Part of #9062: Extracted from eval_expr_dispatch to reduce the I-cache
/// footprint of the main match. SubstIn involves Arc allocation, cache lookups,
/// context cloning, and scope_id computation — ~20 lines of complex code that
/// inflate the match body. Most specs don't use INSTANCE during BFS evaluation,
/// making this arm cold in the common case.
///
/// Part of #3056 Phase 2: Build lazy binding chain from substitutions,
/// matching TLC's evalImplSubstInKind pattern.
///
/// Takes `&Vec<Substitution>` (not `&[Substitution]`) to preserve pointer
/// identity with the Vec stored in the Expr::SubstIn variant. The cache key
/// uses the Vec's own address, not the data pointer.
#[cold]
#[inline(never)]
#[allow(clippy::ptr_arg)] // Intentional: need &Vec / &Box pointer identity for cache key
fn eval_subst_in(
    ctx: &EvalCtx,
    subs: &Vec<tla_core::ast::Substitution>,
    body: &Box<Spanned<Expr>>,
) -> EvalResult<Value> {
    // Fix #3123: Reuse the Arc across repeated evaluations of the same SubstIn
    // node under the same enclosing scope.
    let subs_ptr = subs as *const Vec<_> as usize;
    let body_ptr = std::ptr::addr_of!(**body) as usize;
    let scope_key = crate::cache::raw_subst_scope_key(ctx, subs_ptr, body_ptr);
    // Part of #3962: Access raw_subst_scope_cache via consolidated SMALL_CACHES.
    let (subs_arc, cached_scope_id) = crate::cache::SMALL_CACHES.with(|sc| {
        let c = sc.borrow();
        if let Some(entry) = c.raw_subst_scope_cache.get(&scope_key) {
            return entry.clone();
        }
        drop(c);
        let arc = Arc::new(subs.clone());
        let scope_id = crate::cache::scope_ids::compute_instance_subs_id(&arc);
        sc.borrow_mut()
            .raw_subst_scope_cache
            .insert(scope_key, (arc.clone(), scope_id));
        (arc, scope_id)
    });
    let new_bindings = build_lazy_subst_bindings(&ctx.bindings, &subs_arc);
    let mut sub_ctx = ctx.clone();
    sub_ctx.bindings = new_bindings;
    let s = sub_ctx.stable_mut();
    s.instance_substitutions = Some(subs_arc);
    s.scope_ids.instance_substitutions = cached_scope_id;
    // Part of #3056 Phase B: Empty marker enables eval_ident fast path
    // (can_take_fast_path requires eager_subst_bindings.is_some() when
    // instance_subs active). Actual substitution bindings are in the
    // BindingChain as lazy entries.
    s.eager_subst_bindings = Some(Arc::clone(&EMPTY_EAGER_SUBST));
    eval(&sub_ctx, body)
}

/// Cold error path: OpRef cannot be evaluated directly.
///
/// Part of #4153: Extracted from eval_expr_dispatch to reduce the I-cache
/// footprint of the main match. OpRef should never appear during normal
/// evaluation — it's only valid as an argument to higher-order operators.
#[cold]
#[inline(never)]
fn eval_opref_error(op: &str, span: Option<Span>) -> EvalResult<Value> {
    Err(EvalError::Internal {
        message: format!(
            "Operator reference '{op}' cannot be evaluated directly; \
             it must be used with a higher-order operator like FoldFunctionOnSet"
        ),
        span,
    })
}

/// Cold error path: InstanceExpr should have been registered at load time.
///
/// Part of #4153: Extracted from eval_expr_dispatch. InstanceExpr nodes are
/// resolved during module loading and should never reach the evaluator.
#[cold]
#[inline(never)]
fn eval_instance_expr_error(module: &str, span: Option<Span>) -> EvalResult<Value> {
    Err(EvalError::Internal {
        message: format!(
            "INSTANCE {module} expression should be registered at load time, not evaluated"
        ),
        span,
    })
}

/// Cold error path: temporal operators cannot be directly evaluated.
///
/// Part of #4153: Extracted from eval_expr_dispatch. Temporal operators
/// (Always, Eventually, LeadsTo, WeakFair, StrongFair) are handled by the
/// model checker's liveness/fairness infrastructure, not the expression
/// evaluator.
#[cold]
#[inline(never)]
fn eval_temporal_error(span: Option<Span>) -> EvalResult<Value> {
    Err(EvalError::Internal {
        message: "Temporal operators cannot be directly evaluated".into(),
        span,
    })
}

/// Return the AST discriminant name for diagnostic messages.
/// Used by HOIST_VERIFY to identify which expression type caused a mismatch.
#[cfg(debug_assertions)]
fn expr_kind_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Bool(_) => "Bool",
        Expr::Int(_) => "Int",
        Expr::String(_) => "String",
        Expr::Ident(..) => "Ident",
        Expr::StateVar(..) => "StateVar",
        Expr::OpRef(_) => "OpRef",
        Expr::Apply(..) => "Apply",
        Expr::Lambda(..) => "Lambda",
        Expr::Label(_) => "Label",
        Expr::ModuleRef(..) => "ModuleRef",
        Expr::SubstIn(..) => "SubstIn",
        Expr::InstanceExpr(..) => "InstanceExpr",
        Expr::Let(..) => "Let",
        Expr::If(..) => "If",
        Expr::Case(..) => "Case",
        Expr::Forall(..) => "Forall",
        Expr::Exists(..) => "Exists",
        Expr::Choose(..) => "Choose",
        Expr::SetEnum(_) => "SetEnum",
        Expr::SetBuilder(..) => "SetBuilder",
        Expr::SetFilter(..) => "SetFilter",
        Expr::FuncDef(..) => "FuncDef",
        Expr::FuncApply(..) => "FuncApply",
        Expr::FuncSet(..) => "FuncSet",
        Expr::Except(..) => "Except",
        Expr::Tuple(_) => "Tuple",
        Expr::Record(_) => "Record",
        Expr::RecordSet(_) => "RecordSet",
        Expr::RecordAccess(..) => "RecordAccess",
        Expr::Times(_) => "Times",
        Expr::Not(_) => "Not",
        Expr::And(..) => "And",
        Expr::Or(..) => "Or",
        Expr::Implies(..) => "Implies",
        Expr::Equiv(..) => "Equiv",
        Expr::Eq(..) => "Eq",
        Expr::Neq(..) => "Neq",
        Expr::Lt(..) => "Lt",
        Expr::Leq(..) => "Leq",
        Expr::Gt(..) => "Gt",
        Expr::Geq(..) => "Geq",
        Expr::In(..) => "In",
        Expr::NotIn(..) => "NotIn",
        Expr::Subseteq(..) => "Subseteq",
        Expr::Union(..) => "Union",
        Expr::Intersect(..) => "Intersect",
        Expr::SetMinus(..) => "SetMinus",
        Expr::Domain(_) => "Domain",
        Expr::Powerset(_) => "Powerset",
        Expr::BigUnion(_) => "BigUnion",
        Expr::Range(..) => "Range",
        Expr::Add(..) => "Add",
        Expr::Sub(..) => "Sub",
        Expr::Mul(..) => "Mul",
        Expr::Div(..) => "Div",
        Expr::IntDiv(..) => "IntDiv",
        Expr::Mod(..) => "Mod",
        Expr::Pow(..) => "Pow",
        Expr::Neg(_) => "Neg",
        Expr::Prime(_) => "Prime",
        Expr::Unchanged(_) => "Unchanged",
        Expr::Enabled(_) => "Enabled",
        Expr::Always(_) => "Always",
        Expr::Eventually(_) => "Eventually",
        Expr::LeadsTo(..) => "LeadsTo",
        Expr::WeakFair(..) => "WeakFair",
        Expr::StrongFair(..) => "StrongFair",
    }
}
