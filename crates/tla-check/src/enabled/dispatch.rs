// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint propagation dispatch for ENABLED evaluation.
//!
//! Walks the action expression, propagating primed variable bindings through
//! a functional `WitnessState`. Short-circuits on first satisfying assignment
//! (disjunction, existential) or on first inconsistency (conjunction, equality).
//!
//! Conjunctions are flattened and processed as a list so that domain enumeration
//! (`x' \in S`) correctly backtracks through remaining conjuncts.
//!
//! TLC reference: `Tool.java:2973-3600`
//!
//! Part of #3004: ENABLED constraint propagation decision procedure.

use super::module_ref::resolve_module_ref_body;
use super::witness_state::WitnessState;
use crate::enumerate::is_disabled_action_error;
use crate::eval::{eval, EvalCtx, SparseStateEnvRef};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Spanned, VarRegistry};
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use super::conjunction::{flatten_conjunction, process_conjuncts};
use super::quantifiers::{handle_exists, handle_forall};

/// Result of constraint propagation: `Some(witness)` = enabled, `None` = not enabled.
pub(super) type CpResult = EvalResult<Option<WitnessState>>;

/// Top-level dispatch: evaluate an expression in ENABLED constraint propagation mode.
///
/// Returns `Some(witness)` if a satisfying assignment exists, `None` otherwise.
pub(super) fn dispatch_enabled(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    match &expr.node {
        // --- Conjunction: flatten and process with backtracking ---
        // TLC: Tool.java:3207-3216
        Expr::And(_, _) => {
            let mut conjuncts = Vec::new();
            flatten_conjunction(expr, &mut conjuncts);
            process_conjuncts(ctx, &conjuncts, 0, registry, witness)
        }

        // --- Disjunction: try each branch, return first success ---
        // TLC: Tool.java:3217-3228
        Expr::Or(a, b) => {
            let result = dispatch_enabled(ctx, a, registry, witness.clone())?;
            if result.is_some() {
                return Ok(result);
            }
            dispatch_enabled(ctx, b, registry, witness)
        }

        // --- Equality: x' = expr or boolean constraint ---
        // TLC: Tool.java:3329-3354
        Expr::Eq(lhs, rhs) => handle_equality_leaf(ctx, lhs, rhs, registry, witness),

        // --- Membership: x' \in S (leaf — no continuation) ---
        // TLC: Tool.java:3441-3479
        Expr::In(elem, set) => handle_membership_leaf(ctx, elem, set, registry, witness),

        // --- Existential: \E x \in S : P ---
        // TLC: Tool.java:3146-3159
        Expr::Exists(bounds, body) => handle_exists(ctx, bounds, body, registry, witness),

        // --- Universal: \A x \in S : P ---
        Expr::Forall(bounds, body) => handle_forall(ctx, bounds, body, registry, witness),

        // --- IF cond THEN a ELSE b ---
        // #3035: Must evaluate condition with witness bindings so primed variables resolve.
        Expr::If(cond, then_br, else_br) => {
            let cv = eval_in_witness_ctx(ctx, cond, &witness, registry)?;
            let cb = cv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &cv, Some(cond.span)))?;
            if cb {
                dispatch_enabled(ctx, then_br, registry, witness)
            } else {
                dispatch_enabled(ctx, else_br, registry, witness)
            }
        }

        // --- LET defs IN body ---
        Expr::Let(defs, body) => handle_let(ctx, defs, body, registry, witness),

        // --- UNCHANGED <<x, y, ...>> or UNCHANGED x ---
        // TLC: Tool.java:3508-3526 — bind x' = x
        Expr::Unchanged(vars_expr) => handle_unchanged(ctx, vars_expr, registry, witness),

        // --- Negation ---
        // #3035: Must evaluate inner with witness bindings so primed variables resolve.
        Expr::Not(inner) => {
            let v = eval_in_witness_ctx(ctx, inner, &witness, registry)?;
            let b = v
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &v, Some(inner.span)))?;
            if !b {
                Ok(Some(witness))
            } else {
                Ok(None)
            }
        }

        // --- Implication: A => B ≡ ~A \/ B ---
        // #3035: Must evaluate antecedent with witness bindings so primed variables resolve.
        Expr::Implies(a, b) => {
            let av = eval_in_witness_ctx(ctx, a, &witness, registry)?;
            let ab = av
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
            if !ab {
                Ok(Some(witness)) // Antecedent false → implication holds
            } else {
                dispatch_enabled(ctx, b, registry, witness)
            }
        }

        // --- Boolean literals ---
        Expr::Bool(true) => Ok(Some(witness)),
        Expr::Bool(false) => Ok(None),

        // --- ENABLED (nested): evaluate via normal eval ---
        Expr::Enabled(_) => eval_as_bool(ctx, expr, witness, registry),

        // --- CASE ---
        // #3035: Must evaluate guard with witness bindings so primed variables resolve.
        Expr::Case(arms, other) => {
            for arm in arms {
                let cv = eval_in_witness_ctx(ctx, &arm.guard, &witness, registry)?;
                if let Some(true) = cv.as_bool() {
                    return dispatch_enabled(ctx, &arm.body, registry, witness);
                }
            }
            if let Some(default) = other {
                dispatch_enabled(ctx, default, registry, witness)
            } else {
                Ok(None)
            }
        }

        // --- Ident: resolve zero-arg operator and recurse into body ---
        // Critical for ENABLED Next where Next is a named action operator.
        // Without this, eval_as_bool would hit PrimedVariableNotBound since
        // the operator body contains x' but no next-state is bound.
        // TLC: Tool.java resolves operators inline before constraint propagation.
        Expr::Ident(name, _) => {
            let resolved = ctx.resolve_op_name(name.as_str());
            if let Some(def) = ctx.get_op(resolved).cloned() {
                if def.params.is_empty() {
                    return dispatch_enabled(ctx, &def.body, registry, witness);
                }
            }
            // Not an operator (could be a local binding or constant)
            eval_as_bool(ctx, expr, witness, registry)
        }

        // --- Apply: resolve operator, bind args, recurse into body ---
        // Handles ENABLED Action(arg1, arg2) where Action is a parameterized operator.
        Expr::Apply(op_expr, args) => {
            if let Expr::Ident(op_name, _) = &op_expr.node {
                let resolved = ctx.resolve_op_name(op_name.as_str());
                if let Some(def) = ctx.get_op(resolved).cloned() {
                    // Bind parameters to evaluated argument values
                    let mut inner_ctx = ctx.clone();
                    let _guard = inner_ctx.scope_guard();
                    for (param, arg) in def.params.iter().zip(args.iter()) {
                        let arg_val = eval(ctx, arg)?;
                        inner_ctx.bind_mut(Arc::from(param.name.node.as_str()), arg_val);
                    }
                    return dispatch_enabled(&inner_ctx, &def.body, registry, witness);
                }
            }
            // Unknown operator — fall back to eval
            eval_as_bool(ctx, expr, witness, registry)
        }

        // --- ModuleRef: resolve instance scope, bind args, recurse into body ---
        // Part of #3161: ENABLED M!Op must behave like operator dispatch, not
        // plain boolean eval, or fairness checks will treat enabled instance
        // actions as disabled and admit unfair stuttering loops.
        Expr::ModuleRef(target, op_name, args) => {
            if let Some((inner_ctx, body)) = resolve_module_ref_body(ctx, target, op_name, args)? {
                return dispatch_enabled(&inner_ctx, &body, registry, witness);
            }
            eval_as_bool(ctx, expr, witness, registry)
        }

        // --- Default: evaluate as boolean constraint ---
        // Comparisons, arithmetic, set operations, etc.
        // TLC: Tool.java:3300 default case
        _ => eval_as_bool(ctx, expr, witness, registry),
    }
}

// ============================================================================
// Leaf handlers (no continuation needed)
// ============================================================================

/// Get the VarIndex for a primed variable expression, or None.
///
/// Recognizes `Expr::Prime(Expr::Ident(...))` and `Expr::Prime(Expr::StateVar(...))`.
pub(super) fn get_primed_var_idx(expr: &Expr, registry: &VarRegistry) -> Option<usize> {
    match expr {
        Expr::Prime(inner) => match &inner.node {
            Expr::Ident(name, _) => registry
                .get(name.as_str())
                .map(tla_core::VarIndex::as_usize),
            Expr::StateVar(_, idx, _) => Some(*idx as usize),
            _ => None,
        },
        _ => None,
    }
}

/// Handle `lhs = rhs` where one side may be a primed variable.
///
/// TLC: Tool.java:3329-3354
pub(super) fn handle_equality_leaf(
    ctx: &EvalCtx,
    lhs: &Spanned<Expr>,
    rhs: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    // Check if LHS is x' (primed variable)
    if let Some(var_idx) = get_primed_var_idx(&lhs.node, registry) {
        let rval = eval_in_witness_ctx(ctx, rhs, &witness, registry)?;
        return bind_or_check(var_idx, rval, witness);
    }

    // Check if RHS is x' (primed variable) — symmetric case
    if let Some(var_idx) = get_primed_var_idx(&rhs.node, registry) {
        let lval = eval_in_witness_ctx(ctx, lhs, &witness, registry)?;
        return bind_or_check(var_idx, lval, witness);
    }

    // Neither side is a primed variable: evaluate as boolean constraint
    eval_as_bool(
        ctx,
        &Spanned::new(
            Expr::Eq(Box::new(lhs.clone()), Box::new(rhs.clone())),
            lhs.span,
        ),
        witness,
        registry,
    )
}

/// Bind a primed variable or check consistency with existing binding.
fn bind_or_check(var_idx: usize, value: Value, witness: WitnessState) -> CpResult {
    match witness.lookup(var_idx) {
        None => Ok(Some(witness.bind(var_idx, value))),
        Some(existing) => {
            if *existing == value {
                Ok(Some(witness))
            } else {
                Ok(None) // Inconsistent binding
            }
        }
    }
}

/// Handle `elem \in set` as a leaf (not inside conjunction processing).
///
/// When used as a standalone expression (not in a conjunction), there are no
/// remaining conjuncts to backtrack through, so binding the first element works.
fn handle_membership_leaf(
    ctx: &EvalCtx,
    elem: &Spanned<Expr>,
    set: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    if let Some(var_idx) = get_primed_var_idx(&elem.node, registry) {
        match witness.lookup(var_idx) {
            Some(existing) => {
                let set_val = eval(ctx, set)?;
                let is_member = set_val.set_contains(existing).unwrap_or(false);
                if is_member {
                    Ok(Some(witness))
                } else {
                    Ok(None)
                }
            }
            None => {
                // Standalone membership: any element satisfies it
                let set_val = eval(ctx, set)?;
                if let Some(mut iter) = set_val.iter_set() {
                    if let Some(member) = iter.next() {
                        return Ok(Some(witness.bind(var_idx, member)));
                    }
                }
                Ok(None) // Empty set
            }
        }
    } else {
        // Not a primed variable: evaluate as boolean constraint
        eval_as_bool(
            ctx,
            &Spanned::new(
                Expr::In(Box::new(elem.clone()), Box::new(set.clone())),
                elem.span,
            ),
            witness,
            registry,
        )
    }
}

/// Handle `LET defs IN body`.
///
/// Parameterized LET defs (e.g., `senders(v) == ...`) are added to `local_ops`
/// so they can be resolved during body evaluation. Zero-arg defs are eagerly
/// evaluated and bound. This matches TLC's Tool.java which adds all LET defs
/// to the Context before dispatching the body.
///
/// Fix for #3030: Previously fell back to `eval_as_bool` on parameterized defs,
/// which exited constraint propagation entirely. The body (containing primed
/// variable assignments) was then evaluated by the normal evaluator, which
/// cannot find variables bound via `bind_mut` in the ENABLED context.
fn handle_let(
    ctx: &EvalCtx,
    defs: &[tla_core::ast::OperatorDef],
    body: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    let mut inner_ctx = ctx.clone();
    let _guard = inner_ctx.scope_guard();

    // First pass: add parameterized defs to local_ops so they're available
    // during both zero-arg def evaluation and body dispatch.
    let has_parameterized = defs.iter().any(|d| !d.params.is_empty());
    if has_parameterized {
        let mut local_ops: tla_core::OpEnv = match inner_ctx.local_ops() {
            Some(ops) => (**ops).clone(),
            None => tla_core::OpEnv::default(),
        };
        for def in defs {
            if !def.params.is_empty() {
                local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
            }
        }
        *inner_ctx.local_ops_mut() = Some(Arc::new(local_ops));
    }

    // Second pass: evaluate zero-arg defs and bind their values.
    // Part of #3051: Use eval_in_witness_ctx so primed variables already bound
    // in the witness are accessible. Without this, LET definitions that reference
    // primed variables (e.g., FillBuffer's `LET diskPosA == lo' IN ...`) fail
    // with PrimedVariableNotBound even when lo' was bound earlier in the
    // conjunction by `lo' = (pos \div BuffSz) * BuffSz`.
    for def in defs {
        if def.params.is_empty() {
            let val = eval_in_witness_ctx(&inner_ctx, &def.body, &witness, registry)?;
            inner_ctx.bind_mut(Arc::from(def.name.node.as_str()), val);
        }
    }

    dispatch_enabled(&inner_ctx, body, registry, witness)
}

/// Handle `UNCHANGED <<x, y>>` or `UNCHANGED x`.
///
/// Binds x' = x for each variable.
/// TLC: Tool.java:3508-3526
pub(super) fn handle_unchanged(
    ctx: &EvalCtx,
    vars_expr: &Spanned<Expr>,
    registry: &VarRegistry,
    witness: WitnessState,
) -> CpResult {
    let var_names = collect_unchanged_vars(vars_expr);
    let mut w = witness;
    for name in &var_names {
        if let Some(idx) = registry.get(name.as_str()) {
            let current_val = eval(
                ctx,
                &Spanned::new(
                    Expr::Ident(name.clone(), tla_core::NameId::INVALID),
                    vars_expr.span,
                ),
            )?;
            w = match bind_or_check(idx.as_usize(), current_val, w)? {
                Some(w) => w,
                None => return Ok(None),
            };
        }
    }
    Ok(Some(w))
}

/// Collect variable names from an UNCHANGED expression.
fn collect_unchanged_vars(expr: &Spanned<Expr>) -> Vec<String> {
    match &expr.node {
        Expr::Tuple(elems) => elems.iter().flat_map(collect_unchanged_vars).collect(),
        Expr::Ident(name, _) => vec![name.clone()],
        Expr::StateVar(name, _, _) => vec![name.clone()],
        _ => vec![],
    }
}

// ============================================================================
// Fallback evaluation
// ============================================================================

/// Evaluate an expression with witness bindings injected into the eval context.
///
/// Evaluates an expression with witness bindings visible as a sparse next-state.
///
/// Part of #3365: Instead of building an `Env` HashMap and calling
/// `with_next_state()` (which clones `EvalCtxStable` via `Rc::make_mut`),
/// this binds a `SparseStateEnvRef` directly on the hot `EvalCtx` struct.
/// The evaluator's prime/next-mode lookup paths consult `sparse_next_state_env`.
///
/// #3035: Without this, expressions containing primed variables (e.g., `x' = 3`
/// inside negation or implication) fail with PrimedVariableNotBound because the
/// ENABLED scope clears next_state_env.
fn eval_in_witness_ctx(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    witness: &WitnessState,
    _registry: &VarRegistry,
) -> EvalResult<Value> {
    if witness.is_empty() {
        return eval(ctx, expr);
    }
    // Part of #3365: Bind the sparse overlay directly — zero HashMap allocation,
    // zero Arc::from(name), zero Value::clone per bound var, zero Rc::make_mut.
    let mut eval_ctx = ctx.clone();
    eval_ctx.sparse_next_state_env = Some(SparseStateEnvRef::from_slice(witness.values_slice()));
    eval(&eval_ctx, expr)
}

/// Evaluate an expression as a boolean, preserving the witness on success.
///
/// Falls back to `eval_in_witness_ctx()` so primed variables resolve from
/// witness bindings. TLC: Tool.java:3300 default case.
///
/// #3035: Previously used plain `eval()` which lost witness bindings.
pub(super) fn eval_as_bool(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    witness: WitnessState,
    registry: &VarRegistry,
) -> CpResult {
    match eval_in_witness_ctx(ctx, expr, &witness, registry) {
        Ok(v) => {
            let b = v
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &v, Some(expr.span)))?;
            if b {
                Ok(Some(witness))
            } else {
                Ok(None)
            }
        }
        Err(e) if is_disabled_action_error(&e) => Ok(None),
        Err(e) => Err(e),
    }
}
