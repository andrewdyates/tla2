// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Algebraic invariant synthesis from polynomial closed forms.
//!
//! When a loop has a triangular recurrence with polynomial closed forms
//! (e.g., B' = B + A where A increments linearly), this module derives
//! algebraic invariants by eliminating the iteration count variable n.
//!
//! The resulting invariants are non-linear (e.g., 2*B = A*(A+1)) and
//! cannot be discovered by PDR or CEGAR operating in LIA.
//!
//! # Design Source
//!
//! `designs/2026-03-21-algebraic-invariant-from-polynomial-closed-form.md`
//! Issue: #7170 (s_multipl_22), #5651 (s_multipl_25)

use crate::pdr::model::{InvariantModel, InvariantVerificationMethod, PredicateInterpretation};
use crate::recurrence::{analyze_transition, ClosedForm};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId};
use rustc_hash::{FxHashMap, FxHashSet};

mod init;
mod polynomial;
mod transfer;
mod transfer_entry;
mod validate;

#[cfg(test)]
mod tests;

use self::init::extract_init_values;
use self::polynomial::eliminate_iteration_count;
use self::transfer::{derive_conserved_invariant, derive_transferred_invariant};
use self::validate::{validate_model_with_algebraic_fallback, AlgebraicValidationResult};

struct NormalizedSelfLoop {
    pre_vars: Vec<String>,
    updates: FxHashMap<String, ChcExpr>,
    constraint: ChcExpr,
}

/// Result of algebraic invariant synthesis.
#[derive(Debug)]
pub(crate) enum AlgebraicResult {
    /// The system is safe: an inductive invariant was found.
    Safe(InvariantModel),
    /// The system is unsafe: concrete evaluation proved bad states are reachable
    /// from a correct algebraic invariant. The algebraic closed form is valid
    /// (init and transition clauses hold) but the query clause admits bad states.
    Unsafe,
    /// Algebraic synthesis is not applicable or failed.
    NotApplicable,
}

/// Try to solve the CHC problem using algebraic invariant synthesis.
///
/// Returns `AlgebraicResult::Safe(model)` if algebraic invariants can be derived
/// and the safety condition is implied. Returns `AlgebraicResult::Unsafe` when
/// the algebraic invariant is correct but bad states are reachable (concrete
/// evaluation proves the query clause is satisfiable). Returns
/// `AlgebraicResult::NotApplicable` if the approach doesn't apply or fails.
pub(crate) fn try_algebraic_solve(problem: &ChcProblem, verbose: bool) -> AlgebraicResult {
    let predicates = problem.predicates();
    if predicates.is_empty() {
        return AlgebraicResult::NotApplicable;
    }

    let mut model = InvariantModel::new();
    let mut solved_preds: FxHashSet<PredicateId> = FxHashSet::default();
    let mut solved_invariants: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

    for pred in predicates {
        if verbose {
            safe_eprintln!("Algebraic: checking pred {} (id {:?})", pred.name, pred.id);
        }
        let self_loop = find_self_loop(problem, pred.id);
        let self_loop = match self_loop {
            Some(c) => c,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} has no self-loop", pred.name);
                }
                continue;
            }
        };

        let normalized = match extract_normalized_self_loop(self_loop) {
            Some(t) => t,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} transition extraction failed", pred.name);
                }
                continue;
            }
        };
        let pre_vars = normalized.pre_vars.clone();
        let transition = normalized_transition_expr(&normalized.updates);
        let init_values = match extract_init_values(problem, pred.id, &pre_vars) {
            Some(v) => v,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} init value extraction failed", pred.name);
                }
                continue;
            }
        };
        let constant_deltas = extract_constant_deltas(&normalized.updates);

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} pre_vars={:?}, transition={:?}",
                pred.name,
                pre_vars,
                transition
            );
        }

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} init_values={:?}",
                pred.name,
                init_values
            );
        }

        let mut invariants = derive_auxiliary_invariants(
            problem,
            pred.id,
            &normalized,
            &constant_deltas,
            &init_values,
        );

        let mut has_polynomial = false;
        if let Some(system) = analyze_transition(&transition, &pre_vars) {
            if verbose {
                for (name, cf) in &system.solutions {
                    safe_eprintln!(
                        "Algebraic: pred {} var {} closed form: {:?}",
                        pred.name,
                        name,
                        cf
                    );
                }
            }

            has_polynomial = system
                .solutions
                .values()
                .any(|cf| matches!(cf, ClosedForm::Polynomial { .. }));

            if has_polynomial {
                invariants.extend(eliminate_iteration_count(&system, &init_values));

                // Add constant-value invariants for ConstantDelta(0) variables.
                // These are needed so that transfer clause validation can constrain
                // the constant variables' values (e.g., G=0 in s_multipl_25).
                for (name, cf) in &system.solutions {
                    if matches!(cf, ClosedForm::ConstantDelta { delta: 0 }) {
                        if let Some(&val) = init_values.get(name) {
                            let var = ChcVar::new(name.clone(), ChcSort::Int);
                            invariants.push(ChcExpr::eq(ChcExpr::var(var), ChcExpr::int(val)));
                        }
                    }
                }
            }
        } else if verbose {
            safe_eprintln!(
                "Algebraic: pred {} analyze_transition returned None",
                pred.name
            );
        }

        if !has_polynomial && invariants.is_empty() {
            if verbose {
                safe_eprintln!(
                    "Algebraic: pred {} has no polynomial or auxiliary invariants",
                    pred.name
                );
            }
            continue;
        }
        if invariants.is_empty() {
            continue;
        }

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} has {} invariant(s) from algebraic/auxiliary synthesis",
                pred.name,
                invariants.len()
            );
        }

        let pred_vars: Vec<ChcVar> = pre_vars
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let sort = pred.arg_sorts.get(i).cloned().unwrap_or(ChcSort::Int);
                ChcVar::new(name.clone(), sort)
            })
            .collect();

        solved_invariants.insert(pred.id, invariants.clone());
        let formula = conjoin(invariants);
        if verbose {
            safe_eprintln!("Algebraic: pred {} formula {:?}", pred.name, formula);
        }
        model.set(pred.id, PredicateInterpretation::new(pred_vars, formula));
        model.verification_method = InvariantVerificationMethod::AlgebraicClosedForm;
        solved_preds.insert(pred.id);
    }

    // Phase 2: For unsolved predicates, try conserved quantity approach first
    // (exact invariant from self-loop + entry conditions), then fall back to
    // >= weakening of source invariant equalities.
    for pred in predicates {
        if solved_preds.contains(&pred.id) {
            continue;
        }
        let formula = derive_conserved_invariant(problem, pred, &model, &solved_preds, verbose)
            .or_else(|| {
                derive_transferred_invariant(
                    problem,
                    pred,
                    &model,
                    &solved_preds,
                    &solved_invariants,
                    verbose,
                )
            });
        if let Some(formula) = formula {
            let pred_vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            model.set(pred.id, PredicateInterpretation::new(pred_vars, formula));
            solved_preds.insert(pred.id);
        }
    }

    // Fill remaining unsolved predicates with `true`
    for pred in predicates {
        if !solved_preds.contains(&pred.id) {
            let pred_vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            model.set(
                pred.id,
                PredicateInterpretation::new(pred_vars, ChcExpr::Bool(true)),
            );
        }
    }

    if solved_preds.is_empty() {
        return AlgebraicResult::NotApplicable;
    }

    // Validate via SMT
    match validate_model_with_algebraic_fallback(problem, &model, &solved_preds, verbose) {
        AlgebraicValidationResult::Valid => {
            if verbose {
                safe_eprintln!("Algebraic: model validated successfully");
            }
            AlgebraicResult::Safe(model)
        }
        AlgebraicValidationResult::UnsafeDetected => {
            if verbose {
                safe_eprintln!(
                    "Algebraic: model validation detected UNSAFE \
                     (invariant correct but bad states reachable)"
                );
            }
            AlgebraicResult::Unsafe
        }
        AlgebraicValidationResult::Invalid => {
            if verbose {
                safe_eprintln!("Algebraic: model validation failed");
            }
            AlgebraicResult::NotApplicable
        }
    }
}

pub(super) fn conjoin(exprs: Vec<ChcExpr>) -> ChcExpr {
    match exprs.len() {
        0 => ChcExpr::Bool(true),
        1 => exprs.into_iter().next().unwrap(),
        _ => exprs.into_iter().reduce(ChcExpr::and).unwrap(),
    }
}

/// Find the self-loop clause for a predicate.
fn find_self_loop(problem: &ChcProblem, pred: PredicateId) -> Option<&crate::HornClause> {
    problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 == pred
    })
}

/// Extract normalized transition from a self-loop clause.
///
/// Returns (pre_var_names, transition_expr) where the transition uses
/// `{var}_next` naming for post-state variables, with all inter-variable
/// references resolved (forward substitution).
///
/// Example: body(A,B), constraint (= C (+ 1 A)) (= D (+ B C)), head(C,D)
/// → pre_vars = [`A`, `B`]
///   transition = (and (= A_next (+ 1 A)) (= B_next (+ B (+ 1 A))))
fn extract_normalized_transition(clause: &crate::HornClause) -> Option<(Vec<String>, ChcExpr)> {
    let normalized = extract_normalized_self_loop(clause)?;
    let transition = normalized_transition_expr(&normalized.updates);
    Some((normalized.pre_vars, transition))
}

fn extract_normalized_self_loop(clause: &crate::HornClause) -> Option<NormalizedSelfLoop> {
    let body_args = &clause.body.predicates[0].1;
    let head_args = match &clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    // Pre-state variable names from body predicate args
    let pre_vars: Vec<String> = body_args
        .iter()
        .filter_map(|a| match a {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        })
        .collect();

    if pre_vars.len() != body_args.len() || pre_vars.len() != head_args.len() {
        return None;
    }

    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));

    // Step 1: Collect head variables that may be defined in the body constraint.
    let post_vars: Vec<String> = head_args
        .iter()
        .filter_map(|arg| match arg {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        })
        .collect();

    // Step 2: Extract definitions of head variables from constraint.
    // Look for (= post_var expr) patterns.
    let mut post_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    if post_vars.contains(&v.name) {
                        post_defs.insert(v.name.clone(), (*args[1]).clone());
                    }
                }
                // Also check reversed: (= expr post_var)
                if let ChcExpr::Var(v) = &*args[1] {
                    if post_vars.contains(&v.name) && !post_defs.contains_key(&v.name) {
                        post_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }

    // Step 3: Topologically resolve post-var references in definitions.
    // If post_var C appears in D's definition, substitute C's definition first.
    let resolved = resolve_post_var_refs(&post_vars, &post_defs);
    let substitution: Vec<(ChcVar, ChcExpr)> = resolved
        .iter()
        .map(|(name, expr)| (ChcVar::new(name.clone(), ChcSort::Int), expr.clone()))
        .collect();

    // Step 4: Build normalized updates keyed by pre-state variable name.
    // Strip BvToInt ITE/mod wrappers (#7931) so that extract_constant_deltas
    // and derive_auxiliary_invariants see the underlying linear structure.
    // Without stripping, updates like ite(i+1 < 2^32, i+1, i+1 - 2^32)
    // won't match the x+K or x-K patterns needed for bound derivation.
    let mut updates: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for (head_arg, pre_var) in head_args.iter().zip(pre_vars.iter()) {
        let update = match head_arg {
            ChcExpr::Var(v) => resolved
                .get(&v.name)
                .cloned()
                .unwrap_or_else(|| ChcExpr::var(v.clone())),
            expr => expr.clone(),
        };
        let update = if substitution.is_empty() {
            update
        } else {
            update.substitute(&substitution)
        };
        let update = crate::recurrence::strip_bv_wrapping(&update);
        updates.insert(pre_var.clone(), update);
    }

    if updates.is_empty() {
        return None;
    }

    Some(NormalizedSelfLoop {
        pre_vars,
        updates,
        constraint,
    })
}

fn normalized_transition_expr(updates: &FxHashMap<String, ChcExpr>) -> ChcExpr {
    let mut transition_conjuncts: Vec<ChcExpr> = updates
        .iter()
        .map(|(pre_var, def)| {
            let next_var = ChcVar::new(format!("{pre_var}_next"), ChcSort::Int);
            ChcExpr::eq(ChcExpr::var(next_var), def.clone())
        })
        .collect();
    transition_conjuncts.sort_by_cached_key(|expr| format!("{expr:?}"));
    conjoin(transition_conjuncts)
}

/// Resolve post-variable references in definitions by forward substitution.
///
/// If D is defined as (+ B C) and C is defined as (+ 1 A),
/// the resolved definition of D is (+ B (+ 1 A)).
fn resolve_post_var_refs(
    post_vars: &[String],
    defs: &FxHashMap<String, ChcExpr>,
) -> FxHashMap<String, ChcExpr> {
    let mut resolved = defs.clone();

    // Simple iterative resolution (handles single-level dependencies)
    // For deeper chains, we'd need topological ordering, but CHC benchmarks
    // typically have at most 1 level of post-var dependency.
    for _pass in 0..post_vars.len() {
        let snapshot = resolved.clone();
        for (var, def) in resolved.iter_mut() {
            let substitution: Vec<(ChcVar, ChcExpr)> = post_vars
                .iter()
                .filter(|pv| *pv != var)
                .filter_map(|pv| {
                    snapshot
                        .get(pv)
                        .map(|d| (ChcVar::new(pv.clone(), ChcSort::Int), d.clone()))
                })
                .collect();
            if !substitution.is_empty() {
                *def = def.substitute(&substitution);
            }
        }
    }

    resolved
}

fn derive_auxiliary_invariants(
    problem: &ChcProblem,
    pred: PredicateId,
    normalized: &NormalizedSelfLoop,
    constant_deltas: &FxHashMap<String, i64>,
    init_values: &FxHashMap<String, i64>,
) -> Vec<ChcExpr> {
    let mut invariants = Vec::new();
    let mut lower_bounds: FxHashMap<String, i64> = FxHashMap::default();

    for (name, delta) in constant_deltas {
        let Some(&init) = init_values.get(name) else {
            continue;
        };
        let var = int_var_expr(name);
        if *delta > 0 {
            invariants.push(ChcExpr::ge(var, ChcExpr::int(init)));
            lower_bounds
                .entry(name.clone())
                .and_modify(|bound| *bound = (*bound).max(init))
                .or_insert(init);
        } else if *delta < 0 {
            invariants.push(ChcExpr::le(var, ChcExpr::int(init)));
        }
    }

    let unchanged_vars: FxHashSet<String> = constant_deltas
        .iter()
        .filter_map(|(name, delta)| (*delta == 0).then_some(name.clone()))
        .collect();

    for fact_conjunct in normalized_fact_conjuncts(problem, pred, &normalized.pre_vars) {
        if fact_conjunct
            .vars()
            .iter()
            .all(|var| unchanged_vars.contains(&var.name))
        {
            if let Some((var, lower)) = lower_bound_from_atom(&fact_conjunct) {
                lower_bounds
                    .entry(var.clone())
                    .and_modify(|bound| *bound = (*bound).max(lower))
                    .or_insert(lower);
            }
            invariants.push(fact_conjunct);
        }
    }

    for guard_conjunct in normalized.constraint.conjuncts() {
        if !guard_conjunct
            .vars()
            .iter()
            .all(|var| normalized.pre_vars.contains(&var.name))
        {
            continue;
        }

        if let Some(inv) =
            derive_guard_bridge_invariant(guard_conjunct, constant_deltas, &unchanged_vars)
        {
            invariants.push(inv);
        }
    }

    for (var_name, update) in &normalized.updates {
        let Some(&init) = init_values.get(var_name) else {
            continue;
        };
        if init < 1 {
            continue;
        }

        let Some(factor_lb) = multiplicative_factor_lower_bound(update, var_name, &lower_bounds)
        else {
            continue;
        };
        if factor_lb >= 1 {
            invariants.push(ChcExpr::ge(int_var_expr(var_name), ChcExpr::int(init)));
        }
    }

    invariants
}

fn normalized_fact_conjuncts(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
) -> Vec<ChcExpr> {
    let Some(fact) = problem
        .clauses()
        .iter()
        .find(|clause| clause.is_fact() && clause.head.predicate_id() == Some(pred))
    else {
        return Vec::new();
    };

    let ClauseHead::Predicate(_, head_args) = &fact.head else {
        return Vec::new();
    };

    let substitution: Vec<(ChcVar, ChcExpr)> = head_args
        .iter()
        .zip(pre_vars.iter())
        .filter_map(|(head_arg, pre_var)| match head_arg {
            ChcExpr::Var(v) => Some((
                v.clone(),
                ChcExpr::var(ChcVar::new(pre_var.clone(), v.sort.clone())),
            )),
            _ => None,
        })
        .collect();

    fact.body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true))
        .conjuncts()
        .into_iter()
        .map(|conjunct| conjunct.substitute(&substitution))
        .collect()
}

fn derive_guard_bridge_invariant(
    guard: &ChcExpr,
    constant_deltas: &FxHashMap<String, i64>,
    unchanged_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let ChcExpr::Op(op, args) = guard else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let lhs = &args[0];
    let rhs = &args[1];

    if let Some(inv) = bridge_counter_comparison(lhs, rhs, op, constant_deltas, unchanged_vars) {
        return Some(inv);
    }
    bridge_counter_comparison(
        rhs,
        lhs,
        &swap_comparison(op)?,
        constant_deltas,
        unchanged_vars,
    )
}

fn bridge_counter_comparison(
    counter_side: &ChcExpr,
    bound_side: &ChcExpr,
    op: &ChcOp,
    constant_deltas: &FxHashMap<String, i64>,
    unchanged_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let ChcExpr::Var(counter_var) = counter_side else {
        return None;
    };
    let delta = *constant_deltas.get(&counter_var.name)?;
    if !bound_side
        .vars()
        .iter()
        .all(|var| unchanged_vars.contains(&var.name))
    {
        return None;
    }

    match (delta.signum(), op) {
        (1, &ChcOp::Lt) | (1, &ChcOp::Le) => Some(ChcExpr::le(
            int_var_expr(&counter_var.name),
            upper_bridge_bound(bound_side, matches!(op, ChcOp::Le)),
        )),
        (-1, &ChcOp::Gt) | (-1, &ChcOp::Ge) => Some(ChcExpr::ge(
            int_var_expr(&counter_var.name),
            lower_bridge_bound(bound_side, matches!(op, ChcOp::Ge)),
        )),
        _ => None,
    }
}

fn upper_bridge_bound(bound_side: &ChcExpr, inclusive_guard: bool) -> ChcExpr {
    if inclusive_guard {
        ChcExpr::add(bound_side.clone(), ChcExpr::int(1)).simplify_constants()
    } else {
        bound_side.clone()
    }
}

fn lower_bridge_bound(bound_side: &ChcExpr, inclusive_guard: bool) -> ChcExpr {
    if inclusive_guard {
        ChcExpr::sub(bound_side.clone(), ChcExpr::int(1)).simplify_constants()
    } else {
        bound_side.clone()
    }
}

fn multiplicative_factor_lower_bound(
    update: &ChcExpr,
    updated_var: &str,
    lower_bounds: &FxHashMap<String, i64>,
) -> Option<i64> {
    let ChcExpr::Op(ChcOp::Mul, args) = update else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let lhs = &args[0];
    let rhs = &args[1];

    if matches!(lhs.as_ref(), ChcExpr::Var(v) if v.name == updated_var) {
        return expr_lower_bound(rhs, lower_bounds);
    }
    if matches!(rhs.as_ref(), ChcExpr::Var(v) if v.name == updated_var) {
        return expr_lower_bound(lhs, lower_bounds);
    }
    None
}

fn expr_lower_bound(expr: &ChcExpr, lower_bounds: &FxHashMap<String, i64>) -> Option<i64> {
    match expr {
        ChcExpr::Int(value) => Some(*value),
        ChcExpr::Var(v) => lower_bounds.get(&v.name).copied(),
        _ => None,
    }
}

fn lower_bound_from_atom(atom: &ChcExpr) -> Option<(String, i64)> {
    let ChcExpr::Op(op, args) = atom else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    match (&*args[0], &*args[1], op) {
        (ChcExpr::Var(v), ChcExpr::Int(c), ChcOp::Ge) => Some((v.name.clone(), *c)),
        (ChcExpr::Var(v), ChcExpr::Int(c), ChcOp::Gt) => Some((v.name.clone(), c + 1)),
        (ChcExpr::Int(c), ChcExpr::Var(v), ChcOp::Le) => Some((v.name.clone(), *c)),
        (ChcExpr::Int(c), ChcExpr::Var(v), ChcOp::Lt) => Some((v.name.clone(), c + 1)),
        _ => None,
    }
}

fn swap_comparison(op: &ChcOp) -> Option<ChcOp> {
    Some(match *op {
        ChcOp::Lt => ChcOp::Gt,
        ChcOp::Le => ChcOp::Ge,
        ChcOp::Gt => ChcOp::Lt,
        ChcOp::Ge => ChcOp::Le,
        _ => return None,
    })
}

fn int_var_expr(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name.to_string(), ChcSort::Int))
}

fn extract_constant_deltas(updates: &FxHashMap<String, ChcExpr>) -> FxHashMap<String, i64> {
    let mut deltas = FxHashMap::default();
    for (var_name, update) in updates {
        let delta = match update {
            ChcExpr::Var(v) if v.name == *var_name => Some(0),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == *var_name => Some(*c),
                (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == *var_name => Some(*c),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == *var_name => Some(-*c),
                _ => None,
            },
            _ => None,
        };
        if let Some(delta) = delta {
            deltas.insert(var_name.clone(), delta);
        }
    }
    deltas
}
