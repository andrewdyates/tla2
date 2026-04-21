// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::conjoin;
use super::polynomial::{derive_conserved_quantity, eval_conserved_at_entry};
use super::transfer_entry::{
    apply_source_invariant_to_entry, compute_source_constants, resolve_entry_value,
};
use crate::pdr::model::InvariantModel;
use crate::recurrence::{analyze_transition, ClosedForm};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, Predicate, PredicateId};
use rustc_hash::{FxHashMap, FxHashSet};

/// Derive invariant for a predicate without a fact clause, using conserved
/// quantities from the predicate's own self-loop combined with entry
/// conditions from a solved predecessor.
///
/// This handles multi-predicate problems like s_multipl_25 where:
/// - inv1 has polynomial closed forms and concrete init values → solved
/// - inv2 has polynomial closed forms but no fact clause → needs this
///
/// The approach: for each polynomial variable X with counter N in inv2's
/// self-loop, `LCD*X + correction(N)` is conserved. We evaluate this at
/// entry (from the transfer clause + inv1's invariant) to get the constant,
/// producing invariants like `2*B = F*(F+1) - A*(A+1)`.
pub(super) fn derive_conserved_invariant(
    problem: &ChcProblem,
    pred: &Predicate,
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
    verbose: bool,
) -> Option<ChcExpr> {
    // Step 1: Find self-loop and analyze its transition
    let self_loop = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred.id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 == pred.id
    })?;

    let (pre_vars, transition) = super::extract_normalized_transition(self_loop)?;
    let system = analyze_transition(&transition, &pre_vars)?;

    // Find counter (ConstantDelta with non-zero delta)
    let (n_var_name, _n_delta) = system.solutions.iter().find_map(|(name, cf)| {
        if let ClosedForm::ConstantDelta { delta } = cf {
            if *delta != 0 {
                return Some((name.clone(), *delta));
            }
        }
        None
    })?;

    // Need at least one polynomial variable
    let has_polynomial = system
        .solutions
        .values()
        .any(|cf| matches!(cf, ClosedForm::Polynomial { .. }));
    if !has_polynomial {
        return None;
    }

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: pred {} has polynomial closed forms, counter={}",
            pred.name,
            n_var_name
        );
    }

    // Step 2: Find transfer clause from a solved predecessor
    let trans_clause = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred.id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 != pred.id
            && solved_preds.contains(&c.body.predicates[0].0)
    })?;

    let source_pred_id = trans_clause.body.predicates[0].0;
    let source_args = &trans_clause.body.predicates[0].1;
    let head_args = match &trans_clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let source_interp = model.get(&source_pred_id)?;

    // Step 3: Build mapping from target pre_vars to transfer clause expressions
    // target_pre_var[i] → head_args[i] in transfer clause vars
    let mut target_to_transfer: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for (i, pre_var) in pre_vars.iter().enumerate() {
        if let Some(ha) = head_args.get(i) {
            target_to_transfer.insert(pre_var.clone(), ha.clone());
        }
    }

    // Step 4: Build mapping from transfer clause vars → source pred entry values
    // source_subst: source formal vars → source actual args (transfer body)
    let source_subst: Vec<(ChcVar, ChcExpr)> = source_interp
        .vars
        .iter()
        .zip(source_args.iter())
        .map(|(v, a)| (v.clone(), a.clone()))
        .collect();

    // Extract constraint variable definitions
    let constraint = trans_clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    let mut var_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    var_defs.insert(v.name.clone(), (*args[1]).clone());
                }
                if let ChcExpr::Var(v) = &*args[1] {
                    if !var_defs.contains_key(&v.name) {
                        var_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }

    // Step 5: For the source pred, analyze its self-loop to find which
    // source variables are constant (ConstantDelta(0) with known init)
    let source_constant_values = compute_source_constants(problem, source_pred_id, verbose);

    // Step 6: Compute entry values for each target pre_var
    // For ConstantDelta(0) vars in target: entry = current (use pre_var name)
    // For others: resolve through transfer clause
    let constant_target_vars: FxHashSet<String> = system
        .solutions
        .iter()
        .filter(|(_, cf)| matches!(cf, ClosedForm::ConstantDelta { delta: 0 }))
        .map(|(name, _)| name.clone())
        .collect();

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: constant target vars: {:?}",
            constant_target_vars
        );
    }

    // Step 7: For each polynomial variable, derive conserved quantity invariant
    let mut invariants: Vec<ChcExpr> = Vec::new();

    for (var_name, closed_form) in &system.solutions {
        let coeffs = match closed_form {
            ClosedForm::Polynomial { coeffs } => coeffs,
            _ => continue,
        };

        let (lcd, cq_expr) = match derive_conserved_quantity(var_name, coeffs, &n_var_name) {
            Some(v) => v,
            None => continue,
        };

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: CQ for {} = {:?} (lcd={})",
                var_name,
                cq_expr,
                lcd
            );
        }

        // Compute entry value of X (the polynomial variable)
        let x_entry = resolve_entry_value(
            var_name,
            &target_to_transfer,
            &var_defs,
            &source_subst,
            &source_interp.vars,
            model,
            &source_pred_id,
            &source_constant_values,
            &constant_target_vars,
            &pre_vars,
        );

        // Compute entry value of N (the counter)
        let n_entry = resolve_entry_value(
            &n_var_name,
            &target_to_transfer,
            &var_defs,
            &source_subst,
            &source_interp.vars,
            model,
            &source_pred_id,
            &source_constant_values,
            &constant_target_vars,
            &pre_vars,
        );

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: {} entry={:?}, {} entry={:?}",
                var_name,
                x_entry,
                n_var_name,
                n_entry
            );
        }

        let (x_entry, n_entry) = match (x_entry, n_entry) {
            (Some(x), Some(n)) => (x, n),
            _ => continue,
        };

        // CQ(X_entry, N_entry) = constant
        let cq_at_entry = eval_conserved_at_entry(lcd, &x_entry, &n_var_name, &n_entry, coeffs);

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: CQ_entry for {} = {:?}",
                var_name,
                cq_at_entry
            );
        }

        // Now apply the source invariant to simplify cq_at_entry.
        // The entry value of X may be constrained by the source invariant.
        // Substitute source invariant equalities into the entry expression.
        let simplified = apply_source_invariant_to_entry(
            &cq_at_entry,
            model,
            &source_pred_id,
            &source_subst,
            &constant_target_vars,
            &pre_vars,
            &target_to_transfer,
            verbose,
        );

        let rhs = simplified.unwrap_or(cq_at_entry);

        // Invariant: CQ(X, N) = rhs (simplified entry constant)
        invariants.push(ChcExpr::eq(cq_expr, rhs));
    }

    if invariants.is_empty() {
        return None;
    }

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: derived {} invariant(s) for pred {}",
            invariants.len(),
            pred.name
        );
        for inv in &invariants {
            safe_eprintln!("Algebraic conserved:   {:?}", inv);
        }
    }

    Some(conjoin(invariants))
}

/// Legacy transfer approach: >= weakening of source invariant equalities.
/// Used as fallback when conserved quantity approach doesn't apply.
pub(super) fn derive_transferred_invariant(
    problem: &ChcProblem,
    pred: &Predicate,
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
    solved_invariants: &FxHashMap<PredicateId, Vec<ChcExpr>>,
    verbose: bool,
) -> Option<ChcExpr> {
    if verbose {
        safe_eprintln!(
            "Algebraic: trying transferred invariant for pred {}",
            pred.name
        );
    }
    let trans_clause = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred.id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 != pred.id
            && solved_preds.contains(&c.body.predicates[0].0)
    });
    let trans_clause = match trans_clause {
        Some(c) => c,
        None => {
            if verbose {
                safe_eprintln!(
                    "Algebraic: no inter-predicate transition for pred {}",
                    pred.name
                );
            }
            return None;
        }
    };

    let source_pred_id = trans_clause.body.predicates[0].0;
    let source_args = &trans_clause.body.predicates[0].1;
    let head_args = match &trans_clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let source_interp = model.get(&source_pred_id)?;
    let source_invs = solved_invariants.get(&source_pred_id)?;
    let constraint = trans_clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));

    // Substitution: source pred formal vars → actual body call args
    let source_subst: Vec<(ChcVar, ChcExpr)> = source_interp
        .vars
        .iter()
        .zip(source_args.iter())
        .map(|(v, a)| (v.clone(), a.clone()))
        .collect();

    // Extract variable definitions from constraint
    let mut var_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    var_defs.insert(v.name.clone(), (*args[1]).clone());
                }
                if let ChcExpr::Var(v) = &*args[1] {
                    if !var_defs.contains_key(&v.name) {
                        var_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }

    let mut transferred: Vec<ChcExpr> = Vec::new();
    for inv in source_invs {
        let inv_body = inv.substitute(&source_subst);

        let mut head_to_formal: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (i, ha) in head_args.iter().enumerate() {
            if let ChcExpr::Var(hv) = ha {
                let formal = ChcVar::new(format!("x{i}"), ChcSort::Int);
                if let Some(def) = var_defs.get(&hv.name) {
                    if let ChcExpr::Var(body_var) = def {
                        head_to_formal.push((body_var.clone(), ChcExpr::var(formal)));
                    } else if let ChcExpr::Op(ChcOp::Add, add_args) = def {
                        if add_args.len() == 2 {
                            match (&*add_args[0], &*add_args[1]) {
                                (ChcExpr::Int(c), ChcExpr::Var(bv)) => {
                                    head_to_formal.push((
                                        bv.clone(),
                                        ChcExpr::add(ChcExpr::var(formal), ChcExpr::int(-c)),
                                    ));
                                }
                                (ChcExpr::Var(bv), ChcExpr::Int(c)) => {
                                    head_to_formal.push((
                                        bv.clone(),
                                        ChcExpr::add(ChcExpr::var(formal), ChcExpr::int(-c)),
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                } else {
                    head_to_formal.push((hv.clone(), ChcExpr::var(formal)));
                }
            }
        }

        if head_to_formal.is_empty() {
            continue;
        }

        let in_target_vars = inv_body.substitute(&head_to_formal);

        // Convert equality to >= (sound weakening)
        if let ChcExpr::Op(ChcOp::Eq, eq_args) = &in_target_vars {
            if eq_args.len() == 2 {
                transferred.push(ChcExpr::ge((*eq_args[0]).clone(), (*eq_args[1]).clone()));
            }
        }
    }

    if transferred.is_empty() {
        return None;
    }

    Some(conjoin(transferred))
}
