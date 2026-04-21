// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{ChcExpr, ChcOp, ChcProblem, ClauseHead, PredicateId};
use rustc_hash::FxHashMap;

/// Extract init values from fact clauses.
pub(super) fn extract_init_values(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
) -> Option<FxHashMap<String, i64>> {
    let fact = problem
        .clauses()
        .iter()
        .find(|c| c.is_fact() && c.head.predicate_id() == Some(pred))?;

    let head_args = match &fact.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let mut init = FxHashMap::default();

    // Extract variable-to-value mappings from body constraint
    let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
    let mut var_values: FxHashMap<String, i64> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                match (&*args[0], &*args[1]) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) => {
                        var_values.insert(v.name.clone(), *n);
                    }
                    (ChcExpr::Int(n), ChcExpr::Var(v)) => {
                        var_values.insert(v.name.clone(), *n);
                    }
                    _ => {}
                }
            }
        }
    }

    // Map head arguments to pre-state variable names
    for (i, pre_var) in pre_vars.iter().enumerate() {
        if let Some(head_arg) = head_args.get(i) {
            match head_arg {
                ChcExpr::Int(n) => {
                    init.insert(pre_var.clone(), *n);
                }
                ChcExpr::Var(v) => {
                    if let Some(val) = var_values.get(&v.name) {
                        init.insert(pre_var.clone(), *val);
                    }
                }
                _ => {}
            }
        }
    }

    Some(init)
}
