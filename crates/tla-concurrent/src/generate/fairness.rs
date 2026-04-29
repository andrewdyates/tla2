// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fairness constraint generation for liveness properties.

use tla_core::ast::{Expr, OperatorDef};

use super::helpers::*;
use super::spanned;
use crate::assumptions::FairnessMode;
use crate::model::ConcurrentModel;

/// Generate the Fairness specification operator (if liveness properties exist).
///
/// When FairnessMode is:
/// - None: no fairness constraints (safety only)
/// - WeakFairness: WF_vars(A) for each process action
/// - StrongFairness: SF for condvar/channel, WF for others
pub(super) fn generate_fairness_spec(model: &ConcurrentModel) -> Option<OperatorDef> {
    match model.assumptions.fairness_mode {
        FairnessMode::None => None,
        FairnessMode::WeakFairness => Some(generate_weak_fairness(model)),
        FairnessMode::StrongFairness => Some(generate_strong_fairness(model)),
    }
}

fn generate_weak_fairness(model: &ConcurrentModel) -> OperatorDef {
    let mut wf_conjuncts = Vec::new();

    // WF_vars(Next) as a simple fairness constraint
    // For more granularity, we could generate WF per action
    let vars = Expr::Tuple(
        super::variables::collect_variable_names(model)
            .into_iter()
            .map(|v| spanned(ident(&v)))
            .collect(),
    );

    wf_conjuncts.push(Expr::WeakFair(
        Box::new(spanned(vars)),
        Box::new(spanned(ident("Next"))),
    ));

    make_operator("Fairness", conjoin(wf_conjuncts))
}

fn generate_strong_fairness(model: &ConcurrentModel) -> OperatorDef {
    let vars = Expr::Tuple(
        super::variables::collect_variable_names(model)
            .into_iter()
            .map(|v| spanned(ident(&v)))
            .collect(),
    );

    // SF_vars(Next) for condvar and channel actions, WF for the rest
    // Simplified: use SF for all actions
    let sf = Expr::StrongFair(Box::new(spanned(vars)), Box::new(spanned(ident("Next"))));

    make_operator("Fairness", sf)
}
