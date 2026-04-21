// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Next relation generation: disjunction of all process actions.

use tla_core::ast::{BoundVar, Expr, OperatorDef};

use super::actions;
use super::helpers::*;
use super::{spanned, variables};
use crate::model::ConcurrentModel;

/// Generate the Next operator.
///
/// ```tla
/// Next ==
///     \/ Action_main_s0_s1
///     \/ Action_main_s1_s2
///     \/ Action_thread_0_s0_s1
///     \/ ...
///     \/ (AllDone /\ UNCHANGED <<pc, alive, ...>>)
/// ```
///
/// The AllDone stuttering disjunct prevents the checker from reporting
/// deadlock when all processes have genuinely terminated. Without it,
/// a state where all processes are in terminal states would have no
/// successor and be flagged as a deadlock.
pub(super) fn generate_next(model: &ConcurrentModel) -> OperatorDef {
    let mut action_refs = Vec::new();

    for process in &model.processes {
        for transition in &process.transitions {
            let name = actions::action_name(&process.id, transition);
            action_refs.push(ident(&name));
        }
    }

    // Stuttering step: when all processes are done, allow UNCHANGED
    // AllDone == \A p \in Processes : pc[p] \in TerminalStates \/ alive[p] = FALSE
    let all_done = Expr::Forall(
        vec![BoundVar {
            name: spanned("p".to_string()),
            domain: Some(Box::new(spanned(ident("Processes")))),
            pattern: None,
        }],
        Box::new(spanned(or(
            in_set(func_apply(ident("pc"), ident("p")), ident("TerminalStates")),
            eq(func_apply(ident("alive"), ident("p")), bool_lit(false)),
        ))),
    );

    let all_vars = variables::collect_variable_names(model);
    let var_refs: Vec<&str> = all_vars.iter().map(String::as_str).collect();
    let stutter = and(all_done, unchanged(&var_refs));

    action_refs.push(stutter);

    make_operator_with_prime("Next", disjoin(action_refs))
}
