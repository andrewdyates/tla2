// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Action label identification for trace reconstruction (sequential checker).
//!
//! Part of #2696 Step 3 / #2470: delegates to the shared implementation in
//! `checker_ops::trace_actions` for parity with the parallel checker.

use super::{ModelChecker, State};
use crate::check::ActionLabel;
use crate::checker_ops::{identify_action_labels, ActionLabelCtx};

impl<'a> ModelChecker<'a> {
    /// Identify action labels for each state in a trace.
    ///
    /// For state 0, returns `<Initial predicate>`. For subsequent states, evaluates
    /// each action disjunct of the Next relation to determine which action produced
    /// the transition from state[i-1] to state[i].
    ///
    /// Delegates to `checker_ops::identify_action_labels` — the canonical shared
    /// implementation used by both sequential and parallel checker paths.
    pub(super) fn identify_action_labels(&mut self, states: &[State]) -> Vec<ActionLabel> {
        let next_name = match &self.trace.cached_next_name {
            Some(name) => name.clone(),
            None => {
                // No Next name cached — return placeholder labels
                return placeholder_labels(states.len());
            }
        };
        // Part of #3296: resolve CONSTANT operator replacement for the actual
        // definition lookup. cached_next_name is the raw config name.
        let resolved_next_name = self.ctx.resolve_op_name(&next_name).to_string();

        let label_ctx = ActionLabelCtx {
            next_name: &next_name,
            next_def: self.module.op_defs.get(&resolved_next_name),
            file_id_to_path: &self.module.file_id_to_path,
            module_name: &self.module.root_name,
        };

        identify_action_labels(&mut self.ctx, &label_ctx, states)
    }
}

/// Return placeholder labels for a trace of the given length.
fn placeholder_labels(len: usize) -> Vec<ActionLabel> {
    if len == 0 {
        return Vec::new();
    }
    let mut labels = Vec::with_capacity(len);
    labels.push(ActionLabel {
        name: "Initial predicate".to_string(),
        source_location: None,
    });
    for _ in 1..len {
        labels.push(ActionLabel {
            name: "Action".to_string(),
            source_location: None,
        });
    }
    labels
}

#[cfg(test)]
#[path = "trace_actions_tests.rs"]
mod trace_actions_tests;
