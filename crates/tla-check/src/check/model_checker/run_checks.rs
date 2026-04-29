// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-BFS validation: ASSUME and POSTCONDITION evaluation.
//!
//! Extracted from `run.rs` to separate pre/post checks from runtime dispatch
//! (Part of #2385). TLC evaluates ASSUME before BFS and POSTCONDITION after;
//! grouping these together makes the check lifecycle explicit.

use super::{check_error_to_result, CheckResult, ModelChecker, Value};
use crate::{EvalCheckError, RuntimeCheckError};

impl ModelChecker<'_> {
    /// Evaluate ASSUME statements, returning an error CheckResult if any fail.
    /// Returns `None` if all assumptions pass, `Some(CheckResult)` if one fails.
    ///
    /// Delegates to `checker_ops::check_assumes` — the single shared
    /// implementation used by both sequential and parallel checkers (Part of #810).
    pub(super) fn check_assumes(&self) -> Option<CheckResult> {
        crate::checker_ops::check_assumes(&self.ctx, &self.module.assumes)
            .map(|error| check_error_to_result(error, &self.stats))
    }

    /// Evaluate the POSTCONDITION operator after model checking completes.
    ///
    /// TLC evaluates POSTCONDITION once at constant-level after BFS finishes.
    /// It must be a zero-argument operator that returns a boolean.
    /// Returns None if no postcondition is configured or it evaluates to TRUE.
    pub(super) fn check_postcondition(&mut self) -> Option<CheckResult> {
        let name = self.config.postcondition.as_ref()?;
        let runtime_stats = match crate::checker_ops::final_bfs_runtime_stats(&self.stats) {
            Ok(stats) => stats,
            Err(error) => {
                return Some(CheckResult::from_error(error, self.stats.clone()));
            }
        };
        // TLCGet("stats") must observe final checker counters during POSTCONDITION,
        // not the stale per-state runtime snapshot from the last BFS dequeue.
        self.ctx.set_tlc_runtime_stats(Some(runtime_stats));
        self.ctx.set_tlc_level(runtime_stats.diameter as u32);
        // Part of #3458: Clear eval-scope caches before postcondition evaluation.
        crate::eval::clear_for_eval_scope_boundary();
        match self.ctx.eval_op(name) {
            Ok(Value::Bool(true)) => None,
            Ok(Value::Bool(false)) => Some(CheckResult::from_error(
                RuntimeCheckError::PostconditionFalse {
                    operator: name.clone(),
                }
                .into(),
                self.stats.clone(),
            )),
            Ok(_) => Some(CheckResult::from_error(
                RuntimeCheckError::PostconditionFalse {
                    operator: name.clone(),
                }
                .into(),
                self.stats.clone(),
            )),
            Err(e) => Some(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &self.stats,
            )),
        }
    }
}
