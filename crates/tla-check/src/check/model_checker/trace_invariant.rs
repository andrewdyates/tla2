// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace invariant checking (Apalache-style `--trace-inv`).
//!
//! A trace invariant is a TLA+ operator that takes a single `Seq(Record)`
//! argument representing the execution history up to the current state.
//! Each record in the sequence has fields matching the spec's state variables.
//!
//! During BFS, after a new state passes regular invariant checks, each trace
//! invariant is evaluated with the trace (sequence of states from init to
//! current). If any trace invariant returns FALSE, a violation is reported.
//!
//! Part of #3752: Apalache Gap 4.

use std::sync::Arc;

use crate::check::model_checker::ModelChecker;
use crate::check::{CheckError, Trace};
use crate::state::ArrayState;
use crate::state::{Fingerprint, State};
use tla_value::value::SeqValue;
use tla_value::Value;

/// Outcome of checking trace invariants for one state.
pub(crate) enum TraceInvariantOutcome {
    /// All trace invariants passed (or none configured).
    Ok,
    /// A trace invariant was violated.
    Violation {
        /// Name of the violated trace invariant operator.
        invariant: String,
        /// The trace that caused the violation (for counterexample reporting).
        trace: Trace,
    },
    /// An error occurred during trace invariant evaluation.
    Error(CheckError),
}

/// Build a `Value::Seq` of `Value::Record` from a sequence of states.
///
/// Each state is converted to a record value with fields matching the
/// spec's state variables. The resulting sequence is 1-indexed per TLA+
/// convention (handled internally by `SeqValue`).
pub(crate) fn states_to_trace_seq(states: &[State]) -> Value {
    let records: Vec<Value> = states.iter().map(|s| s.to_record()).collect();
    Value::Seq(Arc::new(SeqValue::from(records)))
}

impl<'a> ModelChecker<'a> {
    /// Check all configured trace invariants for a newly discovered successor.
    ///
    /// Because this is called BEFORE the successor is admitted to the trace
    /// file, we reconstruct the trace to the parent (which IS in storage)
    /// and then append the successor state to form the complete history.
    ///
    /// Returns `TraceInvariantOutcome::Ok` if all pass, or
    /// `TraceInvariantOutcome::Violation` on the first failure.
    ///
    /// Part of #3780: trace invariant checking for history-dependent properties.
    pub(super) fn check_trace_invariants(
        &mut self,
        parent_fp: Fingerprint,
        succ: &ArrayState,
        succ_fp: Fingerprint,
    ) -> TraceInvariantOutcome {
        if self.config.trace_invariants.is_empty() {
            return TraceInvariantOutcome::Ok;
        }

        // Convert the successor ArrayState to a full State for trace building.
        let registry = self.ctx.var_registry().clone();
        let succ_state = succ.to_state(&registry);

        // Build the trace: reconstruct the prefix to the parent, then append
        // the successor. For initial states (parent_fp == succ_fp), the trace
        // is just the successor itself.
        let trace = if parent_fp == succ_fp {
            // Initial state: no parent to reconstruct.
            Trace::from_states(vec![succ_state.clone()])
        } else {
            let parent_trace = self.reconstruct_trace(parent_fp);
            if parent_trace.is_empty() {
                // Parent trace reconstruction failed. This can happen in
                // no-trace mode or when the trace file is unavailable.
                // Fall back to a single-state trace (the successor only).
                // This is conservative: the invariant can still detect
                // violations that are visible from a single state.
                Trace::from_states(vec![succ_state.clone()])
            } else {
                let mut states = parent_trace.states;
                states.push(succ_state.clone());
                Trace::from_states(states)
            }
        };

        // Build the Seq(Record) value from the trace states.
        let trace_seq = states_to_trace_seq(&trace.states);

        // Clear state-dependent caches before evaluating trace invariants.
        crate::eval::clear_for_state_boundary();

        // Evaluate each trace invariant operator.
        for inv_name in &self.config.trace_invariants {
            match self.ctx.eval_op_with_args(inv_name, &[trace_seq.clone()]) {
                Ok(Value::Bool(true)) => {
                    // Trace invariant passed.
                }
                Ok(Value::Bool(false)) => {
                    return TraceInvariantOutcome::Violation {
                        invariant: inv_name.clone(),
                        trace,
                    };
                }
                Ok(other) => {
                    return TraceInvariantOutcome::Error(
                        crate::EvalCheckError::InvariantNotBoolean(format!(
                            "trace invariant {} returned non-boolean: {}",
                            inv_name, other
                        ))
                        .into(),
                    );
                }
                Err(e) => {
                    return TraceInvariantOutcome::Error(crate::EvalCheckError::Eval(e).into());
                }
            }
        }

        TraceInvariantOutcome::Ok
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::State;
    use tla_value::Value;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_states_to_trace_seq_empty() {
        let states: Vec<State> = vec![];
        let seq = states_to_trace_seq(&states);
        match seq {
            Value::Seq(ref s) => assert_eq!(s.len(), 0),
            _ => panic!("expected Seq, got {:?}", seq),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_states_to_trace_seq_single_state() {
        let state = State::from_pairs(vec![("x", Value::SmallInt(1)), ("y", Value::Bool(true))]);
        let seq = states_to_trace_seq(&[state]);
        match seq {
            Value::Seq(ref s) => {
                assert_eq!(s.len(), 1);
                // The single element should be a record with x=1, y=TRUE
                let record = s.get(0).expect("element 0 should exist");
                match record {
                    Value::Record(ref r) => {
                        assert_eq!(r.len(), 2);
                    }
                    _ => panic!("expected Record, got {:?}", record),
                }
            }
            _ => panic!("expected Seq, got {:?}", seq),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_states_to_trace_seq_multi_state() {
        let s1 = State::from_pairs(vec![("x", Value::SmallInt(0))]);
        let s2 = State::from_pairs(vec![("x", Value::SmallInt(1))]);
        let s3 = State::from_pairs(vec![("x", Value::SmallInt(2))]);
        let seq = states_to_trace_seq(&[s1, s2, s3]);
        match seq {
            Value::Seq(ref s) => {
                assert_eq!(s.len(), 3);
                // Verify each element is a record
                for i in 0..3 {
                    let record = s.get(i).expect("element should exist");
                    assert!(
                        matches!(record, Value::Record(_)),
                        "element {} should be Record, got {:?}",
                        i,
                        record
                    );
                }
            }
            _ => panic!("expected Seq, got {:?}", seq),
        }
    }
}
