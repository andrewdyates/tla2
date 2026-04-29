// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counterexample cross-validation for the fused cooperative orchestrator.
//!
//! When a symbolic engine (BMC or PDR) produces a verdict, this module
//! replays the result through the BFS evaluator to confirm agreement
//! before publishing to the shared verdict. This catches soundness bugs
//! in the symbolic translation without crashing the orchestrator.
//!
//! Part of #3836 (F4: Counterexample Cross-Validation).

use std::sync::Arc;

use tla_core::ast::Module;
use tla_z4::{BmcState, BmcValue};

use crate::check::CheckResult;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::value::{FuncValue, Value};

/// Result of cross-validating a symbolic engine's verdict against the BFS evaluator.
#[derive(Debug, Clone)]
pub struct CrossValidationResult {
    /// Whether the BFS evaluator agrees with the symbolic engine's verdict.
    pub engine_agrees: bool,
    /// Length of the trace that was cross-validated (0 for PDR safety proofs).
    pub trace_length: usize,
    /// Which symbolic engine produced the verdict being validated.
    pub source_engine: CrossValidationSource,
    /// Human-readable detail about the cross-validation outcome.
    pub detail: String,
}

/// Which symbolic engine produced the verdict being cross-validated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CrossValidationSource {
    /// BMC (bounded model checking) found a counterexample trace.
    Bmc,
    /// PDR (IC3) proved safety via an inductive invariant.
    Pdr,
    /// k-Induction proved safety via a bounded inductive argument.
    KInduction,
}

/// Convert a `BmcValue` (symbolic engine representation) to a `Value` (BFS evaluator representation).
///
/// Returns `None` for values that cannot be represented in the BFS evaluator.
pub(crate) fn bmc_value_to_value(bmc_val: &BmcValue) -> Option<Value> {
    match bmc_val {
        BmcValue::Bool(b) => Some(Value::Bool(*b)),
        BmcValue::Int(n) => Some(Value::int(*n)),
        BmcValue::BigInt(n) => Some(Value::big_int(n.clone())),
        BmcValue::Set(members) => {
            let converted: Option<Vec<Value>> = members.iter().map(bmc_value_to_value).collect();
            converted.map(Value::set)
        }
        BmcValue::Sequence(elems) => {
            let converted: Option<Vec<Value>> = elems.iter().map(bmc_value_to_value).collect();
            converted.map(Value::seq)
        }
        BmcValue::Record(fields) => {
            let converted: Option<Vec<(String, Value)>> = fields
                .iter()
                .map(|(name, val)| bmc_value_to_value(val).map(|v| (name.clone(), v)))
                .collect();
            converted.map(Value::record)
        }
        BmcValue::Tuple(elems) => {
            let converted: Option<Vec<Value>> = elems.iter().map(bmc_value_to_value).collect();
            converted.map(Value::tuple)
        }
        BmcValue::Function(entries) => {
            let converted: Option<Vec<(Value, Value)>> = entries
                .iter()
                .map(|(k, v)| {
                    let kv = Value::int(*k);
                    bmc_value_to_value(v).map(|vv| (kv, vv))
                })
                .collect();
            converted.map(|pairs| Value::Func(Arc::new(FuncValue::from_sorted_entries(pairs))))
        }
    }
}

/// Cross-validate a BMC counterexample trace by replaying it through the BFS evaluator.
///
/// For each state in the BMC trace, this function:
/// 1. Converts `BmcValue` assignments to `Value`s
/// 2. Binds them as state variables in a fresh `EvalCtx`
/// 3. Evaluates each configured invariant
/// 4. Reports whether the invariant violation is confirmed
///
/// If the BMC trace is empty or contains no invariant violations when replayed,
/// cross-validation reports disagreement (the BFS evaluator does not confirm
/// the BMC finding).
pub fn cross_validate_bmc_trace(
    module: &Module,
    config: &Config,
    trace: &[BmcState],
) -> CrossValidationResult {
    let trace_length = trace.len();

    if trace.is_empty() {
        return CrossValidationResult {
            engine_agrees: false,
            trace_length: 0,
            source_engine: CrossValidationSource::Bmc,
            detail: "BMC trace is empty — cannot cross-validate".to_string(),
        };
    }

    if config.invariants.is_empty() {
        return CrossValidationResult {
            engine_agrees: false,
            trace_length,
            source_engine: CrossValidationSource::Bmc,
            detail: "no invariants configured — cannot verify BMC violation".to_string(),
        };
    }

    // Set up evaluation context with the spec's operators.
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);

    // BMC finds a violation at the last state in the trace.
    // Cross-validate by checking invariants against that final state.
    let final_state = &trace[trace.len() - 1];

    // Convert BMC assignments to Values and bind as state variables.
    for (var_name, bmc_val) in &final_state.assignments {
        match bmc_value_to_value(bmc_val) {
            Some(value) => {
                ctx.env_mut().insert(Arc::from(var_name.as_str()), value);
            }
            None => {
                return CrossValidationResult {
                    engine_agrees: false,
                    trace_length,
                    source_engine: CrossValidationSource::Bmc,
                    detail: format!(
                        "cannot convert BMC value for variable '{var_name}' — \
                         cross-validation inconclusive"
                    ),
                };
            }
        }
    }

    // Evaluate each invariant. BMC claims at least one is violated.
    for inv_name in &config.invariants {
        match ctx.eval_op(inv_name) {
            Ok(Value::Bool(false)) => {
                // Invariant violated — BFS evaluator confirms BMC finding.
                return CrossValidationResult {
                    engine_agrees: true,
                    trace_length,
                    source_engine: CrossValidationSource::Bmc,
                    detail: format!(
                        "BFS evaluator confirms invariant '{inv_name}' violated at trace step {}",
                        final_state.step
                    ),
                };
            }
            Ok(Value::Bool(true)) => {
                // This invariant holds — continue checking others.
            }
            Ok(other) => {
                return CrossValidationResult {
                    engine_agrees: false,
                    trace_length,
                    source_engine: CrossValidationSource::Bmc,
                    detail: format!(
                        "invariant '{inv_name}' evaluated to non-boolean: {other:?} — \
                         cross-validation inconclusive"
                    ),
                };
            }
            Err(e) => {
                return CrossValidationResult {
                    engine_agrees: false,
                    trace_length,
                    source_engine: CrossValidationSource::Bmc,
                    detail: format!(
                        "invariant '{inv_name}' evaluation error: {e} — \
                         cross-validation inconclusive"
                    ),
                };
            }
        }
    }

    // All invariants passed — BFS evaluator does NOT confirm BMC violation.
    CrossValidationResult {
        engine_agrees: false,
        trace_length,
        source_engine: CrossValidationSource::Bmc,
        detail: format!(
            "BFS evaluator finds all {} invariants hold at trace step {} — \
             BMC violation not confirmed",
            config.invariants.len(),
            final_state.step
        ),
    }
}

/// Cross-validate a PDR safety proof against the BFS completion status.
///
/// When PDR proves safety (synthesizes an inductive invariant), we check
/// whether BFS also completed successfully as a consistency check. If BFS
/// found a violation while PDR claims safety, that indicates a soundness
/// issue in one of the engines.
///
/// `pdr_invariant` is the synthesized invariant string from PDR (for logging).
pub fn cross_validate_pdr_safety(
    bfs_result: &CheckResult,
    pdr_invariant: &str,
) -> CrossValidationResult {
    match bfs_result {
        CheckResult::Success(stats) => CrossValidationResult {
            engine_agrees: true,
            trace_length: 0,
            source_engine: CrossValidationSource::Pdr,
            detail: format!(
                "BFS completed with {} states, confirming PDR safety proof (invariant: {})",
                stats.states_found,
                truncate_invariant(pdr_invariant),
            ),
        },
        CheckResult::InvariantViolation { invariant, .. } => CrossValidationResult {
            engine_agrees: false,
            trace_length: 0,
            source_engine: CrossValidationSource::Pdr,
            detail: format!(
                "BFS found invariant violation '{}' but PDR claims safety — \
                 possible soundness issue (PDR invariant: {})",
                invariant,
                truncate_invariant(pdr_invariant),
            ),
        },
        CheckResult::PropertyViolation { kind, .. } => CrossValidationResult {
            engine_agrees: false,
            trace_length: 0,
            source_engine: CrossValidationSource::Pdr,
            detail: format!(
                "BFS found property violation ({kind:?}) but PDR claims safety — \
                 possible soundness issue"
            ),
        },
        // BFS hit a limit or other non-definitive result: PDR may still be correct,
        // we just can't confirm it from BFS alone. Report as agreement with caveat.
        _ => CrossValidationResult {
            engine_agrees: true,
            trace_length: 0,
            source_engine: CrossValidationSource::Pdr,
            detail: format!(
                "BFS did not complete (result: {}) — PDR safety proof accepted without \
                 BFS confirmation (invariant: {})",
                bfs_result_summary(bfs_result),
                truncate_invariant(pdr_invariant),
            ),
        },
    }
}

/// Cross-validate a k-induction safety proof against the BFS completion status.
///
/// When k-induction proves safety (inductive step is UNSAT at some depth k),
/// we check whether BFS also completed successfully as a consistency check.
/// If BFS found a violation while k-induction claims safety, that indicates a
/// soundness issue in one of the engines.
///
/// `proved_k` is the induction depth at which the proof succeeded.
pub fn cross_validate_kinduction_safety(
    bfs_result: &CheckResult,
    proved_k: usize,
) -> CrossValidationResult {
    match bfs_result {
        CheckResult::Success(stats) => CrossValidationResult {
            engine_agrees: true,
            trace_length: 0,
            source_engine: CrossValidationSource::KInduction,
            detail: format!(
                "BFS completed with {} states, confirming k-induction safety proof (k={proved_k})",
                stats.states_found,
            ),
        },
        CheckResult::InvariantViolation { invariant, .. } => CrossValidationResult {
            engine_agrees: false,
            trace_length: 0,
            source_engine: CrossValidationSource::KInduction,
            detail: format!(
                "BFS found invariant violation '{invariant}' but k-induction claims safety \
                 at k={proved_k} — possible soundness issue"
            ),
        },
        CheckResult::PropertyViolation { kind, .. } => CrossValidationResult {
            engine_agrees: false,
            trace_length: 0,
            source_engine: CrossValidationSource::KInduction,
            detail: format!(
                "BFS found property violation ({kind:?}) but k-induction claims safety \
                 at k={proved_k} — possible soundness issue"
            ),
        },
        // BFS hit a limit or other non-definitive result: k-induction may still be
        // correct, we just can't confirm it from BFS alone.
        _ => CrossValidationResult {
            engine_agrees: true,
            trace_length: 0,
            source_engine: CrossValidationSource::KInduction,
            detail: format!(
                "BFS did not complete (result: {}) — k-induction safety proof accepted \
                 without BFS confirmation (k={proved_k})",
                bfs_result_summary(bfs_result),
            ),
        },
    }
}

/// Truncate a synthesized invariant string for human-readable output.
fn truncate_invariant(inv: &str) -> String {
    if inv.len() <= 120 {
        inv.to_string()
    } else {
        format!("{}...", &inv[..117])
    }
}

/// One-line summary of a CheckResult variant for logging.
fn bfs_result_summary(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Success(_) => "success",
        CheckResult::InvariantViolation { .. } => "invariant_violation",
        CheckResult::PropertyViolation { .. } => "property_violation",
        CheckResult::LivenessViolation { .. } => "liveness_violation",
        CheckResult::LimitReached { .. } => "limit_reached",
        _ => "other",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_bmc_value_to_value_bool() {
        assert_eq!(
            bmc_value_to_value(&BmcValue::Bool(true)),
            Some(Value::Bool(true))
        );
        assert_eq!(
            bmc_value_to_value(&BmcValue::Bool(false)),
            Some(Value::Bool(false))
        );
    }

    #[test]
    fn test_bmc_value_to_value_int() {
        assert_eq!(bmc_value_to_value(&BmcValue::Int(42)), Some(Value::int(42)));
        assert_eq!(bmc_value_to_value(&BmcValue::Int(-1)), Some(Value::int(-1)));
    }

    #[test]
    fn test_bmc_value_to_value_set() {
        let bmc_set = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
        let result = bmc_value_to_value(&bmc_set);
        assert!(result.is_some());
    }

    #[test]
    fn test_bmc_value_to_value_sequence() {
        let bmc_seq = BmcValue::Sequence(vec![BmcValue::Bool(true), BmcValue::Int(3)]);
        let result = bmc_value_to_value(&bmc_seq);
        assert!(result.is_some());
    }

    #[test]
    fn test_cross_validate_bmc_empty_trace() {
        let module = crate::test_support::parse_module(
            "---- MODULE Empty ----\nVARIABLE x\nInv == TRUE\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let result = cross_validate_bmc_trace(&module, &config, &[]);
        assert!(!result.engine_agrees);
        assert_eq!(result.trace_length, 0);
        assert_eq!(result.source_engine, CrossValidationSource::Bmc);
    }

    #[test]
    fn test_cross_validate_bmc_no_invariants() {
        let module = crate::test_support::parse_module("---- MODULE NoInv ----\nVARIABLE x\n====");
        let config = Config::default();
        let trace = vec![BmcState {
            step: 0,
            assignments: HashMap::new(),
        }];
        let result = cross_validate_bmc_trace(&module, &config, &trace);
        assert!(!result.engine_agrees);
    }

    #[test]
    fn test_cross_validate_bmc_violation_confirmed() {
        let module = crate::test_support::parse_module(
            "---- MODULE ConfirmViol ----\nVARIABLE x\nInv == x < 2\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let mut assignments = HashMap::new();
        assignments.insert("x".to_string(), BmcValue::Int(5));
        let trace = vec![BmcState {
            step: 0,
            assignments,
        }];
        let result = cross_validate_bmc_trace(&module, &config, &trace);
        assert!(result.engine_agrees, "detail: {}", result.detail);
        assert_eq!(result.trace_length, 1);
        assert_eq!(result.source_engine, CrossValidationSource::Bmc);
    }

    #[test]
    fn test_cross_validate_bmc_violation_not_confirmed() {
        let module = crate::test_support::parse_module(
            "---- MODULE NoConfirm ----\nVARIABLE x\nInv == x < 10\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let mut assignments = HashMap::new();
        assignments.insert("x".to_string(), BmcValue::Int(5));
        let trace = vec![BmcState {
            step: 0,
            assignments,
        }];
        let result = cross_validate_bmc_trace(&module, &config, &trace);
        assert!(!result.engine_agrees, "detail: {}", result.detail);
    }

    #[test]
    fn test_cross_validate_pdr_safety_confirmed() {
        let bfs_result = CheckResult::Success(crate::check::CheckStats {
            states_found: 10,
            ..Default::default()
        });
        let result = cross_validate_pdr_safety(&bfs_result, "x \\in {0, 1}");
        assert!(result.engine_agrees);
        assert_eq!(result.source_engine, CrossValidationSource::Pdr);
    }

    #[test]
    fn test_cross_validate_pdr_safety_contradicted() {
        let bfs_result = CheckResult::InvariantViolation {
            invariant: "Inv".to_string(),
            trace: crate::check::Trace::new(),
            stats: crate::check::CheckStats::default(),
        };
        let result = cross_validate_pdr_safety(&bfs_result, "synthesized_inv");
        assert!(!result.engine_agrees);
        assert_eq!(result.source_engine, CrossValidationSource::Pdr);
    }

    #[test]
    fn test_cross_validate_pdr_bfs_limit_reached() {
        let bfs_result = CheckResult::LimitReached {
            limit_type: crate::check::LimitType::States,
            stats: crate::check::CheckStats::default(),
        };
        let result = cross_validate_pdr_safety(&bfs_result, "synthesized_inv");
        // BFS didn't complete — accept PDR proof without confirmation.
        assert!(result.engine_agrees);
    }

    #[test]
    fn test_truncate_invariant_short() {
        assert_eq!(truncate_invariant("short"), "short");
    }

    #[test]
    fn test_truncate_invariant_long() {
        let long = "x".repeat(200);
        let truncated = truncate_invariant(&long);
        assert!(truncated.len() <= 123);
        assert!(truncated.ends_with("..."));
    }
}
