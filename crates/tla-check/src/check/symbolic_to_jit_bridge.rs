// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge between symbolic BMC counterexample traces and JIT-compiled invariant evaluation.
//!
//! When the BMC symbolic engine finds a counterexample trace, this module converts
//! the individual states to the JIT state layout and evaluates invariants using
//! JIT-compiled native code. If JIT is not available (feature-gated or the invariant
//! is not JIT-compilable), evaluation falls back to the interpreter.
//!
//! This closes the loop between symbolic and concrete execution in the fused
//! cooperative orchestrator (CDEMC).
//!
//! Part of #3855 (FJ3: Symbolic Engine Provides Counterexample States to JIT).

use std::sync::Arc;

use tla_core::ast::Module;
use tla_z4::{BmcState, BmcValue};

use crate::check::cross_validation::bmc_value_to_value;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::value::Value;

/// Which evaluation method was used for a particular invariant check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvalMethod {
    /// Interpreter (tree-walk evaluator) evaluated the invariant.
    Interpreter,
}

/// Result of verifying invariants across an entire BMC counterexample trace.
#[derive(Debug, Clone)]
pub(crate) struct TraceVerificationResult {
    /// Whether any invariant was violated on any state in the trace.
    pub(crate) violation_found: bool,
    /// Name of the violated invariant, if any.
    pub(crate) violated_invariant: Option<String>,
    /// Step number where the violation was found (0-indexed).
    pub(crate) violation_step: Option<usize>,
    /// Evaluation method used for the verification.
    pub(crate) eval_method: EvalMethod,
    /// Number of states in the trace that were checked.
    pub(crate) states_checked: usize,
    /// Human-readable detail about the verification outcome.
    pub(crate) detail: String,
}

/// Bridge that converts BMC counterexample states to the JIT layout and
/// evaluates invariants using JIT-compiled code when available.
///
/// The bridge operates in two modes:
/// 1. **JIT mode**: Flattens `BmcState` to `&[i64]` and calls JIT-compiled invariant
///    functions. Only works for scalar (Bool/Int) state variables.
/// 2. **Interpreter fallback**: Converts `BmcValue` to `Value` via the existing
///    `bmc_value_to_value` conversion and evaluates through the tree-walk interpreter.
///
/// Part of #3855.
pub(crate) struct SymbolicToJitBridge<'a> {
    module: &'a Module,
    config: &'a Config,
    /// Ordered variable names matching the JIT state array layout.
    /// Derived from the module's VARIABLE declarations.
    var_names: Vec<String>,
}

impl<'a> SymbolicToJitBridge<'a> {
    /// Create a new bridge for the given module and config.
    ///
    /// If the `jit` feature is enabled, this attempts to build a JIT invariant cache
    /// for the configured invariants. If JIT compilation fails, the bridge still works
    /// but will always use the interpreter fallback.
    pub(crate) fn new(module: &'a Module, config: &'a Config) -> Self {
        let var_names = extract_variable_names(module);

        Self {
            module,
            config,
            var_names,
        }
    }

    /// Verify invariants across the entire BMC counterexample trace.
    ///
    /// Checks each configured invariant on the final state of the trace (where
    /// the BMC engine claims a violation exists). Returns as soon as a violation
    /// is confirmed.
    pub(crate) fn verify_trace(&self, trace: &[BmcState]) -> TraceVerificationResult {
        if trace.is_empty() {
            return TraceVerificationResult {
                violation_found: false,
                violated_invariant: None,
                violation_step: None,
                eval_method: EvalMethod::Interpreter,
                states_checked: 0,
                detail: "BMC trace is empty — nothing to verify".to_string(),
            };
        }

        if self.config.invariants.is_empty() {
            return TraceVerificationResult {
                violation_found: false,
                violated_invariant: None,
                violation_step: None,
                eval_method: EvalMethod::Interpreter,
                states_checked: 0,
                detail: "no invariants configured".to_string(),
            };
        }

        // BMC finds the violation at the final state in the trace.
        let final_state = &trace[trace.len() - 1];

        // Interpreter path (Cranelift JIT invariant cache removed — #4266).
        self.verify_state_interpreter(final_state)
    }

    /// Verify invariants on all states in the trace (not just the final one).
    ///
    /// Useful for trace visualization and debugging: confirms invariant status
    /// at each step. Returns results for every state.
    pub(crate) fn verify_all_states(&self, trace: &[BmcState]) -> Vec<TraceVerificationResult> {
        trace
            .iter()
            .map(|state| self.verify_state_interpreter(state))
            .collect()
    }

    /// Flatten a BMC state to the i64 layout expected by JIT invariant functions.
    ///
    /// The JIT state array is ordered by variable name (matching `var_names`).
    /// Returns `None` if any variable has a compound type (set, sequence, function)
    /// or if a variable from the state is not in the registry.
    fn flatten_bmc_state(&self, state: &BmcState) -> Option<Vec<i64>> {
        let mut flat = Vec::with_capacity(self.var_names.len());
        for name in &self.var_names {
            let bmc_val = state.assignments.get(name)?;
            match bmc_val {
                BmcValue::Bool(b) => flat.push(if *b { 1i64 } else { 0i64 }),
                BmcValue::Int(n) => flat.push(*n),
                BmcValue::BigInt(n) => {
                    use num_traits::ToPrimitive;
                    flat.push(n.to_i64()?);
                }
                // Compound types cannot be flattened to i64 — JIT path ineligible.
                BmcValue::Set(_)
                | BmcValue::Sequence(_)
                | BmcValue::Function(_)
                | BmcValue::Record(_)
                | BmcValue::Tuple(_) => {
                    return None;
                }
            }
        }
        Some(flat)
    }

    /// Interpreter-based invariant verification for a single BMC state.
    ///
    /// Converts BmcValue assignments to Values, binds them in an EvalCtx,
    /// and evaluates each configured invariant.
    fn verify_state_interpreter(&self, state: &BmcState) -> TraceVerificationResult {
        let mut ctx = EvalCtx::new();
        ctx.load_module(self.module);

        // Bind state variables.
        for (var_name, bmc_val) in &state.assignments {
            match bmc_value_to_value(bmc_val) {
                Some(value) => {
                    ctx.env_mut().insert(Arc::from(var_name.as_str()), value);
                }
                None => {
                    return TraceVerificationResult {
                        violation_found: false,
                        violated_invariant: None,
                        violation_step: None,
                        eval_method: EvalMethod::Interpreter,
                        states_checked: 1,
                        detail: format!(
                            "cannot convert BMC value for variable '{}' — \
                             verification inconclusive",
                            var_name,
                        ),
                    };
                }
            }
        }

        // Evaluate each invariant.
        for inv_name in &self.config.invariants {
            match ctx.eval_op(inv_name) {
                Ok(Value::Bool(false)) => {
                    return TraceVerificationResult {
                        violation_found: true,
                        violated_invariant: Some(inv_name.clone()),
                        violation_step: Some(state.step),
                        eval_method: EvalMethod::Interpreter,
                        states_checked: 1,
                        detail: format!(
                            "interpreter confirms invariant '{}' violated at trace step {}",
                            inv_name, state.step,
                        ),
                    };
                }
                Ok(Value::Bool(true)) => {
                    // Invariant holds — continue.
                }
                Ok(other) => {
                    return TraceVerificationResult {
                        violation_found: false,
                        violated_invariant: None,
                        violation_step: None,
                        eval_method: EvalMethod::Interpreter,
                        states_checked: 1,
                        detail: format!(
                            "invariant '{}' evaluated to non-boolean: {:?}",
                            inv_name, other,
                        ),
                    };
                }
                Err(e) => {
                    return TraceVerificationResult {
                        violation_found: false,
                        violated_invariant: None,
                        violation_step: None,
                        eval_method: EvalMethod::Interpreter,
                        states_checked: 1,
                        detail: format!("invariant '{}' evaluation error: {}", inv_name, e,),
                    };
                }
            }
        }

        // All invariants hold.
        TraceVerificationResult {
            violation_found: false,
            violated_invariant: None,
            violation_step: None,
            eval_method: EvalMethod::Interpreter,
            states_checked: 1,
            detail: format!(
                "interpreter: all {} invariants hold at step {}",
                self.config.invariants.len(),
                state.step,
            ),
        }
    }
}

/// Extract VARIABLE names from a module in declaration order.
///
/// This order must match the JIT state array layout (which uses VarRegistry ordering,
/// which itself follows declaration order).
fn extract_variable_names(module: &Module) -> Vec<String> {
    use tla_core::ast::Unit;

    let mut names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                names.push(var.node.clone());
            }
        }
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn make_bmc_state(step: usize, assignments: Vec<(&str, BmcValue)>) -> BmcState {
        BmcState {
            step,
            assignments: assignments
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
        }
    }

    #[test]
    fn test_flatten_bmc_state_scalar() {
        let module = crate::test_support::parse_module(
            "---- MODULE FlattenScalar ----\nVARIABLE x, y\n====",
        );
        let config = Config::default();
        let bridge = SymbolicToJitBridge::new(&module, &config);

        let state = make_bmc_state(
            0,
            vec![("x", BmcValue::Int(42)), ("y", BmcValue::Bool(true))],
        );
        let flat = bridge.flatten_bmc_state(&state);
        assert!(flat.is_some(), "scalar state should flatten");
        let flat = flat.unwrap();
        assert_eq!(flat.len(), 2);
        // x=42, y=1 (true)
        assert_eq!(flat[0], 42);
        assert_eq!(flat[1], 1);
    }

    #[test]
    fn test_flatten_bmc_state_compound_returns_none() {
        let module = crate::test_support::parse_module(
            "---- MODULE FlattenCompound ----\nVARIABLE x, y\n====",
        );
        let config = Config::default();
        let bridge = SymbolicToJitBridge::new(&module, &config);

        let state = make_bmc_state(
            0,
            vec![
                ("x", BmcValue::Int(1)),
                ("y", BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)])),
            ],
        );
        let flat = bridge.flatten_bmc_state(&state);
        assert!(flat.is_none(), "compound type should not flatten");
    }

    #[test]
    fn test_flatten_bmc_state_missing_var_returns_none() {
        let module = crate::test_support::parse_module(
            "---- MODULE FlattenMissing ----\nVARIABLE x, y\n====",
        );
        let config = Config::default();
        let bridge = SymbolicToJitBridge::new(&module, &config);

        // Only provide x, not y.
        let state = make_bmc_state(0, vec![("x", BmcValue::Int(1))]);
        let flat = bridge.flatten_bmc_state(&state);
        assert!(flat.is_none(), "missing variable should not flatten");
    }

    #[test]
    fn test_verify_trace_empty() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifyEmpty ----\nVARIABLE x\nInv == TRUE\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let result = bridge.verify_trace(&[]);
        assert!(!result.violation_found);
        assert_eq!(result.states_checked, 0);
    }

    #[test]
    fn test_verify_trace_no_invariants() {
        let module =
            crate::test_support::parse_module("---- MODULE VerifyNoInv ----\nVARIABLE x\n====");
        let config = Config::default();
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![make_bmc_state(0, vec![("x", BmcValue::Int(1))])];
        let result = bridge.verify_trace(&trace);
        assert!(!result.violation_found);
        assert_eq!(result.states_checked, 0);
    }

    #[test]
    fn test_verify_trace_violation_confirmed_interpreter() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifyViol ----\nVARIABLE x\nInv == x < 2\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![make_bmc_state(0, vec![("x", BmcValue::Int(5))])];
        let result = bridge.verify_trace(&trace);
        assert!(result.violation_found, "detail: {}", result.detail);
        assert_eq!(result.violated_invariant.as_deref(), Some("Inv"));
        assert_eq!(result.violation_step, Some(0));
    }

    #[test]
    fn test_verify_trace_no_violation_interpreter() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifyOk ----\nVARIABLE x\nInv == x < 10\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![make_bmc_state(0, vec![("x", BmcValue::Int(5))])];
        let result = bridge.verify_trace(&trace);
        assert!(!result.violation_found, "detail: {}", result.detail);
    }

    #[test]
    fn test_verify_all_states_multi_step() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifyMulti ----\nVARIABLE x\nInv == x < 3\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![
            make_bmc_state(0, vec![("x", BmcValue::Int(0))]),
            make_bmc_state(1, vec![("x", BmcValue::Int(1))]),
            make_bmc_state(2, vec![("x", BmcValue::Int(5))]),
        ];
        let results = bridge.verify_all_states(&trace);
        assert_eq!(results.len(), 3);
        assert!(!results[0].violation_found, "step 0 should hold");
        assert!(!results[1].violation_found, "step 1 should hold");
        assert!(results[2].violation_found, "step 2 should violate");
        assert_eq!(results[2].violated_invariant.as_deref(), Some("Inv"));
    }

    #[test]
    fn test_extract_variable_names() {
        let module = crate::test_support::parse_module(
            "---- MODULE ExtractVars ----\nVARIABLE a, b, c\n====",
        );
        let names = extract_variable_names(&module);
        assert_eq!(names, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_verify_trace_bigint_state() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifyBigInt ----\nVARIABLE x\nInv == x < 100\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![make_bmc_state(
            0,
            vec![("x", BmcValue::BigInt(num_bigint::BigInt::from(200)))],
        )];
        let result = bridge.verify_trace(&trace);
        assert!(result.violation_found, "detail: {}", result.detail);
        assert_eq!(result.violated_invariant.as_deref(), Some("Inv"));
    }

    #[test]
    fn test_verify_trace_sequence_state_falls_back_to_interpreter() {
        let module = crate::test_support::parse_module(
            "---- MODULE VerifySeq ----\nVARIABLE x\nInv == TRUE\n====",
        );
        let config = Config {
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        let bridge = SymbolicToJitBridge::new(&module, &config);
        let trace = vec![make_bmc_state(
            0,
            vec![("x", BmcValue::Sequence(vec![BmcValue::Int(1)]))],
        )];
        let result = bridge.verify_trace(&trace);
        // Should fall back to interpreter and succeed (Inv == TRUE).
        assert!(!result.violation_found, "detail: {}", result.detail);
        assert_eq!(result.eval_method, EvalMethod::Interpreter);
    }
}
