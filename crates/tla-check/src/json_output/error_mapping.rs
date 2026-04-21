// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error code mapping and suggestion generation from CheckError.

use super::diagnostics::error_codes;
use super::types::ErrorSuggestion;
use crate::{
    CheckError, ConfigCheckError, EvalCheckError, InfraCheckError, LivenessCheckError,
    RuntimeCheckError,
};

/// Map CheckError to a structured error code
pub(super) fn error_code_from_check_error(error: &CheckError) -> String {
    match error {
        CheckError::Config(ConfigCheckError::Setup(_)) => error_codes::SYS_SETUP_ERROR.to_string(),
        CheckError::Config(ConfigCheckError::MissingInit) => {
            error_codes::CFG_MISSING_INIT.to_string()
        }
        CheckError::Config(ConfigCheckError::MissingNext) => {
            error_codes::CFG_MISSING_NEXT.to_string()
        }
        CheckError::Config(ConfigCheckError::MissingInvariant(_)) => {
            error_codes::TLC_UNDEFINED_OP.to_string()
        }
        CheckError::Config(ConfigCheckError::MissingProperty(_)) => {
            error_codes::TLC_UNDEFINED_OP.to_string()
        }
        CheckError::Eval(EvalCheckError::Eval(_)) => error_codes::TLC_EVAL_ERROR.to_string(),
        CheckError::Eval(EvalCheckError::InitNotBoolean) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Eval(EvalCheckError::NextNotBoolean) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Eval(EvalCheckError::InvariantNotBoolean(_)) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Eval(EvalCheckError::ConstraintNotBoolean(_)) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Eval(EvalCheckError::PropertyNotBoolean(_)) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Config(ConfigCheckError::NoVariables) => {
            error_codes::TLC_EVAL_ERROR.to_string()
        }
        CheckError::Config(ConfigCheckError::InitCannotEnumerate(_)) => {
            error_codes::TLC_EVAL_ERROR.to_string()
        }
        CheckError::Config(ConfigCheckError::Specification(_)) => {
            error_codes::CFG_PARSE_ERROR.to_string()
        }
        CheckError::Config(ConfigCheckError::Config(_)) => error_codes::CFG_PARSE_ERROR.to_string(),
        CheckError::Liveness(LivenessCheckError::CannotHandleFormula { .. }) => {
            error_codes::TLC_LIVE_CANNOT_HANDLE_FORMULA.to_string()
        }
        CheckError::Liveness(LivenessCheckError::FormulaTautology { .. }) => {
            error_codes::TLC_LIVE_FORMULA_TAUTOLOGY.to_string()
        }
        CheckError::Liveness(LivenessCheckError::Generic(_)) => {
            error_codes::SYS_LIVENESS_ERROR.to_string()
        }
        CheckError::Liveness(LivenessCheckError::RuntimeFailure(_)) => {
            error_codes::SYS_LIVENESS_RUNTIME_FAILURE.to_string()
        }
        CheckError::Infra(InfraCheckError::FingerprintOverflow { .. }) => {
            error_codes::TLC_LIMIT_REACHED.to_string()
        }
        CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. }) => {
            error_codes::TLC_EVAL_ERROR.to_string()
        }
        CheckError::Runtime(RuntimeCheckError::PostconditionFalse { .. }) => {
            error_codes::TLC_EVAL_ERROR.to_string()
        }
        CheckError::Runtime(RuntimeCheckError::ViewEvalError { .. }) => {
            error_codes::TLC_EVAL_ERROR.to_string()
        }
        CheckError::Infra(InfraCheckError::WorkerThreadPanicked { .. }) => {
            error_codes::SYS_SETUP_ERROR.to_string()
        }
        CheckError::Infra(InfraCheckError::ProgressThreadPanicked { .. }) => {
            error_codes::SYS_SETUP_ERROR.to_string()
        }
        CheckError::Config(ConfigCheckError::OpRequiresNoArgs { .. }) => {
            error_codes::CFG_PARSE_ERROR.to_string()
        }
        CheckError::Config(ConfigCheckError::InvariantNotStateLevel { .. }) => {
            error_codes::TLC_TYPE_MISMATCH.to_string()
        }
        CheckError::Runtime(RuntimeCheckError::Internal(_)) => {
            error_codes::SYS_SETUP_ERROR.to_string()
        }
    }
}

/// Generate actionable suggestion from CheckError
pub(super) fn suggestion_from_check_error(error: &CheckError) -> Option<ErrorSuggestion> {
    match error {
        CheckError::Config(ConfigCheckError::Setup(_message)) => {
            Some(ErrorSuggestion {
                action: "Provide the missing modules to the model checker and retry"
                    .to_string(),
                example: Some(
                    "If using the embedding API: ensure you pass all referenced non-stdlib modules (EXTENDS + INSTANCE closure) to ModelChecker::new_with_extends"
                        .to_string(),
                ),
                options: vec![
                    "If using the CLI: this is likely a tool bug (missing module loader output)"
                        .to_string(),
                ],
            })
        }
        CheckError::Config(ConfigCheckError::MissingInit) => Some(ErrorSuggestion {
            action: "Define an Init predicate in the spec and reference it in the config"
                .to_string(),
            example: Some("INIT Init\n\nIn spec: Init == x = 0".to_string()),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::MissingNext) => Some(ErrorSuggestion {
            action: "Define a Next action in the spec and reference it in the config".to_string(),
            example: Some("NEXT Next\n\nIn spec: Next == x' = x + 1".to_string()),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::Config(_)) => Some(ErrorSuggestion {
            action: "Fix the configuration error and retry".to_string(),
            example: Some(
                "For module-scoped overrides like `CONSTANT Foo <- [Mod] Bar`, verify `Mod` is loaded and `Foo` exists in that module"
                    .to_string(),
            ),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::MissingInvariant(name)) => Some(ErrorSuggestion {
            action: format!("Define the invariant '{name}' in the spec"),
            example: Some(format!("{name} == x >= 0")),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::MissingProperty(name)) => Some(ErrorSuggestion {
            action: format!("Define the property '{name}' in the spec"),
            example: Some(format!("{name} == <>[] done")),
            options: vec![],
        }),
        CheckError::Eval(EvalCheckError::Eval(e)) => {
            let (action, example) = match e {
                crate::error::EvalError::UndefinedVar { name, .. } => (
                    format!("Variable '{name}' is not defined"),
                    Some(format!("Ensure '{name}' is declared: VARIABLE {name}")),
                ),
                crate::error::EvalError::UndefinedOp { name, .. } => (
                    format!("Operator '{name}' is not defined"),
                    Some(format!(
                        "Define '{name}' in spec or EXTENDS a module that defines it"
                    )),
                ),
                crate::error::EvalError::TypeError { expected, got, .. } => (
                    format!("Type error: expected {expected}, got {got}"),
                    None,
                ),
                crate::error::EvalError::DivisionByZero { .. } => (
                    "Division by zero occurred".to_string(),
                    Some("Check that the divisor is never zero".to_string()),
                ),
                crate::error::EvalError::ChooseFailed { .. } => (
                    "CHOOSE found no satisfying value".to_string(),
                    Some(
                        "Ensure the set is non-empty and the predicate can be satisfied"
                            .to_string(),
                    ),
                ),
                _ => (
                    "Check the error details for more information".to_string(),
                    None,
                ),
            };
            Some(ErrorSuggestion {
                action,
                example,
                options: vec![],
            })
        }
        CheckError::Eval(EvalCheckError::InitNotBoolean) => Some(ErrorSuggestion {
            action: "Init predicate must return a boolean value".to_string(),
            example: Some("Init == x = 0 /\\ y = 0".to_string()),
            options: vec![],
        }),
        CheckError::Eval(EvalCheckError::NextNotBoolean) => Some(ErrorSuggestion {
            action: "Next relation must return a boolean value".to_string(),
            example: Some("Next == x' = x + 1".to_string()),
            options: vec![],
        }),
        CheckError::Eval(EvalCheckError::InvariantNotBoolean(name)) => Some(ErrorSuggestion {
            action: format!("Invariant '{name}' must return a boolean value"),
            example: Some(format!("{name} == x >= 0")),
            options: vec![],
        }),
        CheckError::Eval(EvalCheckError::ConstraintNotBoolean(name)) => Some(ErrorSuggestion {
            action: format!("Constraint '{name}' must return a boolean value"),
            example: Some(format!("{name} == x >= 0")),
            options: vec![],
        }),
        CheckError::Eval(EvalCheckError::PropertyNotBoolean(name)) => Some(ErrorSuggestion {
            action: format!("Property '{name}' must return a boolean value"),
            example: Some(format!("{name} == <>[] done")),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::NoVariables) => Some(ErrorSuggestion {
            action: "Spec must declare at least one variable".to_string(),
            example: Some("VARIABLE x, y".to_string()),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::InitCannotEnumerate(reason)) => Some(ErrorSuggestion {
            action: "Init predicate cannot be enumerated for initial states".to_string(),
            example: Some(format!(
                "Reason: {reason}\n\nUse explicit enumeration: x \\in {{0, 1, 2}}"
            )),
            options: vec![
                "Use set membership: x \\in {1, 2, 3}".to_string(),
                "Use range: x \\in 1..10".to_string(),
            ],
        }),
        CheckError::Config(ConfigCheckError::Specification(msg)) => Some(ErrorSuggestion {
            action: "Fix the SPECIFICATION formula".to_string(),
            example: Some(msg.clone()),
            options: vec![],
        }),
        CheckError::Liveness(LivenessCheckError::CannotHandleFormula { location, reason }) => Some(ErrorSuggestion {
            action: "Rewrite the liveness property to avoid non-enumerable bounded quantifiers"
                .to_string(),
            example: Some(
                crate::check::TlcLiveCannotHandleFormulaMsg {
                    location,
                    reason: reason.as_deref(),
                }
                .to_string(),
            ),
            options: vec![
                "Use finite sets (or constrain domains to be finite)".to_string(),
                "Move quantifiers outside temporal operators when possible".to_string(),
                "Replace bounded quantification with an equivalent finite enumeration".to_string(),
            ],
        }),
        CheckError::Liveness(LivenessCheckError::FormulaTautology { property }) => Some(ErrorSuggestion {
            action: format!(
                "Temporal property '{property}' is a tautology and will never be violated"
            ),
            example: Some(
                "Common causes: []TRUE, <>TRUE, or a temporal formula that simplifies to TRUE"
                    .to_string(),
            ),
            options: vec![
                "Check the property definition for mistakes".to_string(),
                "Ensure the property actually constrains system behavior".to_string(),
            ],
        }),
        CheckError::Liveness(LivenessCheckError::Generic(msg)) => Some(ErrorSuggestion {
            action: "Liveness checking could not complete".to_string(),
            example: Some(msg.clone()),
            options: vec![
                "Simplify the temporal property formula".to_string(),
                "Check if the property can be expressed in a supported pattern".to_string(),
            ],
        }),
        CheckError::Liveness(LivenessCheckError::RuntimeFailure(msg)) => Some(ErrorSuggestion {
            action: "Liveness checker encountered an internal runtime failure".to_string(),
            example: Some(msg.clone()),
            options: vec![
                "This indicates a bug in the liveness checker. Please file a bug report.".to_string(),
                "Retry with a simpler spec to narrow the triggering condition".to_string(),
            ],
        }),
        CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }) => Some(ErrorSuggestion {
            action: format!(
                "Fingerprint storage overflowed, {dropped} states were dropped"
            ),
            example: Some(
                "Increase --mmap-fingerprints capacity or reduce state space".to_string(),
            ),
            options: vec![
                "Use larger --mmap-fingerprints value".to_string(),
                "Add CONSTRAINT to reduce state space".to_string(),
                "Use symmetry reduction".to_string(),
            ],
        }),
        CheckError::Runtime(RuntimeCheckError::AssumeFalse { location }) => Some(ErrorSuggestion {
            action: format!("ASSUME statement {location} evaluated to FALSE"),
            example: Some("Check that all ASSUME prerequisites are satisfied".to_string()),
            options: vec![
                "Verify ASSUME conditions match your model configuration".to_string(),
                "Remove or modify the failing ASSUME statement".to_string(),
            ],
        }),
        CheckError::Runtime(RuntimeCheckError::PostconditionFalse { operator }) => Some(ErrorSuggestion {
            action: format!("POSTCONDITION operator {operator} evaluated to FALSE"),
            example: Some("Check that postcondition requirements are satisfied after model checking completes".to_string()),
            options: vec![
                "Verify your postcondition logic is correct".to_string(),
                "Check that the spec's state space satisfies the postcondition".to_string(),
            ],
        }),
        CheckError::Runtime(RuntimeCheckError::ViewEvalError { view_name, eval_error }) => Some(ErrorSuggestion {
            action: format!("VIEW operator '{view_name}' evaluation failed: {eval_error}"),
            example: Some("Ensure the VIEW expression can be evaluated for all reachable states".to_string()),
            options: vec![
                "Check that all operators referenced in VIEW are defined".to_string(),
                "Verify VIEW expression handles all possible state variable values".to_string(),
            ],
        }),
        CheckError::Infra(InfraCheckError::WorkerThreadPanicked { worker_id, message }) => Some(ErrorSuggestion {
            action: format!(
                "Worker thread {worker_id} panicked during model checking: {message}"
            ),
            example: Some("Retry with --workers=1 to isolate the failure path".to_string()),
            options: vec![
                "Capture the full panic output and file a bug".to_string(),
                "Reduce model complexity to narrow the triggering state".to_string(),
            ],
        }),
        CheckError::Infra(InfraCheckError::ProgressThreadPanicked { message }) => Some(ErrorSuggestion {
            action: format!("Progress reporting thread panicked: {message}"),
            example: Some(
                "If using a progress callback in embedding mode, ensure it does not panic"
                    .to_string(),
            ),
            options: vec![
                "Retry without progress callback to confirm the checker core is stable".to_string(),
                "File a bug if the panic occurs without a custom callback".to_string(),
            ],
        }),
        CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
            op_name, kind, arity,
        }) => Some(ErrorSuggestion {
            action: format!(
                "{kind} operator '{op_name}' has {arity} parameter(s) but must take zero"
            ),
            example: Some(format!(
                "Define '{op_name}' without parameters: {op_name} == <expr>"
            )),
            options: vec![],
        }),
        CheckError::Config(ConfigCheckError::InvariantNotStateLevel {
            name,
            has_prime,
            has_temporal,
        }) => {
            let issue = match (has_prime, has_temporal) {
                (true, true) => "primed variables and temporal operators",
                (true, false) => "primed variables",
                (false, true) => "temporal operators",
                (false, false) => "non-state-level operators",
            };
            Some(ErrorSuggestion {
                action: format!(
                    "Invariant '{name}' contains {issue} and cannot be checked at state level"
                ),
                example: Some(
                    "Invariants must be state-level predicates evaluable on a single state"
                        .to_string(),
                ),
                options: vec![
                    "If using primed variables: use ACTION_CONSTRAINT instead of INVARIANT"
                        .to_string(),
                    "If using temporal operators: use PROPERTY instead of INVARIANT".to_string(),
                ],
            })
        }
        CheckError::Runtime(RuntimeCheckError::Internal(msg)) => Some(ErrorSuggestion {
            action: format!("Internal model checker error: {msg}"),
            example: Some("This indicates a bug in the model checker. Please file a bug report.".to_string()),
            options: vec![
                "Retry with a simpler spec to narrow the triggering condition".to_string(),
                "Check if a newer version fixes this issue".to_string(),
            ],
        }),
    }
}
