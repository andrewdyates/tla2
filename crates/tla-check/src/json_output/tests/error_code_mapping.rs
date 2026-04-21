// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for exhaustive error code mapping and guard suppression warnings.

use super::*;
use crate::{
    ConfigCheckError, EvalCheckError, InfraCheckError, LivenessCheckError, RuntimeCheckError,
};

/// Exhaustive error code mapping test: every CheckError variant maps to the correct code.
/// Supersedes the former test_error_codes (tautological) and
/// test_liveness_error_maps_to_sys_liveness_error_not_violated (single-variant subset).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_code_from_check_error_exhaustive() {
    use super::super::error_mapping::error_code_from_check_error;
    use crate::CheckError;

    let te = || crate::EvalError::TypeError {
        expected: "bool",
        got: "int",
        span: None,
    };
    let s = |s: &str| s.to_string();

    // (CheckError variant, expected code) — all variants
    let cases: Vec<(CheckError, &str)> = vec![
        (
            ConfigCheckError::Setup(s("t")).into(),
            error_codes::SYS_SETUP_ERROR,
        ),
        (
            ConfigCheckError::MissingInit.into(),
            error_codes::CFG_MISSING_INIT,
        ),
        (
            ConfigCheckError::MissingNext.into(),
            error_codes::CFG_MISSING_NEXT,
        ),
        (
            ConfigCheckError::MissingInvariant(s("I")).into(),
            error_codes::TLC_UNDEFINED_OP,
        ),
        (
            ConfigCheckError::MissingProperty(s("P")).into(),
            error_codes::TLC_UNDEFINED_OP,
        ),
        (
            EvalCheckError::Eval(te()).into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            EvalCheckError::InitNotBoolean.into(),
            error_codes::TLC_TYPE_MISMATCH,
        ),
        (
            EvalCheckError::NextNotBoolean.into(),
            error_codes::TLC_TYPE_MISMATCH,
        ),
        (
            EvalCheckError::InvariantNotBoolean(s("I")).into(),
            error_codes::TLC_TYPE_MISMATCH,
        ),
        (
            EvalCheckError::ConstraintNotBoolean(s("C")).into(),
            error_codes::TLC_TYPE_MISMATCH,
        ),
        (
            EvalCheckError::PropertyNotBoolean(s("P")).into(),
            error_codes::TLC_TYPE_MISMATCH,
        ),
        (
            ConfigCheckError::NoVariables.into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            ConfigCheckError::InitCannotEnumerate(s("r")).into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            ConfigCheckError::Specification(s("s")).into(),
            error_codes::CFG_PARSE_ERROR,
        ),
        (
            ConfigCheckError::Config(s("c")).into(),
            error_codes::CFG_PARSE_ERROR,
        ),
        (
            LivenessCheckError::CannotHandleFormula {
                location: s("l"),
                reason: None,
            }
            .into(),
            error_codes::TLC_LIVE_CANNOT_HANDLE_FORMULA,
        ),
        (
            LivenessCheckError::Generic(s("t")).into(),
            error_codes::SYS_LIVENESS_ERROR,
        ),
        (
            LivenessCheckError::RuntimeFailure(s("t")).into(),
            error_codes::SYS_LIVENESS_RUNTIME_FAILURE,
        ),
        (
            LivenessCheckError::FormulaTautology { property: s("P") }.into(),
            error_codes::TLC_LIVE_FORMULA_TAUTOLOGY,
        ),
        (
            InfraCheckError::FingerprintOverflow {
                dropped: 1,
                detail: String::new(),
            }
            .into(),
            error_codes::TLC_LIMIT_REACHED,
        ),
        (
            RuntimeCheckError::AssumeFalse { location: s("l") }.into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            RuntimeCheckError::PostconditionFalse { operator: s("O") }.into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            RuntimeCheckError::ViewEvalError {
                view_name: s("V"),
                eval_error: te(),
            }
            .into(),
            error_codes::TLC_EVAL_ERROR,
        ),
        (
            InfraCheckError::WorkerThreadPanicked {
                worker_id: 0,
                message: s("p"),
            }
            .into(),
            error_codes::SYS_SETUP_ERROR,
        ),
        (
            InfraCheckError::ProgressThreadPanicked { message: s("p") }.into(),
            error_codes::SYS_SETUP_ERROR,
        ),
        (
            RuntimeCheckError::Internal(s("b")).into(),
            error_codes::SYS_SETUP_ERROR,
        ),
    ];

    let violations = [
        error_codes::TLC_DEADLOCK,
        error_codes::TLC_INVARIANT_VIOLATED,
        error_codes::TLC_LIVENESS_VIOLATED,
    ];

    for (error, expected) in &cases {
        let actual = error_code_from_check_error(error);
        assert_eq!(
            &actual, expected,
            "CheckError::{error} → {actual}, want {expected}"
        );
        if expected.starts_with("SYS_") || expected.starts_with("CFG_") {
            for v in &violations {
                assert_ne!(actual, *v, "infra error collides with violation code {v}");
            }
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_with_check_result_emits_guard_suppression_warning() {
    use crate::{CheckResult, CheckStats};

    let stats = CheckStats {
        states_found: 3,
        initial_states: 1,
        suppressed_guard_errors: 2,
        ..Default::default()
    };
    let result = CheckResult::Success(stats);

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&result, Duration::from_secs(1));

    assert_eq!(output.statistics.suppressed_guard_errors, Some(2));
    assert_eq!(output.diagnostics.warnings.len(), 1);
    assert_eq!(
        output.diagnostics.warnings[0].code,
        error_codes::TLC_GUARD_ERRORS_SUPPRESSED
    );
}

/// Part of #3706: Setup errors (no longer POR-specific) get generic module guidance.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setup_suggestion_provides_module_guidance() {
    use super::super::error_mapping::suggestion_from_check_error;
    use crate::CheckError;

    let error: CheckError =
        ConfigCheckError::Setup("Module 'Foo' referenced in EXTENDS is not loaded".to_string())
            .into();
    let suggestion =
        suggestion_from_check_error(&error).expect("setup errors should have suggestions");

    assert!(
        suggestion.action.contains("missing modules"),
        "setup suggestion should reference missing modules: {}",
        suggestion.action,
    );
}
