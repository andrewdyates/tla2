// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[path = "../common/mod.rs"]
mod common;

mod core;
mod liveness;
mod symmetry;

use tla_check::{
    resolve_spec_from_config, set_use_handle_state_override, CheckError, CheckResult, CheckStats,
    Config, ConstantValue, ModelChecker, ParallelChecker,
};
use tla_check::{
    ConfigCheckError, EvalCheckError, InfraCheckError, LivenessCheckError, RuntimeCheckError,
};
use tla_core::{lower, parse_to_syntax_tree, FileId};

/// Process-local lock to serialize parity tests that exercise the parallel
/// checker pipeline. Required because freeze/unfreeze of the value interner
/// uses process-global state (PARALLEL_INTERN_ACTIVE, FROZEN_SNAPSHOT) that
/// cannot be isolated between concurrent test threads.
///
/// Same root cause as #3300, but for integration tests which cannot access
/// the `#[cfg(test)] pub(crate) mod test_utils` in tla-check's lib.rs.
static PARITY_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn acquire_parity_lock() -> std::sync::MutexGuard<'static, ()> {
    PARITY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// These integration tests compare independent specs in one process, so they
/// need both serialized access to the parallel checker and a full run reset at
/// the test boundary.
struct ParityTestScope {
    _serial: std::sync::MutexGuard<'static, ()>,
}

impl ParityTestScope {
    fn begin() -> Self {
        let serial = acquire_parity_lock();
        tla_check::reset_global_state();
        Self { _serial: serial }
    }
}

impl Drop for ParityTestScope {
    fn drop(&mut self) {
        tla_check::reset_global_state();
    }
}

fn stats(result: &CheckResult) -> &CheckStats {
    match result {
        CheckResult::Success(stats)
        | CheckResult::InvariantViolation { stats, .. }
        | CheckResult::PropertyViolation { stats, .. }
        | CheckResult::LivenessViolation { stats, .. }
        | CheckResult::Deadlock { stats, .. }
        | CheckResult::Error { stats, .. }
        | CheckResult::LimitReached { stats, .. } => stats,
        _ => panic!("unhandled CheckResult variant: {result:?}"),
    }
}

fn assert_result_kind_parity(
    case_name: &str,
    use_handle_state: bool,
    seq: &CheckResult,
    par: &CheckResult,
) {
    match (seq, par) {
        (CheckResult::Success(_), CheckResult::Success(_)) => {}
        (
            CheckResult::InvariantViolation {
                invariant: seq_inv, ..
            },
            CheckResult::InvariantViolation {
                invariant: par_inv, ..
            },
        ) => {
            assert_eq!(
                seq_inv, par_inv,
                "{case_name}: invariant mismatch (handle_state={use_handle_state})"
            );
        }
        (
            CheckResult::PropertyViolation {
                property: seq_prop, ..
            },
            CheckResult::PropertyViolation {
                property: par_prop, ..
            },
        ) => {
            assert_eq!(
                seq_prop, par_prop,
                "{case_name}: property mismatch (handle_state={use_handle_state})"
            );
        }
        (
            CheckResult::LivenessViolation {
                property: seq_prop, ..
            },
            CheckResult::LivenessViolation {
                property: par_prop, ..
            },
        ) => {
            assert_eq!(
                seq_prop, par_prop,
                "{case_name}: liveness property mismatch (handle_state={use_handle_state})"
            );
        }
        (CheckResult::Deadlock { .. }, CheckResult::Deadlock { .. }) => {}
        (
            CheckResult::Error {
                error: seq_error, ..
            },
            CheckResult::Error {
                error: par_error, ..
            },
        ) => {
            assert_eq!(
                check_error_kind(seq_error),
                check_error_kind(par_error),
                "{case_name}: error kind mismatch (handle_state={use_handle_state})"
            );
        }
        (
            CheckResult::LimitReached {
                limit_type: seq_limit,
                ..
            },
            CheckResult::LimitReached {
                limit_type: par_limit,
                ..
            },
        ) => {
            assert_eq!(
                seq_limit, par_limit,
                "{case_name}: limit type mismatch (handle_state={use_handle_state})"
            );
        }
        _ => {
            panic!(
                "{case_name}: result kind mismatch (handle_state={use_handle_state}): seq={seq:?}, par={par:?}"
            );
        }
    }
}

fn check_error_kind(error: &CheckError) -> &'static str {
    match error {
        CheckError::Config(ConfigCheckError::Setup(_)) => "SetupError",
        CheckError::Config(ConfigCheckError::MissingInit) => "MissingInit",
        CheckError::Config(ConfigCheckError::MissingNext) => "MissingNext",
        CheckError::Config(ConfigCheckError::MissingInvariant(_)) => "MissingInvariant",
        CheckError::Config(ConfigCheckError::MissingProperty(_)) => "MissingProperty",
        CheckError::Eval(EvalCheckError::Eval(_)) => "EvalError",
        CheckError::Eval(EvalCheckError::InitNotBoolean) => "InitNotBoolean",
        CheckError::Eval(EvalCheckError::NextNotBoolean) => "NextNotBoolean",
        CheckError::Eval(EvalCheckError::InvariantNotBoolean(_)) => "InvariantNotBoolean",
        CheckError::Eval(EvalCheckError::PropertyNotBoolean(_)) => "PropertyNotBoolean",
        CheckError::Config(ConfigCheckError::NoVariables) => "NoVariables",
        CheckError::Config(ConfigCheckError::InitCannotEnumerate(_)) => "InitCannotEnumerate",
        CheckError::Config(ConfigCheckError::Specification(_)) => "SpecificationError",
        CheckError::Config(ConfigCheckError::Config(_)) => "ConfigError",
        CheckError::Liveness(LivenessCheckError::Generic(_)) => "LivenessError",
        CheckError::Liveness(LivenessCheckError::CannotHandleFormula { .. }) => {
            "TlcLiveCannotHandleFormula"
        }
        CheckError::Infra(InfraCheckError::FingerprintOverflow { .. }) => {
            "FingerprintStorageOverflow"
        }
        CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. }) => "AssumeFalse",
        CheckError::Runtime(RuntimeCheckError::PostconditionFalse { .. }) => "PostconditionFalse",
        _ => "UnknownCheckErrorVariant",
    }
}

fn assert_parallel_sequential_parity(
    case_name: &str,
    src: &str,
    config: Config,
    workers: usize,
    expected_seq_counts: Option<(usize, usize)>,
) {
    let module = common::parse_module(src);

    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();
    let seq_stats = stats(&seq_result);

    if let Some((expected_states, expected_initial)) = expected_seq_counts {
        assert_eq!(
            seq_stats.states_found, expected_states,
            "{case_name}: sequential states_found mismatch"
        );
        assert_eq!(
            seq_stats.initial_states, expected_initial,
            "{case_name}: sequential initial_states mismatch"
        );
    }

    for use_handle_state in [false, true] {
        let _guard = set_use_handle_state_override(use_handle_state);

        let mut par_checker = ParallelChecker::new(&module, &config, workers);
        par_checker.set_deadlock_check(false);
        let par_result = par_checker.check();
        let par_stats = stats(&par_result);

        assert_result_kind_parity(case_name, use_handle_state, &seq_result, &par_result);
        assert_eq!(
            seq_stats.states_found, par_stats.states_found,
            "{case_name}: states_found mismatch (handle_state={use_handle_state})"
        );
        assert_eq!(
            seq_stats.initial_states, par_stats.initial_states,
            "{case_name}: initial_states mismatch (handle_state={use_handle_state})"
        );
    }
}
