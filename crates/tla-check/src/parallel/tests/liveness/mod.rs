// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness property tests — tautology detection, violation detection, satisfaction

use super::parse_module;
use super::*;
use crate::check::CheckError;
mod action_forms;
mod fp_only;
mod on_the_fly;
mod outcomes;

fn assert_temporal_action_form_rejected(result: CheckResult, label: &str) {
    match result {
        CheckResult::Error {
            error:
                CheckError::Liveness(LivenessCheckError::CannotHandleFormula {
                    reason: Some(reason),
                    ..
                }),
            ..
        }
        | CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::RuntimeFailure(reason)),
            ..
        } => {
            assert!(
                reason.contains("must be of the form <>[]A or []<>A"),
                "{label} rejection should reference supported action-temporal forms, got: {reason}"
            );
        }
        other => panic!("Expected {label} rejection, got: {other:?}"),
    }
}
