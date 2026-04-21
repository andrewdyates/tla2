// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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

mod action_forms;
mod promoted_state_predicates;
mod state_body_subscripts;
