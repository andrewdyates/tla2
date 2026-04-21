// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for trace param bind error diagnostic payloads (4 error kind variants).

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_param_bind_error_diagnostic_payload() {
    use crate::{
        ActionLabelParamBindError, ActionLabelParamBindErrorKind, BoundVarSite, DetectedActionId,
    };
    use tla_core::{FileId, Span};

    let err = ActionLabelParamBindError {
        label: "A".to_string(),
        operator_raw: "Op".to_string(),
        action_name: "Approve".to_string(),
        action_id: DetectedActionId::new(Span::new(FileId(7), 100, 200)),
        action_span: Span::new(FileId(7), 100, 200),
        outer_binders: vec![
            BoundVarSite {
                name: "reqId".to_string(),
                span: Span::new(FileId(7), 110, 115),
            },
            BoundVarSite {
                name: "p".to_string(),
                span: Span::new(FileId(7), 120, 121),
            },
        ],
        kind: ActionLabelParamBindErrorKind::MissingBinder {
            param: "q".to_string(),
        },
    };

    let diag = DiagnosticMessage::from_action_label_param_bind_error(&err);
    assert_eq!(diag.code, error_codes::TRACE_PARAM_BIND_MISSING_BINDER);
    let payload = diag.payload.expect("payload present");
    assert_eq!(payload["label"], "A");
    assert_eq!(payload["operator_raw"], "Op");
    assert_eq!(payload["action_name"], "Approve");
    assert_eq!(payload["action_id"], "7:100-200");
    assert_eq!(payload["action_span"]["file_id"], 7);
    assert_eq!(payload["kind"], "missing_binder");
    assert_eq!(payload["param"], "q");
    assert_eq!(payload["outer_binders"][0]["name"], "reqId");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_param_bind_error_ambiguous_diagnostic_payload() {
    use crate::{
        ActionLabelParamBindError, ActionLabelParamBindErrorKind, BoundVarSite, DetectedActionId,
    };
    use tla_core::{FileId, Span};

    let err = ActionLabelParamBindError {
        label: "A".to_string(),
        operator_raw: "Op".to_string(),
        action_name: "Approve".to_string(),
        action_id: DetectedActionId::new(Span::new(FileId(7), 100, 200)),
        action_span: Span::new(FileId(7), 100, 200),
        outer_binders: vec![
            BoundVarSite {
                name: "p".to_string(),
                span: Span::new(FileId(7), 110, 115),
            },
            BoundVarSite {
                name: "q".to_string(),
                span: Span::new(FileId(7), 120, 121),
            },
            BoundVarSite {
                name: "p".to_string(),
                span: Span::new(FileId(7), 130, 131),
            },
        ],
        kind: ActionLabelParamBindErrorKind::AmbiguousBinder {
            param: "p".to_string(),
            matches: vec![
                BoundVarSite {
                    name: "p".to_string(),
                    span: Span::new(FileId(7), 110, 115),
                },
                BoundVarSite {
                    name: "p".to_string(),
                    span: Span::new(FileId(7), 130, 131),
                },
            ],
        },
    };

    let diag = DiagnosticMessage::from_action_label_param_bind_error(&err);
    assert_eq!(diag.code, error_codes::TRACE_PARAM_BIND_AMBIGUOUS_BINDER);
    let payload = diag.payload.expect("payload present");
    assert_eq!(payload["label"], "A");
    assert_eq!(payload["kind"], "ambiguous_binder");
    assert_eq!(payload["param"], "p");
    assert_eq!(
        payload["matches"]
            .as_array()
            .expect("invariant: serialization succeeds for well-formed types")
            .len(),
        2
    );
    assert_eq!(payload["matches"][0]["name"], "p");
    assert_eq!(payload["matches"][0]["span"]["file_id"], 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_param_bind_error_missing_callsite_diagnostic_payload() {
    use crate::{
        ActionLabelParamBindError, ActionLabelParamBindErrorKind, BoundVarSite, DetectedActionId,
    };
    use tla_core::{FileId, Span};

    let err = ActionLabelParamBindError {
        label: "A".to_string(),
        operator_raw: "Op".to_string(),
        action_name: "Approve".to_string(),
        action_id: DetectedActionId::new(Span::new(FileId(7), 100, 200)),
        action_span: Span::new(FileId(7), 100, 200),
        outer_binders: vec![BoundVarSite {
            name: "reqId".to_string(),
            span: Span::new(FileId(7), 110, 115),
        }],
        kind: ActionLabelParamBindErrorKind::MissingCallsite {
            param: "req".to_string(),
        },
    };

    let diag = DiagnosticMessage::from_action_label_param_bind_error(&err);
    assert_eq!(diag.code, error_codes::TRACE_PARAM_BIND_MISSING_CALLSITE);
    let payload = diag.payload.expect("payload present");
    assert_eq!(payload["kind"], "missing_callsite");
    assert_eq!(payload["param"], "req");
    assert!(payload.get("callsites").is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_param_bind_error_unsupported_callsite_arg_diagnostic_payload() {
    use crate::{
        ActionLabelParamBindError, ActionLabelParamBindErrorKind, BoundVarSite, DetectedActionId,
    };
    use tla_core::{FileId, Span};

    let err = ActionLabelParamBindError {
        label: "A".to_string(),
        operator_raw: "Op".to_string(),
        action_name: "Approve".to_string(),
        action_id: DetectedActionId::new(Span::new(FileId(7), 100, 200)),
        action_span: Span::new(FileId(7), 100, 200),
        outer_binders: vec![BoundVarSite {
            name: "reqId".to_string(),
            span: Span::new(FileId(7), 110, 115),
        }],
        kind: ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
            param: "req".to_string(),
            position: 0,
            arg: "reqId + 1".to_string(),
            arg_span: Span::new(FileId(7), 130, 137),
        },
    };

    let diag = DiagnosticMessage::from_action_label_param_bind_error(&err);
    assert_eq!(
        diag.code,
        error_codes::TRACE_PARAM_BIND_UNSUPPORTED_CALLSITE_ARG
    );
    let payload = diag.payload.expect("payload present");
    assert_eq!(payload["kind"], "unsupported_callsite_arg");
    assert_eq!(payload["param"], "req");
    assert_eq!(payload["position"], 0);
    assert_eq!(payload["arg"], "reqId + 1");
    assert_eq!(payload["arg_span"]["file_id"], 7);
}
