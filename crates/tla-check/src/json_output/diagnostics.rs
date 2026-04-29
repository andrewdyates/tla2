// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error codes and diagnostic message construction for JSON output.

use super::types::DiagnosticMessage;

/// Error codes for structured error handling
pub mod error_codes {
    // Model checker errors (TLC_*)
    pub const TLC_DEADLOCK: &str = "TLC_DEADLOCK";
    pub const TLC_INVARIANT_VIOLATED: &str = "TLC_INVARIANT_VIOLATED";
    pub const TLC_PROPERTY_VIOLATED: &str = "TLC_PROPERTY_VIOLATED";
    pub const TLC_LIVENESS_VIOLATED: &str = "TLC_LIVENESS_VIOLATED";
    pub const TLC_LIVE_CANNOT_HANDLE_FORMULA: &str = "TLC_LIVE_CANNOT_HANDLE_FORMULA";
    pub const TLC_LIVE_FORMULA_TAUTOLOGY: &str = "TLC_LIVE_FORMULA_TAUTOLOGY";
    pub const TLC_EVAL_ERROR: &str = "TLC_EVAL_ERROR";
    pub const TLC_TYPE_MISMATCH: &str = "TLC_TYPE_MISMATCH";
    pub const TLC_UNDEFINED_VAR: &str = "TLC_UNDEFINED_VAR";
    pub const TLC_UNDEFINED_OP: &str = "TLC_UNDEFINED_OP";
    pub const TLC_LIMIT_REACHED: &str = "TLC_LIMIT_REACHED";
    pub const TLC_GUARD_ERRORS_SUPPRESSED: &str = "TLC_GUARD_ERRORS_SUPPRESSED";

    // Configuration errors (CFG_*)
    pub const CFG_PARSE_ERROR: &str = "CFG_PARSE_ERROR";
    pub const CFG_MISSING_INIT: &str = "CFG_MISSING_INIT";
    pub const CFG_MISSING_NEXT: &str = "CFG_MISSING_NEXT";
    pub const CFG_UNSUPPORTED_SYNTAX: &str = "CFG_UNSUPPORTED_SYNTAX";

    // TLA+ parsing errors (TLA_*)
    pub const TLA_PARSE_ERROR: &str = "TLA_PARSE_ERROR";
    pub const TLA_LOWER_ERROR: &str = "TLA_LOWER_ERROR";

    // System errors (SYS_*)
    pub const SYS_LIVENESS_ERROR: &str = "SYS_LIVENESS_ERROR";
    pub const SYS_LIVENESS_RUNTIME_FAILURE: &str = "SYS_LIVENESS_RUNTIME_FAILURE";
    pub const SYS_IO_ERROR: &str = "SYS_IO_ERROR";
    pub const SYS_TIMEOUT: &str = "SYS_TIMEOUT";
    pub const SYS_SETUP_ERROR: &str = "SYS_SETUP_ERROR";
    pub const SYS_SOUNDNESS_GATED: &str = "SYS_SOUNDNESS_GATED";
    pub const SYS_COMPLETENESS_GATED: &str = "SYS_COMPLETENESS_GATED";

    // Trace validation errors (TRACE_*)
    //
    // These are intended for semantic trace validation / diagnostics, not model checking results.
    pub const TRACE_PARAM_BIND_MISSING_BINDER: &str = "TRACE_PARAM_BIND_MISSING_BINDER";
    pub const TRACE_PARAM_BIND_AMBIGUOUS_BINDER: &str = "TRACE_PARAM_BIND_AMBIGUOUS_BINDER";
    pub const TRACE_PARAM_BIND_MISSING_CALLSITE: &str = "TRACE_PARAM_BIND_MISSING_CALLSITE";
    pub const TRACE_PARAM_BIND_AMBIGUOUS_CALLSITE: &str = "TRACE_PARAM_BIND_AMBIGUOUS_CALLSITE";
    pub const TRACE_PARAM_BIND_UNSUPPORTED_CALLSITE_ARG: &str =
        "TRACE_PARAM_BIND_UNSUPPORTED_CALLSITE_ARG";
    pub const TRACE_PARAM_BIND_UNSUPPORTED_BINDER_PATTERN: &str =
        "TRACE_PARAM_BIND_UNSUPPORTED_BINDER_PATTERN";
}

impl DiagnosticMessage {
    /// Convert a rewrite-backend action-label param binding error into a structured diagnostic.
    pub fn from_action_label_param_bind_error(err: &crate::ActionLabelParamBindError) -> Self {
        fn span_payload(span: tla_core::Span) -> serde_json::Value {
            serde_json::json!({
                "file_id": span.file.0,
                "start": span.start,
                "end": span.end,
            })
        }

        fn binder_site_payload(site: &crate::BoundVarSite) -> serde_json::Value {
            serde_json::json!({
                "name": site.name,
                "span": span_payload(site.span),
            })
        }

        use crate::ActionLabelParamBindErrorKind;

        let outer_binders: Vec<serde_json::Value> =
            err.outer_binders.iter().map(binder_site_payload).collect();

        let (code, kind, param) = match &err.kind {
            ActionLabelParamBindErrorKind::MissingBinder { param } => (
                error_codes::TRACE_PARAM_BIND_MISSING_BINDER,
                "missing_binder",
                param.as_str(),
            ),
            ActionLabelParamBindErrorKind::AmbiguousBinder { param, .. } => (
                error_codes::TRACE_PARAM_BIND_AMBIGUOUS_BINDER,
                "ambiguous_binder",
                param.as_str(),
            ),
            ActionLabelParamBindErrorKind::MissingCallsite { param } => (
                error_codes::TRACE_PARAM_BIND_MISSING_CALLSITE,
                "missing_callsite",
                param.as_str(),
            ),
            ActionLabelParamBindErrorKind::AmbiguousCallsite { param, .. } => (
                error_codes::TRACE_PARAM_BIND_AMBIGUOUS_CALLSITE,
                "ambiguous_callsite",
                param.as_str(),
            ),
            ActionLabelParamBindErrorKind::UnsupportedCallsiteArg { param, .. } => (
                error_codes::TRACE_PARAM_BIND_UNSUPPORTED_CALLSITE_ARG,
                "unsupported_callsite_arg",
                param.as_str(),
            ),
        };

        let mut payload = serde_json::Map::new();
        payload.insert("label".to_string(), serde_json::json!(err.label));
        payload.insert(
            "operator_raw".to_string(),
            serde_json::json!(err.operator_raw),
        );
        payload.insert(
            "action_name".to_string(),
            serde_json::json!(err.action_name),
        );
        payload.insert(
            "action_id".to_string(),
            serde_json::json!(err.action_id.to_string()),
        );
        payload.insert(
            "action_span".to_string(),
            serde_json::json!(span_payload(err.action_span)),
        );
        payload.insert(
            "outer_binders".to_string(),
            serde_json::Value::Array(outer_binders),
        );
        payload.insert("kind".to_string(), serde_json::json!(kind));
        payload.insert("param".to_string(), serde_json::json!(param));

        match &err.kind {
            ActionLabelParamBindErrorKind::AmbiguousBinder { matches, .. } => {
                let matches_payload: Vec<serde_json::Value> =
                    matches.iter().map(binder_site_payload).collect();
                payload.insert(
                    "matches".to_string(),
                    serde_json::Value::Array(matches_payload),
                );
            }
            ActionLabelParamBindErrorKind::AmbiguousCallsite { callsites, .. } => {
                let spans_payload: Vec<serde_json::Value> =
                    callsites.iter().copied().map(span_payload).collect();
                payload.insert(
                    "callsites".to_string(),
                    serde_json::Value::Array(spans_payload),
                );
            }
            ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
                position,
                arg,
                arg_span,
                ..
            } => {
                payload.insert("position".to_string(), serde_json::json!(position));
                payload.insert("arg".to_string(), serde_json::json!(arg));
                payload.insert(
                    "arg_span".to_string(),
                    serde_json::json!(span_payload(*arg_span)),
                );
            }
            _ => {}
        }

        Self {
            code: code.to_string(),
            message: err.to_string(),
            location: None,
            suggestion: Some(err.suggestion_text().to_string()),
            payload: Some(serde_json::Value::Object(payload)),
        }
    }
}
