// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{
    format_span_location, format_span_location_from_source, Arc, CheckError, Expr,
    FairnessToLiveExprError, ModelChecker, Spanned,
};
use crate::LivenessCheckError;

impl<'a> ModelChecker<'a> {
    pub(super) fn module_name_for_file(&self, file: tla_core::FileId) -> &str {
        self.module
            .file_id_to_name
            .get(&file)
            .map_or(self.module.root_name.as_str(), std::string::String::as_str)
    }

    pub(super) fn format_span_location_for_error(&self, span: &tla_core::span::Span) -> String {
        let module_name = self.module_name_for_file(span.file);
        if let Some(path) = self.module.file_id_to_path.get(&span.file) {
            if let Ok(source) = std::fs::read_to_string(path) {
                return format_span_location_from_source(span, module_name, &source);
            }
        }
        format_span_location(span, module_name)
    }

    pub(super) fn tlc_live_cannot_handle_formula_error(
        &self,
        original: &Arc<Spanned<Expr>>,
        reason: Option<String>,
    ) -> CheckError {
        LivenessCheckError::CannotHandleFormula {
            location: self.format_span_location_for_error(&original.span),
            reason,
        }
        .into()
    }

    pub(super) fn render_convert_error(&self, err: &crate::liveness::ConvertError) -> String {
        use crate::liveness::ConvertError;

        match err {
            ConvertError::CannotHandleFormula {
                original, reason, ..
            } => self
                .tlc_live_cannot_handle_formula_error(original, reason.clone())
                .to_string(),
            other => other.to_string(),
        }
    }

    pub(super) fn check_error_for_liveness_convert_error(
        &self,
        prop_name: &str,
        err: crate::liveness::ConvertError,
    ) -> CheckError {
        use crate::liveness::ConvertError;

        match err {
            ConvertError::CannotHandleFormula {
                original, reason, ..
            } => self.tlc_live_cannot_handle_formula_error(&original, reason),
            other => LivenessCheckError::Generic(format!(
                "Failed to convert property '{}': {}",
                prop_name,
                self.render_convert_error(&other)
            ))
            .into(),
        }
    }

    pub(super) fn check_error_for_fairness_to_live_expr_error(
        &self,
        prop_name: &str,
        err: FairnessToLiveExprError,
    ) -> CheckError {
        use crate::liveness::ConvertError;

        match err {
            FairnessToLiveExprError::Convert(detail) => match detail.error {
                ConvertError::CannotHandleFormula {
                    original, reason, ..
                } => self.tlc_live_cannot_handle_formula_error(&original, reason),
                other => LivenessCheckError::Generic(format!(
                    "Failed to process fairness for property '{}': {}: {}",
                    prop_name,
                    detail.context,
                    self.render_convert_error(&other)
                ))
                .into(),
            },
            FairnessToLiveExprError::Other(msg) => LivenessCheckError::Generic(format!(
                "Failed to process fairness for property '{}': {}",
                prop_name, msg
            ))
            .into(),
        }
    }
}
