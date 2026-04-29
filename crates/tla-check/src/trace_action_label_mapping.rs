// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trace action-label mapping config loading and runtime validation.

mod config;
mod runtime;

pub use config::{
    ActionLabelInstanceError, ActionLabelMapping, ActionLabelMappingConfig, ActionParamEncoding,
    OperatorRef, TraceActionLabelMappingError,
};
pub use runtime::{validate_action_label, ActionLabelValidationError, ActionLabelValidationResult};

#[cfg(test)]
mod tests;
