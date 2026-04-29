// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime policy predicates for configuration.

use super::types::{Config, ConfigValidationIssue};

impl Config {
    /// Returns true when the parsed config file specified SPECIFICATION
    /// alongside INIT or NEXT, which TLC rejects.
    #[must_use]
    pub fn specification_conflicts_with_init_next(&self) -> bool {
        self.specification.is_some() && (self.init.is_some() || self.next.is_some())
    }

    /// Normalize a config after resolving SPECIFICATION into INIT/NEXT.
    ///
    /// CLI/test call sites that resolve a SPECIFICATION formula into concrete
    /// INIT/NEXT operator names should clear `specification` before passing the
    /// config into runtime-only paths. This keeps the config aligned with the
    /// actual execution shape without weakening validation of the original file.
    pub fn normalize_resolved_specification(&mut self) {
        if self.specification.is_some() && self.init.is_some() && self.next.is_some() {
            self.specification = None;
        }
    }

    /// Clone the config into the shape consumed by checker runtime paths.
    #[must_use]
    pub fn runtime_model_config(&self) -> Self {
        let mut runtime = self.clone();
        runtime.normalize_resolved_specification();
        runtime
    }

    /// Validate field-relationship consistency.
    ///
    /// Returns a list of issues found. All current issues are hard errors.
    ///
    /// Part of #2692.
    #[must_use]
    pub(crate) fn validate(&self) -> Vec<ConfigValidationIssue> {
        let mut issues = Vec::new();

        // SPECIFICATION and INIT/NEXT are mutually exclusive (TLC ModelConfig.java).
        if self.specification_conflicts_with_init_next() {
            issues.push(ConfigValidationIssue::SpecificationWithInitNext);
        }

        issues
    }

    /// Validate runtime-relevant config policy after SPECIFICATION resolution.
    ///
    /// Some callers populate `INIT`/`NEXT` from `SPECIFICATION` before
    /// invoking `check()`. Re-running full validation there would
    /// false-positive on the now-populated config, so runtime validation only
    /// checks policies that remain meaningful after resolution.
    #[must_use]
    pub(crate) fn validate_runtime(&self) -> Vec<ConfigValidationIssue> {
        let issues = Vec::new();
        issues
    }

    /// Returns true when temporal PROPERTIES are configured.
    ///
    /// Shared policy predicate used by both adaptive and direct-parallel entry points.
    /// Part of #2250.
    #[must_use]
    pub(crate) fn has_liveness_properties(&self) -> bool {
        !self.properties.is_empty()
    }

    /// Returns the fingerprint-only liveness warning message when temporal
    /// properties are configured but full states are not stored.
    ///
    /// TLC warns when liveness is unavailable in fingerprint-only mode.
    /// `promoted_names` contains property names whose safety parts (state-level
    /// invariants and action-level implied actions) have been fully extracted
    /// for BFS-phase checking (#2670). Only properties with remaining temporal
    /// components (WF, SF, <>, ~>) are listed in the warning.
    #[must_use]
    pub(crate) fn fingerprint_liveness_warning(
        &self,
        store_full_states: bool,
        promoted_names: &[String],
    ) -> Option<String> {
        if store_full_states || !self.has_liveness_properties() {
            return None;
        }

        // Filter out fully-promoted properties (their safety parts are BFS-checked).
        let temporal_names: Vec<&str> = self
            .properties
            .iter()
            .filter(|name| !promoted_names.contains(name))
            .map(std::string::String::as_str)
            .collect();

        if temporal_names.is_empty() {
            return None;
        }

        Some(format!(
            "Warning: Temporal liveness checking (WF, SF, <>, ~>) is not supported in \
             fingerprint-only mode. Skipping temporal properties: {}. \
             Use --store-states to enable liveness checking.",
            temporal_names.join(", ")
        ))
    }
}
