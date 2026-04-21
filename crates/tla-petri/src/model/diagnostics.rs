// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[derive(Debug, Clone, Default)]
pub(super) struct ColoredExecutionDiagnostics {
    properties: Vec<ColoredPropertyDiagnostic>,
}

impl ColoredExecutionDiagnostics {
    pub(super) fn push(&mut self, diagnostic: ColoredPropertyDiagnostic) {
        if diagnostic.should_render() {
            self.properties.push(diagnostic);
        }
    }

    pub(super) fn emit_stderr(&self) {
        for diagnostic in &self.properties {
            diagnostic.emit_stderr();
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct ColoredLoadDiagnostics {
    collapsed_places: usize,
    places_saved: usize,
    transitions_removed: usize,
}

impl ColoredLoadDiagnostics {
    pub(super) fn new(
        collapsed_places: usize,
        places_saved: usize,
        transitions_removed: usize,
    ) -> Self {
        Self {
            collapsed_places,
            places_saved,
            transitions_removed,
        }
    }

    pub(super) fn emit_stderr(&self) {
        if self.places_saved > 0 {
            eprintln!(
                "colored reduction: collapsed {} places, saving {} unfolded instances",
                self.collapsed_places, self.places_saved,
            );
        }
        if self.transitions_removed > 0 {
            eprintln!(
                "colored dead transitions: removed {} transitions",
                self.transitions_removed,
            );
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct ColoredPropertyDiagnostic {
    property_id: String,
    places_removed: usize,
    transitions_removed: usize,
    fallback_reason: Option<String>,
}

impl ColoredPropertyDiagnostic {
    pub(super) fn new(property_id: String) -> Self {
        Self {
            property_id,
            ..Self::default()
        }
    }

    fn should_render(&self) -> bool {
        self.places_removed > 0 || self.transitions_removed > 0 || self.fallback_reason.is_some()
    }

    fn emit_stderr(&self) {
        if self.places_removed > 0 || self.transitions_removed > 0 {
            eprintln!(
                "colored relevance ({}): removed {} places, {} transitions",
                self.property_id, self.places_removed, self.transitions_removed,
            );
        }
        if let Some(reason) = &self.fallback_reason {
            eprintln!(
                "colored relevance unfold failed for {}: {}, using full net",
                self.property_id, reason,
            );
        }
    }

    pub(super) fn set_reduction(&mut self, places_removed: usize, transitions_removed: usize) {
        self.places_removed = places_removed;
        self.transitions_removed = transitions_removed;
    }

    pub(super) fn set_fallback_reason(&mut self, reason: String) {
        self.fallback_reason = Some(reason);
    }
}
