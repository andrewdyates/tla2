// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Source mapping from TLA+ states/transitions to Rust source locations.

use std::collections::BTreeMap;
use std::fmt::{self, Write};

use serde::{Deserialize, Serialize};

use crate::model::{AccessSite, ConcurrentModel, ProcessId, SharedVar, StateId};
use crate::transition::{Transition, TransitionKind};

/// Mapping from TLA+ model elements to Rust source spans.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SourceMap {
    /// Ordered list of source map entries, indexed by transition.
    pub entries: Vec<SourceMapEntry>,
}

/// A single source map entry linking a TLA+ transition to Rust source.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceMapEntry {
    /// The TLA+ state this transition originates from.
    pub from_state: StateId,
    /// The TLA+ state this transition leads to.
    pub to_state: StateId,
    /// The process performing this transition.
    pub process: ProcessId,
    /// A string tag for the transition kind (for matching against action labels).
    pub transition_tag: String,
    /// Rust source file path.
    pub rust_file: String,
    /// Start line in Rust source (1-indexed).
    pub rust_line: u32,
    /// Start column in Rust source (1-indexed).
    pub rust_col: u32,
    /// End line in Rust source (1-indexed).
    pub rust_end_line: u32,
    /// End column in Rust source (1-indexed).
    pub rust_end_col: u32,
}

/// A Rust source span.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// A counterexample trace with source-mapped steps.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MappedTrace {
    pub steps: Vec<MappedStep>,
}

/// A single step in a source-mapped counterexample trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MappedStep {
    /// Which process took this step.
    pub process: ProcessId,
    /// The transition kind.
    pub transition_tag: String,
    /// Rust source location (if available).
    pub rust_location: Option<SourceSpan>,
    /// State variable snapshot after this step.
    pub state_snapshot: BTreeMap<String, String>,
}

impl SourceMap {
    /// Build a source map from the source-location-bearing access sites in a model.
    #[must_use]
    pub fn from_model(model: &ConcurrentModel) -> Self {
        let mut entries = Vec::new();

        for process in &model.processes {
            for transition in &process.transitions {
                if let Some(site) = find_access_site_for_transition(model, &process.id, transition)
                {
                    if let Some(entry) =
                        source_map_entry_from_access_site(&process.id, transition, site)
                    {
                        entries.push(entry);
                    }
                }
            }
        }

        Self { entries }
    }

    /// Look up the source entry for a given action label.
    ///
    /// Matches by comparing the action label name against `transition_tag`
    /// values in the source map.
    pub fn find_by_action_label(&self, action_label: &str) -> Option<&SourceMapEntry> {
        self.entries
            .iter()
            .find(|e| e.transition_tag == action_label)
    }

    /// Look up all entries for a given process.
    pub fn entries_for_process(&self, process: &str) -> Vec<&SourceMapEntry> {
        self.entries
            .iter()
            .filter(|e| e.process == process)
            .collect()
    }

    /// Look up a source map entry by process ID, from-state, and to-state.
    ///
    /// This matches the generated TLA+ action naming convention:
    /// `Action_{process}_{from}_{to}`.
    pub fn find_by_transition(
        &self,
        process: &str,
        from_state: &str,
        to_state: &str,
    ) -> Option<&SourceMapEntry> {
        self.entries
            .iter()
            .find(|e| e.process == process && e.from_state == from_state && e.to_state == to_state)
    }
}

impl SourceSpan {
    /// Format as `file:line:col`.
    #[must_use]
    pub fn format_short(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.col)
    }
}

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

#[cfg(not(feature = "check"))]
impl MappedTrace {
    /// Format a human-readable representation of the trace.
    #[must_use]
    pub fn format_human_readable(&self) -> String {
        let mut out = String::new();
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(
                out,
                "Step {}: [{}] {}",
                i + 1,
                step.process,
                step.transition_tag
            );
            if let Some(ref loc) = step.rust_location {
                let _ = write!(out, " at {}:{}:{}", loc.file, loc.line, loc.col);
            }
            let _ = writeln!(out);

            for (var, val) in &step.state_snapshot {
                let _ = writeln!(out, "  {} = {}", var, val);
            }
        }
        out
    }
}

impl MappedStep {
    /// Format the source location as `file:line:col` or `<unknown>`.
    #[must_use]
    pub fn format_location(&self) -> String {
        match &self.rust_location {
            Some(loc) => loc.format_short(),
            None => "<unknown>".to_string(),
        }
    }
}

impl fmt::Display for MappedStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {} at {}",
            self.process,
            self.transition_tag,
            self.format_location()
        )
    }
}

impl MappedTrace {
    /// Serialize to a JSON value.
    ///
    /// Returns `serde_json::Value::Null` if serialization fails (should not
    /// happen for well-formed traces).
    #[must_use]
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::to_value(self).unwrap_or(serde_json::Value::Null)
    }

    /// Compact one-line-per-step format for concise output.
    ///
    /// Each line: `Step N: [process] action at file:line`
    #[must_use]
    pub fn format_compact(&self) -> String {
        let mut out = String::new();
        for (i, step) in self.steps.iter().enumerate() {
            let location = step
                .rust_location
                .as_ref()
                .map(|loc| format!("{}:{}", loc.file, loc.line))
                .unwrap_or_else(|| "<unknown>".to_string());
            let _ = writeln!(
                out,
                "Step {}: [{}] {} at {}",
                i + 1,
                step.process,
                step.transition_tag,
                location
            );
        }
        out
    }

    /// Format a liveness counterexample (prefix + cycle).
    #[must_use]
    pub fn format_liveness(prefix: &MappedTrace, cycle: &MappedTrace) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "Prefix:");
        if prefix.steps.is_empty() {
            let _ = writeln!(out, "<empty>");
        } else {
            out.push_str(&prefix.format_human_readable());
        }

        let _ = writeln!(out, "Cycle:");
        if cycle.steps.is_empty() {
            let _ = writeln!(out, "<empty>");
        } else {
            out.push_str(&cycle.format_human_readable());
        }
        out
    }
}

impl fmt::Display for MappedTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format_human_readable())
    }
}

fn find_access_site_for_transition<'a>(
    model: &'a ConcurrentModel,
    process: &str,
    transition: &Transition,
) -> Option<&'a AccessSite> {
    let accessed_var = transition_accessed_variable(transition);
    let mut best_match = None;
    let mut best_score = 0_u8;

    for var in &model.shared_vars {
        let matches_var = accessed_var
            .map(|name| shared_var_matches_name(var, name))
            .unwrap_or(false);

        for site in &var.access_sites {
            let score = access_site_match_score(site, process, transition, matches_var);
            if score > best_score {
                best_score = score;
                best_match = Some(site);
            }
        }
    }

    best_match
}

fn access_site_match_score(
    site: &AccessSite,
    process: &str,
    transition: &Transition,
    matches_var: bool,
) -> u8 {
    if site.process != process || site.source_file.is_none() || site.source_line.is_none() {
        return 0;
    }

    match site.state_id.as_deref() {
        Some(state_id) if state_id == transition.to.as_str() => 4,
        Some(state_id) if state_id == transition.from.as_str() => 3,
        None if matches_var => 2,
        _ => 0,
    }
}

fn source_map_entry_from_access_site(
    process: &str,
    transition: &Transition,
    site: &AccessSite,
) -> Option<SourceMapEntry> {
    let rust_file = site.source_file.clone()?;
    let rust_line = site.source_line?;
    let rust_col = site.source_col.unwrap_or(1);

    Some(SourceMapEntry {
        from_state: transition.from.clone(),
        to_state: transition.to.clone(),
        process: process.to_string(),
        transition_tag: transition.kind.tag().to_string(),
        rust_file,
        rust_line,
        rust_col,
        rust_end_line: rust_line,
        rust_end_col: rust_col,
    })
}

fn shared_var_matches_name(var: &SharedVar, name: &str) -> bool {
    var.name == name || var.field_path.last().map_or(false, |field| field == name)
}

fn transition_accessed_variable(transition: &Transition) -> Option<&str> {
    match &transition.kind {
        TransitionKind::AtomicLoad { variable, .. }
        | TransitionKind::AtomicStore { variable, .. }
        | TransitionKind::AtomicRmw { variable, .. }
        | TransitionKind::CasOk { variable, .. }
        | TransitionKind::CasFail { variable, .. } => Some(variable),
        _ => None,
    }
}
