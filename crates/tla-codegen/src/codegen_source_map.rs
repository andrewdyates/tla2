// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Source mapping from TLA+ operators to generated Rust source lines.
//!
//! Some items are `pub(crate)` infrastructure for future trace annotation
//! integration and are exercised only by unit tests at present.

use std::fmt;

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Source map from TLA+ operators to generated Rust source spans.
///
/// Produced during code generation and persisted alongside the generated
/// Rust file. Used to annotate model checker counterexample traces with
/// the specific Rust source lines corresponding to each TLA+ action.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodegenSourceMap {
    /// The generated Rust file this map refers to.
    pub(crate) generated_file: String,
    /// The TLA+ source file this was generated from.
    pub(crate) tla_source: String,
    /// Per-operator mappings in emission order.
    pub(crate) entries: Vec<CodegenSourceMapEntry>,
}

/// A single entry mapping a TLA+ construct to a Rust source range.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CodegenSourceMapEntry {
    /// The TLA+ operator name (for example, `Init` or `Next`).
    pub(crate) tla_operator: String,
    /// What kind of construct this is.
    pub(crate) kind: CodegenEntryKind,
    /// Start line in the generated Rust file (1-indexed).
    pub(crate) rust_start_line: u32,
    /// End line in the generated Rust file (1-indexed).
    pub(crate) rust_end_line: u32,
}

/// The kind of TLA+ construct that was code-generated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) enum CodegenEntryKind {
    /// The state struct definition.
    StateStruct,
    /// An Init action (generates initial states).
    Init,
    /// A Next action (generates successor states).
    Next,
    /// An invariant check.
    Invariant,
    /// A helper operator.
    Helper,
}

#[derive(Debug, Error, PartialEq, Eq)]
enum CodegenSourceMapError {
    #[error(
        "invalid generated Rust line range {start_line}..={end_line}; line numbers are 1-indexed and start must not exceed end"
    )]
    InvalidLineRange { start_line: u32, end_line: u32 },
}

impl CodegenSourceMap {
    /// Create an empty source map for a generated Rust file.
    #[must_use]
    pub(crate) fn new(generated_file: impl Into<String>, tla_source: impl Into<String>) -> Self {
        Self {
            generated_file: generated_file.into(),
            tla_source: tla_source.into(),
            entries: Vec::new(),
        }
    }

    /// Record a source-mapping entry for a code-generated operator.
    pub(crate) fn add_entry(
        &mut self,
        tla_operator: impl Into<String>,
        kind: CodegenEntryKind,
        start_line: u32,
        end_line: u32,
    ) {
        validate_line_range(start_line, end_line)
            .expect("codegen source map entries must use a valid 1-indexed line range");

        self.entries.push(CodegenSourceMapEntry {
            tla_operator: tla_operator.into(),
            kind,
            rust_start_line: start_line,
            rust_end_line: end_line,
        });
    }

    /// Find the first entry for a TLA+ operator name.
    #[must_use]
    pub(crate) fn find_by_operator(&self, name: &str) -> Option<&CodegenSourceMapEntry> {
        self.entries.iter().find(|entry| entry.tla_operator == name)
    }

    /// Find all entries of a given kind in emission order.
    #[must_use]
    pub(crate) fn find_by_kind(&self, kind: CodegenEntryKind) -> Vec<&CodegenSourceMapEntry> {
        self.entries
            .iter()
            .filter(|entry| entry.kind == kind)
            .collect()
    }

    /// Format a trace-step annotation using this source map.
    #[must_use]
    pub(crate) fn annotate_action(&self, action_name: &str) -> Option<String> {
        let entry = self.find_by_operator(action_name)?;
        Some(format!(
            "{action_name} -> {}:{}",
            self.generated_file,
            format_line_range(entry.rust_start_line, entry.rust_end_line)
        ))
    }
}

/// String-backed output buffer that tracks the current 1-indexed line number.
///
/// This is intended for code generation paths that need both the emitted Rust
/// source and stable line numbers for source-map entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LineTracker {
    buffer: String,
    current_line: u32,
}

impl Default for LineTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl LineTracker {
    /// Create an empty line tracker positioned at line 1.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            buffer: String::new(),
            current_line: 1,
        }
    }

    /// Create an empty line tracker with preallocated capacity.
    #[must_use]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            buffer: String::with_capacity(capacity),
            current_line: 1,
        }
    }

    /// Append a string slice and update the tracked line number.
    pub(crate) fn push_str(&mut self, text: &str) {
        self.buffer.push_str(text);
        self.bump_lines(count_newlines(text));
    }

    /// Append a single character and update the tracked line number.
    pub(crate) fn push(&mut self, ch: char) {
        self.buffer.push(ch);
        if ch == '\n' {
            self.bump_lines(1);
        }
    }

    /// Return the current 1-indexed line number.
    #[must_use]
    pub(crate) const fn current_line(&self) -> u32 {
        self.current_line
    }

    /// Borrow the accumulated text.
    #[must_use]
    pub(crate) fn as_str(&self) -> &str {
        &self.buffer
    }

    /// Consume the tracker and return the accumulated text.
    #[must_use]
    pub(crate) fn into_string(self) -> String {
        self.buffer
    }

    fn bump_lines(&mut self, added_lines: u32) {
        self.current_line = self
            .current_line
            .checked_add(added_lines)
            .expect("generated Rust exceeded supported source-map line count");
    }
}

impl fmt::Write for LineTracker {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

fn validate_line_range(start_line: u32, end_line: u32) -> Result<(), CodegenSourceMapError> {
    if start_line == 0 || end_line == 0 || start_line > end_line {
        return Err(CodegenSourceMapError::InvalidLineRange {
            start_line,
            end_line,
        });
    }
    Ok(())
}

#[must_use]
fn format_line_range(start_line: u32, end_line: u32) -> String {
    if start_line == end_line {
        start_line.to_string()
    } else {
        format!("{start_line}-{end_line}")
    }
}

fn count_newlines(text: &str) -> u32 {
    u32::try_from(text.bytes().filter(|byte| *byte == b'\n').count())
        .expect("generated Rust exceeded supported source-map line count")
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use super::{CodegenEntryKind, CodegenSourceMap, LineTracker};

    fn sample_map() -> CodegenSourceMap {
        let mut map = CodegenSourceMap::new("generated/spec.rs", "specs/Mutex.tla");
        map.add_entry("MutexState", CodegenEntryKind::StateStruct, 1, 8);
        map.add_entry("Init", CodegenEntryKind::Init, 10, 18);
        map.add_entry("Next", CodegenEntryKind::Next, 20, 37);
        map.add_entry("InvMutualExclusion", CodegenEntryKind::Invariant, 39, 39);
        map.add_entry("HelperEnabled", CodegenEntryKind::Helper, 41, 44);
        map.add_entry("HelperApply", CodegenEntryKind::Helper, 46, 52);
        map
    }

    #[test]
    fn roundtrip_serialization() {
        let map = sample_map();

        let json = serde_json::to_string_pretty(&map).expect("source map should serialize");
        let decoded: CodegenSourceMap =
            serde_json::from_str(&json).expect("source map should deserialize");

        assert_eq!(decoded, map);
    }

    #[test]
    fn lookup_by_operator() {
        let map = sample_map();

        let entry = map
            .find_by_operator("Next")
            .expect("expected Next entry to exist");

        assert_eq!(entry.kind, CodegenEntryKind::Next);
        assert_eq!(entry.rust_start_line, 20);
        assert_eq!(entry.rust_end_line, 37);
        assert!(map.find_by_operator("Missing").is_none());
    }

    #[test]
    fn lookup_by_kind() {
        let map = sample_map();

        let helpers = map.find_by_kind(CodegenEntryKind::Helper);

        assert_eq!(helpers.len(), 2);
        assert_eq!(helpers[0].tla_operator, "HelperEnabled");
        assert_eq!(helpers[1].tla_operator, "HelperApply");
    }

    #[test]
    fn annotate_action() {
        let map = sample_map();

        assert_eq!(
            map.annotate_action("Init").as_deref(),
            Some("Init -> generated/spec.rs:10-18")
        );
        assert_eq!(
            map.annotate_action("InvMutualExclusion").as_deref(),
            Some("InvMutualExclusion -> generated/spec.rs:39")
        );
        assert_eq!(map.annotate_action("Missing"), None);
    }

    #[test]
    fn line_tracker_basic_tracking() {
        let mut tracker = LineTracker::with_capacity(64);

        assert_eq!(tracker.current_line(), 1);

        writeln!(&mut tracker, "fn main() {{").expect("write into String-backed tracker");
        assert_eq!(tracker.current_line(), 2);

        writeln!(&mut tracker, "    println!(\"hi\");").expect("write into String-backed tracker");
        assert_eq!(tracker.current_line(), 3);

        tracker.push('}');
        assert_eq!(tracker.current_line(), 3);

        tracker.push('\n');
        assert_eq!(tracker.current_line(), 4);

        assert_eq!(tracker.as_str(), "fn main() {\n    println!(\"hi\");\n}\n");
        assert_eq!(
            tracker.into_string(),
            "fn main() {\n    println!(\"hi\");\n}\n"
        );
    }
}
