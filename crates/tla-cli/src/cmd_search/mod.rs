// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 search` -- semantic pattern search across TLA+ specifications.
//!
//! Searches for operators, variables, constants, expression patterns, and
//! free-text content within `.tla` files. Recursively traverses directories,
//! parses TLA+ files for semantic search via `tla_core::parse` and
//! `tla_core::lower_main_module`, and falls back to line-by-line substring
//! matching for the `Pattern` kind.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::Serialize;
use tla_core::ast::{Module, Unit};
use tla_core::{lower_main_module, parse, FileId, SyntaxNode};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// What kind of TLA+ construct to search for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum, Serialize)]
pub(crate) enum SearchKind {
    /// Search for operator definitions by name.
    Operator,
    /// Search for VARIABLE declarations by name.
    Variable,
    /// Search for CONSTANT declarations by name.
    Constant,
    /// Search for a substring/pattern against raw source lines.
    Pattern,
    /// Search across all categories (operators, variables, constants, and lines).
    #[default]
    All,
}

/// Output format for search results.
#[derive(Debug, Clone, Copy, Default, clap::ValueEnum, Serialize)]
pub(crate) enum SearchOutputFormat {
    /// Human-readable output with colored match highlights (default).
    #[default]
    Human,
    /// Structured JSON output for tooling integration.
    Json,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the search command across all `.tla` files under `dir`.
///
/// `pattern` is a substring to search for. In `Pattern` and `All` modes it is
/// matched against each source line; in semantic modes (`Operator`, `Variable`,
/// `Constant`) it is matched against declaration names. When `ignore_case` is
/// true all comparisons are case-insensitive.
pub(crate) fn cmd_search(
    pattern: &str,
    paths: &[PathBuf],
    kind: SearchKind,
    format: SearchOutputFormat,
) -> Result<()> {
    let ignore_case = true;
    let mut files = Vec::new();
    for p in paths {
        if p.is_dir() {
            files.extend(collect_tla_files(p)?);
        } else if p.extension().is_some_and(|e| e == "tla") {
            files.push(p.clone());
        }
    }
    if files.is_empty() {
        match format {
            SearchOutputFormat::Human => {
                println!("No .tla files found in provided paths");
            }
            SearchOutputFormat::Json => {
                let report = SearchReport::new(pattern, kind, Vec::new(), 0);
                println!("{}", serde_json::to_string_pretty(&report)?);
            }
        }
        return Ok(());
    }

    let mut all_matches: Vec<SearchMatch> = Vec::new();

    for file_path in &files {
        let file_matches = search_file(file_path, pattern, kind, ignore_case, usize::MAX);
        all_matches.extend(file_matches);
    }

    let files_searched = files.len();
    match format {
        SearchOutputFormat::Human => print_human(pattern, kind, &all_matches),
        SearchOutputFormat::Json => print_json(pattern, kind, &all_matches, files_searched)?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

/// A single search match.
#[derive(Debug, Clone, Serialize)]
struct SearchMatch {
    /// Path to the file containing the match.
    file: String,
    /// 1-based line number.
    line: usize,
    /// 1-based column of the match start.
    column: usize,
    /// Full text of the matched source line (trimmed trailing whitespace).
    line_text: String,
    /// Category of the match.
    category: MatchCategory,
    /// The matched identifier or text fragment.
    matched_text: String,
}

/// What kind of construct was matched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
enum MatchCategory {
    Operator,
    Variable,
    Constant,
    Pattern,
}

/// Top-level JSON report.
#[derive(Debug, Serialize)]
struct SearchReport {
    pattern: String,
    kind: SearchKind,
    total_matches: usize,
    files_searched: usize,
    matches: Vec<SearchMatch>,
}

impl SearchReport {
    fn new(pattern: &str, kind: SearchKind, matches: Vec<SearchMatch>, files: usize) -> Self {
        let total_matches = matches.len();
        Self {
            pattern: pattern.to_string(),
            kind,
            total_matches,
            files_searched: files,
            matches,
        }
    }
}

// ---------------------------------------------------------------------------
// File collection
// ---------------------------------------------------------------------------

/// Recursively collect all `.tla` files under `root`.
/// If `root` is itself a `.tla` file, returns it as a single-element list.
fn collect_tla_files(root: &Path) -> Result<Vec<PathBuf>> {
    if root.is_file() {
        return if has_tla_extension(root) {
            Ok(vec![root.to_path_buf()])
        } else {
            Ok(Vec::new())
        };
    }
    let mut files = Vec::new();
    collect_tla_recursive(root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_tla_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .with_context(|| format!("read directory: {}", dir.display()))?;
    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_tla_recursive(&path, out)?;
        } else if has_tla_extension(&path) {
            out.push(path);
        }
    }
    Ok(())
}

fn has_tla_extension(p: &Path) -> bool {
    p.extension()
        .and_then(|e| e.to_str())
        .map_or(false, |e| e.eq_ignore_ascii_case("tla"))
}

// ---------------------------------------------------------------------------
// Per-file search
// ---------------------------------------------------------------------------

/// Search a single `.tla` file and return up to `limit` matches.
fn search_file(
    file: &Path,
    pattern: &str,
    kind: SearchKind,
    ignore_case: bool,
    limit: usize,
) -> Vec<SearchMatch> {
    let source = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    let file_str = file.display().to_string();
    let lines: Vec<&str> = source.lines().collect();
    let mut matches = Vec::new();

    // For semantic kinds, attempt to parse the TLA+ file.
    let module = if kind != SearchKind::Pattern {
        try_parse_module(&source)
    } else {
        None
    };

    if matches!(kind, SearchKind::Operator | SearchKind::All) {
        if let Some(ref m) = module {
            collect_operator_matches(m, &file_str, &lines, pattern, ignore_case, limit, &mut matches);
        }
    }
    if matches!(kind, SearchKind::Variable | SearchKind::All) {
        if let Some(ref m) = module {
            collect_variable_matches(m, &file_str, &lines, pattern, ignore_case, limit, &mut matches);
        }
    }
    if matches!(kind, SearchKind::Constant | SearchKind::All) {
        if let Some(ref m) = module {
            collect_constant_matches(m, &file_str, &lines, pattern, ignore_case, limit, &mut matches);
        }
    }
    if matches!(kind, SearchKind::Pattern | SearchKind::All) {
        let remaining = limit.saturating_sub(matches.len());
        collect_pattern_matches(&file_str, &lines, pattern, ignore_case, remaining, &mut matches);
    }

    // Deduplicate: same file + line + category should appear only once.
    matches.sort_by(|a, b| a.line.cmp(&b.line).then(a.column.cmp(&b.column)));
    matches.dedup_by(|a, b| a.file == b.file && a.line == b.line && a.category == b.category);
    matches.truncate(limit);
    matches
}

/// Attempt to parse and lower a TLA+ source. Returns `None` on any error.
fn try_parse_module(source: &str) -> Option<Module> {
    let parse_result = parse(source);
    if !parse_result.errors.is_empty() {
        return None;
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);
    let lower_result = lower_main_module(FileId(0), &tree, None);
    if !lower_result.errors.is_empty() {
        return None;
    }
    lower_result.module
}

// ---------------------------------------------------------------------------
// Semantic match collectors
// ---------------------------------------------------------------------------

fn collect_operator_matches(
    module: &Module,
    file: &str,
    lines: &[&str],
    pattern: &str,
    ignore_case: bool,
    limit: usize,
    out: &mut Vec<SearchMatch>,
) {
    for unit in &module.units {
        if out.len() >= limit {
            return;
        }
        if let Unit::Operator(op) = &unit.node {
            if name_matches(&op.name.node, pattern, ignore_case) {
                let (line, col) = span_to_line_col(op.name.span.start, lines);
                out.push(SearchMatch {
                    file: file.to_string(),
                    line,
                    column: col,
                    line_text: line_text_at(lines, line),
                    category: MatchCategory::Operator,
                    matched_text: op.name.node.clone(),
                });
            }
        }
    }
}

fn collect_variable_matches(
    module: &Module,
    file: &str,
    lines: &[&str],
    pattern: &str,
    ignore_case: bool,
    limit: usize,
    out: &mut Vec<SearchMatch>,
) {
    for unit in &module.units {
        if out.len() >= limit {
            return;
        }
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                if out.len() >= limit {
                    return;
                }
                if name_matches(&name.node, pattern, ignore_case) {
                    let (line, col) = span_to_line_col(name.span.start, lines);
                    out.push(SearchMatch {
                        file: file.to_string(),
                        line,
                        column: col,
                        line_text: line_text_at(lines, line),
                        category: MatchCategory::Variable,
                        matched_text: name.node.clone(),
                    });
                }
            }
        }
    }
}

fn collect_constant_matches(
    module: &Module,
    file: &str,
    lines: &[&str],
    pattern: &str,
    ignore_case: bool,
    limit: usize,
    out: &mut Vec<SearchMatch>,
) {
    for unit in &module.units {
        if out.len() >= limit {
            return;
        }
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                if out.len() >= limit {
                    return;
                }
                if name_matches(&decl.name.node, pattern, ignore_case) {
                    let (line, col) = span_to_line_col(decl.name.span.start, lines);
                    out.push(SearchMatch {
                        file: file.to_string(),
                        line,
                        column: col,
                        line_text: line_text_at(lines, line),
                        category: MatchCategory::Constant,
                        matched_text: decl.name.node.clone(),
                    });
                }
            }
        }
    }
}

/// Line-by-line substring search for pattern matches.
fn collect_pattern_matches(
    file: &str,
    lines: &[&str],
    pattern: &str,
    ignore_case: bool,
    limit: usize,
    out: &mut Vec<SearchMatch>,
) {
    let pattern_lower = pattern.to_lowercase();
    for (idx, line) in lines.iter().enumerate() {
        if out.len() >= limit {
            return;
        }
        let found = if ignore_case {
            line.to_lowercase().find(&pattern_lower)
        } else {
            line.find(pattern)
        };
        if let Some(col_offset) = found {
            // Extract the actual matched text from the line (preserving original case).
            let match_end = (col_offset + pattern.len()).min(line.len());
            let matched = &line[col_offset..match_end];
            out.push(SearchMatch {
                file: file.to_string(),
                line: idx + 1,
                column: col_offset + 1,
                line_text: line.trim_end().to_string(),
                category: MatchCategory::Pattern,
                matched_text: matched.to_string(),
            });
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Check whether `name` matches `pattern` as a substring.
fn name_matches(name: &str, pattern: &str, ignore_case: bool) -> bool {
    if ignore_case {
        name.to_lowercase().contains(&pattern.to_lowercase())
    } else {
        name.contains(pattern)
    }
}

/// Convert a byte offset into (1-based line, 1-based column).
fn span_to_line_col(offset: u32, lines: &[&str]) -> (usize, usize) {
    let offset = offset as usize;
    let mut cumulative = 0usize;
    for (idx, line) in lines.iter().enumerate() {
        let line_end = cumulative + line.len() + 1; // +1 for newline
        if offset < line_end {
            return (idx + 1, offset.saturating_sub(cumulative) + 1);
        }
        cumulative = line_end;
    }
    (lines.len().max(1), 1)
}

/// Get the trimmed text of a 1-based line number.
fn line_text_at(lines: &[&str], line: usize) -> String {
    lines
        .get(line.saturating_sub(1))
        .unwrap_or(&"")
        .trim_end()
        .to_string()
}

/// Highlight the first occurrence of `needle` in `haystack` with ANSI bold red.
fn highlight_match(haystack: &str, needle: &str) -> String {
    if needle.is_empty() {
        return haystack.to_string();
    }
    let hay_lower = haystack.to_lowercase();
    let needle_lower = needle.to_lowercase();
    if let Some(idx) = hay_lower.find(&needle_lower) {
        let end = (idx + needle.len()).min(haystack.len());
        let actual = &haystack[idx..end];
        format!(
            "{}\x1b[1;31m{}\x1b[0m{}",
            &haystack[..idx],
            actual,
            &haystack[end..],
        )
    } else {
        haystack.to_string()
    }
}

fn count_unique_files(matches: &[SearchMatch]) -> usize {
    let mut files: Vec<&str> = matches.iter().map(|m| m.file.as_str()).collect();
    files.sort_unstable();
    files.dedup();
    files.len()
}

// ---------------------------------------------------------------------------
// Output: Human
// ---------------------------------------------------------------------------

fn print_human(pattern: &str, kind: SearchKind, matches: &[SearchMatch]) {
    if matches.is_empty() {
        println!("No matches found for {kind:?} pattern: {pattern}");
        return;
    }

    println!(
        "Found {} match{} for {kind:?} pattern: {pattern}",
        matches.len(),
        if matches.len() == 1 { "" } else { "es" },
    );
    println!();

    let mut current_file = "";
    for m in matches {
        if m.file != current_file {
            if !current_file.is_empty() {
                println!();
            }
            println!("\x1b[1;35m{}\x1b[0m", m.file);
            current_file = &m.file;
        }

        let tag = match m.category {
            MatchCategory::Operator => "\x1b[1;34m[OP]\x1b[0m",
            MatchCategory::Variable => "\x1b[1;32m[VAR]\x1b[0m",
            MatchCategory::Constant => "\x1b[1;33m[CONST]\x1b[0m",
            MatchCategory::Pattern => "\x1b[1;36m[PAT]\x1b[0m",
        };

        let highlighted = highlight_match(&m.line_text, &m.matched_text);
        println!("  \x1b[2m{:>5}:{:<3}\x1b[0m {tag} {highlighted}", m.line, m.column);
    }

    let n_files = count_unique_files(matches);
    println!();
    println!(
        "--- {} match{} in {} file{} ---",
        matches.len(),
        if matches.len() == 1 { "" } else { "es" },
        n_files,
        if n_files == 1 { "" } else { "s" },
    );
}

// ---------------------------------------------------------------------------
// Output: JSON
// ---------------------------------------------------------------------------

fn print_json(
    pattern: &str,
    kind: SearchKind,
    matches: &[SearchMatch],
    files_searched: usize,
) -> Result<()> {
    let report = SearchReport::new(pattern, kind, matches.to_vec(), files_searched);
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;

    fn make_tla_source() -> &'static str {
        r#"---- MODULE TestSearch ----
EXTENDS Naturals
CONSTANT N, MaxVal
VARIABLE x, y, counter

Init == x = 0 /\ y = 0 /\ counter = 0
Next == x' = x + 1 /\ y' = y /\ counter' = counter + 1
TypeOK == x \in Nat /\ y \in Nat /\ counter \in 0..N
Helper(a, b) == a + b
===="#
    }

    fn parse_test_module() -> Module {
        let source = make_tla_source();
        let result = parse(source);
        assert!(result.errors.is_empty(), "parse errors: {:?}", result.errors);
        let tree = SyntaxNode::new_root(result.green_node);
        let lr = lower_main_module(FileId(0), &tree, None);
        assert!(lr.errors.is_empty(), "lower errors: {:?}", lr.errors);
        lr.module.expect("no module produced")
    }

    // -- name_matches ---------------------------------------------------------

    #[test]
    fn test_name_matches_case_sensitive() {
        assert!(name_matches("Init", "Init", false));
        assert!(name_matches("Init", "In", false));
        assert!(!name_matches("Init", "init", false));
    }

    #[test]
    fn test_name_matches_case_insensitive() {
        assert!(name_matches("Init", "init", true));
        assert!(name_matches("TypeOK", "typeok", true));
        assert!(!name_matches("Init", "Next", true));
    }

    // -- collect_operator_matches ---------------------------------------------

    #[test]
    fn test_collect_operator_matches_exact() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_operator_matches(&module, "t.tla", &lines, "Init", false, 100, &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].matched_text, "Init");
        assert_eq!(out[0].category, MatchCategory::Operator);
    }

    #[test]
    fn test_collect_operator_matches_partial() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_operator_matches(&module, "t.tla", &lines, "Help", false, 100, &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].matched_text, "Helper");
    }

    #[test]
    fn test_collect_operator_matches_ignore_case() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_operator_matches(&module, "t.tla", &lines, "init", true, 100, &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].matched_text, "Init");
    }

    // -- collect_variable_matches ---------------------------------------------

    #[test]
    fn test_collect_variable_matches_found() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_variable_matches(&module, "t.tla", &lines, "counter", false, 100, &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].matched_text, "counter");
        assert_eq!(out[0].category, MatchCategory::Variable);
    }

    #[test]
    fn test_collect_variable_matches_no_hit() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_variable_matches(&module, "t.tla", &lines, "zzz", false, 100, &mut out);
        assert!(out.is_empty());
    }

    // -- collect_constant_matches ---------------------------------------------

    #[test]
    fn test_collect_constant_matches_found() {
        let module = parse_test_module();
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_constant_matches(&module, "t.tla", &lines, "Max", false, 100, &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].matched_text, "MaxVal");
        assert_eq!(out[0].category, MatchCategory::Constant);
    }

    // -- collect_pattern_matches ----------------------------------------------

    #[test]
    fn test_collect_pattern_matches_multi_line() {
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_pattern_matches("t.tla", &lines, "counter", false, 100, &mut out);
        assert!(out.len() >= 3, "expected >=3 matches, got {}", out.len());
        assert!(out.iter().all(|m| m.category == MatchCategory::Pattern));
    }

    #[test]
    fn test_collect_pattern_matches_ignore_case() {
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_pattern_matches("t.tla", &lines, "COUNTER", true, 100, &mut out);
        assert!(out.len() >= 3, "case-insensitive should still match");
    }

    #[test]
    fn test_collect_pattern_matches_respects_limit() {
        let source = make_tla_source();
        let lines: Vec<&str> = source.lines().collect();
        let mut out = Vec::new();
        collect_pattern_matches("t.tla", &lines, "=", false, 2, &mut out);
        assert_eq!(out.len(), 2);
    }

    // -- highlight_match ------------------------------------------------------

    #[test]
    fn test_highlight_match_present() {
        let result = highlight_match("Init == x = 0", "Init");
        assert!(result.contains("\x1b[1;31mInit\x1b[0m"));
    }

    #[test]
    fn test_highlight_match_absent() {
        assert_eq!(highlight_match("Init == x = 0", "zzz"), "Init == x = 0");
    }

    #[test]
    fn test_highlight_match_empty() {
        assert_eq!(highlight_match("Init == x = 0", ""), "Init == x = 0");
    }

    // -- span_to_line_col -----------------------------------------------------

    #[test]
    fn test_span_to_line_col_first_line() {
        let lines = vec!["---- MODULE M ----", "VARIABLE x", "Init == x = 0"];
        assert_eq!(span_to_line_col(0, &lines), (1, 1));
        assert_eq!(span_to_line_col(5, &lines), (1, 6));
    }

    #[test]
    fn test_span_to_line_col_second_line() {
        let lines = vec!["---- MODULE M ----", "VARIABLE x"];
        // line 1 = 18 chars + 1 newline = 19 bytes => line 2 starts at 19.
        assert_eq!(span_to_line_col(19, &lines), (2, 1));
    }

    // -- has_tla_extension ----------------------------------------------------

    #[test]
    fn test_has_tla_extension_positive() {
        assert!(has_tla_extension(Path::new("foo.tla")));
        assert!(has_tla_extension(Path::new("foo.TLA")));
    }

    #[test]
    fn test_has_tla_extension_negative() {
        assert!(!has_tla_extension(Path::new("foo.cfg")));
        assert!(!has_tla_extension(Path::new("foo")));
    }

    // -- count_unique_files ---------------------------------------------------

    #[test]
    fn test_count_unique_files() {
        let mk = |f: &str| SearchMatch {
            file: f.to_string(),
            line: 1,
            column: 1,
            line_text: String::new(),
            category: MatchCategory::Operator,
            matched_text: String::new(),
        };
        assert_eq!(count_unique_files(&[mk("a.tla"), mk("a.tla"), mk("b.tla")]), 2);
    }

    // -- collect_tla_files ----------------------------------------------------

    #[test]
    fn test_collect_tla_files_single_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let p = dir.path().join("Spec.tla");
        std::fs::write(&p, "---- MODULE Spec ----\n====").expect("write");
        assert_eq!(collect_tla_files(&p).unwrap().len(), 1);
    }

    #[test]
    fn test_collect_tla_files_directory() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("A.tla"), "---- MODULE A ----\n====").expect("write");
        std::fs::write(dir.path().join("B.tla"), "---- MODULE B ----\n====").expect("write");
        std::fs::write(dir.path().join("C.cfg"), "INIT Init").expect("write");
        assert_eq!(collect_tla_files(dir.path()).unwrap().len(), 2);
    }

    #[test]
    fn test_collect_tla_files_recursive() {
        let dir = tempfile::tempdir().expect("tempdir");
        let sub = dir.path().join("sub");
        std::fs::create_dir(&sub).expect("mkdir");
        std::fs::write(dir.path().join("Top.tla"), "---- MODULE Top ----\n====").expect("write");
        std::fs::write(sub.join("N.tla"), "---- MODULE N ----\n====").expect("write");
        assert_eq!(collect_tla_files(dir.path()).unwrap().len(), 2);
    }

    // -- search_file integration ----------------------------------------------

    #[test]
    fn test_search_file_all_kind() {
        let dir = tempfile::tempdir().expect("tempdir");
        let p = dir.path().join("Test.tla");
        {
            let mut f = std::fs::File::create(&p).expect("create");
            write!(f, "{}", make_tla_source()).expect("write");
        }
        let matches = search_file(&p, "Init", SearchKind::All, false, 100);
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|m| m.category == MatchCategory::Operator));
    }

    #[test]
    fn test_search_file_pattern_only() {
        let dir = tempfile::tempdir().expect("tempdir");
        let p = dir.path().join("Test.tla");
        {
            let mut f = std::fs::File::create(&p).expect("create");
            write!(f, "{}", make_tla_source()).expect("write");
        }
        let matches = search_file(&p, "\\in Nat", SearchKind::Pattern, false, 100);
        assert!(!matches.is_empty());
        assert!(matches.iter().all(|m| m.category == MatchCategory::Pattern));
    }

    // -- JSON serialization ---------------------------------------------------

    #[test]
    fn test_search_report_json_roundtrip() {
        let report = SearchReport::new(
            "Init",
            SearchKind::Operator,
            vec![SearchMatch {
                file: "Spec.tla".to_string(),
                line: 3,
                column: 1,
                line_text: "Init == x = 0".to_string(),
                category: MatchCategory::Operator,
                matched_text: "Init".to_string(),
            }],
            1,
        );
        let json = serde_json::to_string_pretty(&report).expect("serialize");
        assert!(json.contains("\"pattern\": \"Init\""));
        assert!(json.contains("\"total_matches\": 1"));
        assert!(json.contains("\"category\": \"operator\""));
    }

    // -- cmd_search integration -----------------------------------------------

    #[test]
    fn test_cmd_search_empty_dir() {
        let dir = tempfile::tempdir().expect("tempdir");
        let r = cmd_search("Init", &[dir.path().to_path_buf()], SearchKind::All, SearchOutputFormat::Human);
        assert!(r.is_ok());
    }

    #[test]
    fn test_cmd_search_with_pattern() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("T.tla"), make_tla_source()).expect("write");
        let r = cmd_search("=", &[dir.path().to_path_buf()], SearchKind::Pattern, SearchOutputFormat::Json);
        assert!(r.is_ok());
    }

    #[test]
    fn test_cmd_search_operator_kind() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("T.tla"), make_tla_source()).expect("write");
        let r = cmd_search("Init", &[dir.path().to_path_buf()], SearchKind::Operator, SearchOutputFormat::Human);
        assert!(r.is_ok());
    }
}
