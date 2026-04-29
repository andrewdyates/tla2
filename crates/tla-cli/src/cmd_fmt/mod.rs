// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 fmt` — format TLA+ source files with consistent style.
//!
//! Parses TLA+ source into an AST, then re-emits it through the width-aware
//! `TlaFormatter` from `tla-core`. Supports four modes:
//!
//! - **Default (stdout)**: prints formatted output.
//! - **Write (`--write`)**: overwrites the input file in place.
//! - **Check (`--check`)**: exits 0 if already formatted, 1 if changes needed.
//! - **Diff (`--diff`)**: shows a unified diff of what would change.

mod diff;

use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, FormatConfig, TlaFormatter};

use crate::helpers::{parse_or_report, read_source};

/// Configuration for the `fmt` subcommand, extracted from CLI args.
pub(crate) struct FmtConfig {
    /// TLA+ source file(s) to format. Use `["-"]` for stdin.
    pub files: Vec<PathBuf>,
    /// Write formatted output back to the source file (in place).
    pub write: bool,
    /// Number of spaces per indentation level.
    pub indent: usize,
    /// Target maximum line width before breaking expressions.
    pub width: usize,
    /// Check mode: exit 1 if any file would be reformatted.
    pub check: bool,
    /// Diff mode: show unified diff of what would change.
    pub diff: bool,
}

/// Entry point for `tla2 fmt`.
pub(crate) fn cmd_fmt(config: FmtConfig) -> Result<()> {
    if config.files.is_empty() {
        bail!("no input files specified");
    }

    let fmt_config = FormatConfig::default()
        .with_indent_width(config.indent)
        .with_max_width(config.width);
    let formatter = TlaFormatter::new(fmt_config);

    let mut any_unformatted = false;

    for file in &config.files {
        let result = format_one_file(file, &formatter, &config)?;
        if result == FormatResult::Changed {
            any_unformatted = true;
        }
    }

    if config.check && any_unformatted {
        // In check mode, a non-zero exit signals "needs formatting"
        std::process::exit(1);
    }

    Ok(())
}

/// Result of formatting a single file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatResult {
    /// The file content is already canonical.
    Unchanged,
    /// The file content differs from the canonical form.
    Changed,
}

/// Format a single file and emit output according to the selected mode.
fn format_one_file(
    file: &Path,
    formatter: &TlaFormatter,
    config: &FmtConfig,
) -> Result<FormatResult> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "{}: lowering failed with {} error(s)",
            file.display(),
            result.errors.len()
        );
    }
    let module = result
        .module
        .ok_or_else(|| anyhow::anyhow!("{}: lowering produced no module", file.display()))?;

    let formatted = formatter.format_module(&module);

    if formatted == source {
        if config.write {
            eprintln!("unchanged: {}", file.display());
        }
        // In default (stdout) mode with unchanged content, still print it
        if !config.check && !config.write && !config.diff {
            print!("{}", formatted);
        }
        return Ok(FormatResult::Unchanged);
    }

    // Content differs from canonical form
    if config.check {
        // Report the file that needs formatting; caller handles exit code.
        eprintln!("{}: would be reformatted", file.display());
        return Ok(FormatResult::Changed);
    }

    if config.diff {
        let file_label = file.display().to_string();
        let diff_output = diff::unified_diff(&source, &formatted, &file_label);
        print!("{}", diff_output);
        return Ok(FormatResult::Changed);
    }

    if config.write {
        if file.as_os_str() == "-" {
            bail!("cannot use --write with stdin");
        }
        std::fs::write(file, &formatted).with_context(|| format!("write {}", file.display()))?;
        eprintln!("formatted: {}", file.display());
    } else {
        // Default: print to stdout
        print!("{}", formatted);
    }

    Ok(FormatResult::Changed)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_result_enum() {
        assert_eq!(FormatResult::Unchanged, FormatResult::Unchanged);
        assert_ne!(FormatResult::Changed, FormatResult::Unchanged);
    }
}
