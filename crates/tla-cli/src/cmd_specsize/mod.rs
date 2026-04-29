// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 spec-size` — specification size metrics.
//!
//! Reports line counts, character counts, and structural size
//! metrics for a TLA+ specification.

use std::path::Path;
use std::time::Instant;

use anyhow::Result;

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the spec-size command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpecsizeOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Report specification size metrics.
pub(crate) fn cmd_specsize(file: &Path, format: SpecsizeOutputFormat) -> Result<()> {
    let start = Instant::now();

    let source = read_source(file)?;

    let total_lines = source.lines().count();
    let blank_lines = source.lines().filter(|l| l.trim().is_empty()).count();
    let comment_lines = source
        .lines()
        .filter(|l| {
            let trimmed = l.trim();
            trimmed.starts_with("\\*") || trimmed.starts_with("(*")
        })
        .count();
    let code_lines = total_lines - blank_lines - comment_lines;
    let total_chars = source.len();
    let non_ws_chars = source.chars().filter(|c| !c.is_whitespace()).count();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        SpecsizeOutputFormat::Human => {
            println!("spec-size: {}", file.display());
            println!("  total lines:    {total_lines}");
            println!("  code lines:     {code_lines}");
            println!("  blank lines:    {blank_lines}");
            println!("  comment lines:  {comment_lines}");
            println!("  total chars:    {total_chars}");
            println!("  non-ws chars:   {non_ws_chars}");
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        SpecsizeOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total_lines": total_lines,
                "code_lines": code_lines,
                "blank_lines": blank_lines,
                "comment_lines": comment_lines,
                "total_chars": total_chars,
                "non_ws_chars": non_ws_chars,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
