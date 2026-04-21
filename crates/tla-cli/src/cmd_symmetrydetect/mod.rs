// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 symmetry-detect` — detect potential symmetry in a spec.
//!
//! Analyzes constants, variables, and operators to identify potential
//! symmetry sets that could be used with the SYMMETRY keyword to
//! reduce the state space.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the symmetry-detect command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SymmetrydetectOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect potential symmetry in a TLA+ spec.
pub(crate) fn cmd_symmetrydetect(
    file: &Path,
    config: Option<&Path>,
    format: SymmetrydetectOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;

    let config_path_buf = match config {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let parsed_config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf)
            .with_context(|| format!("read config {}", config_path_buf.display()))?;
        Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        Config::default()
    };

    // --- Analyze for symmetry candidates -----------------------------------

    let mut const_names: Vec<String> = Vec::new();
    let mut var_names: Vec<String> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => {
                for d in decls {
                    const_names.push(d.name.node.clone());
                }
            }
            Unit::Variable(decls) => {
                for d in decls {
                    var_names.push(d.node.clone());
                }
            }
            _ => {}
        }
    }

    let mut candidates: Vec<SymmetryCandidate> = Vec::new();

    // Check constants assigned to model value sets in config.
    for (name, val) in &parsed_config.constants {
        let val_str = format!("{val}");
        // Look for set-valued constants (e.g., {m1, m2, m3}).
        if val_str.starts_with('{') && val_str.ends_with('}') {
            let inner = &val_str[1..val_str.len() - 1];
            let elements: Vec<&str> = inner.split(',').map(|s| s.trim()).collect();
            if elements.len() >= 2 {
                // Heuristic: if all elements have the same prefix, likely symmetric.
                let first_prefix = elements[0].chars().take_while(|c| c.is_alphabetic()).collect::<String>();
                let all_same_prefix = elements.iter().all(|e| {
                    let prefix: String = e.chars().take_while(|c| c.is_alphabetic()).collect();
                    prefix == first_prefix
                });
                if all_same_prefix && !first_prefix.is_empty() {
                    candidates.push(SymmetryCandidate {
                        constant: name.clone(),
                        elements: elements.iter().map(|s| s.to_string()).collect(),
                        confidence: "high".to_string(),
                        reason: format!("model value set with uniform prefix '{first_prefix}'"),
                    });
                } else if elements.len() >= 2 {
                    candidates.push(SymmetryCandidate {
                        constant: name.clone(),
                        elements: elements.iter().map(|s| s.to_string()).collect(),
                        confidence: "medium".to_string(),
                        reason: "set-valued constant with multiple elements".to_string(),
                    });
                }
            }
        }
    }

    // Heuristic: constants named Node, Proc, Server, etc. are often symmetric.
    let sym_keywords = ["node", "proc", "server", "client", "acceptor", "replica", "worker"];
    for name in &const_names {
        let lower = name.to_lowercase();
        if sym_keywords.iter().any(|k| lower.contains(k)) {
            if !candidates.iter().any(|c| c.constant == *name) {
                candidates.push(SymmetryCandidate {
                    constant: name.clone(),
                    elements: Vec::new(),
                    confidence: "low".to_string(),
                    reason: format!("name pattern suggests process/node set"),
                });
            }
        }
    }

    // Check if SYMMETRY is already configured.
    let has_symmetry = parsed_config.symmetry.is_some();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        SymmetrydetectOutputFormat::Human => {
            println!("symmetry-detect: {}", file.display());
            println!("  existing SYMMETRY config: {}", if has_symmetry { "yes" } else { "no" });
            println!();
            if candidates.is_empty() {
                println!("  No symmetry candidates detected.");
            } else {
                println!("  Symmetry candidates ({}):", candidates.len());
                for c in &candidates {
                    println!("    {} (confidence: {})", c.constant, c.confidence);
                    println!("      reason: {}", c.reason);
                    if !c.elements.is_empty() {
                        println!("      elements: {{{}}}", c.elements.join(", "));
                    }
                }
                if !has_symmetry {
                    println!();
                    println!("  Suggested .cfg addition:");
                    for c in &candidates {
                        if c.confidence == "high" {
                            println!("    SYMMETRY {}", c.constant);
                        }
                    }
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        SymmetrydetectOutputFormat::Json => {
            let candidates_json: Vec<serde_json::Value> = candidates
                .iter()
                .map(|c| {
                    serde_json::json!({
                        "constant": c.constant,
                        "elements": c.elements,
                        "confidence": c.confidence,
                        "reason": c.reason,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "has_existing_symmetry": has_symmetry,
                "candidates": candidates_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

struct SymmetryCandidate {
    constant: String,
    elements: Vec<String>,
    confidence: String,
    reason: String,
}
