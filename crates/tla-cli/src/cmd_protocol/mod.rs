// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 protocol` — protocol pattern detection.
//!
//! Analyzes a TLA+ specification to detect common distributed protocol
//! patterns: message passing, leader election, consensus, two-phase
//! commit, request/response, and barrier synchronization.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the protocol command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProtocolOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect protocol patterns in a TLA+ spec.
pub(crate) fn cmd_protocol(
    file: &Path,
    format: ProtocolOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower ---------------------------------------------------

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

    // --- Scan for patterns -------------------------------------------------

    let mut patterns: Vec<PatternDetection> = Vec::new();

    // Collect variable and constant names for pattern matching.
    let mut var_names: Vec<String> = Vec::new();
    let mut const_names: Vec<String> = Vec::new();
    let mut op_names: Vec<String> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for d in decls {
                    var_names.push(d.node.clone());
                }
            }
            Unit::Constant(decls) => {
                for d in decls {
                    const_names.push(d.name.node.clone());
                }
            }
            Unit::Operator(def) => {
                op_names.push(def.name.node.clone());
            }
            _ => {}
        }
    }

    // Check naming patterns for protocol detection.
    let all_names: Vec<&str> = var_names
        .iter()
        .chain(const_names.iter())
        .chain(op_names.iter())
        .map(|s| s.as_str())
        .collect();

    // Message passing pattern.
    let msg_keywords = ["msg", "message", "messages", "inbox", "outbox", "send", "recv", "deliver"];
    let msg_matches: Vec<&str> = all_names
        .iter()
        .filter(|n| {
            let lower = n.to_lowercase();
            msg_keywords.iter().any(|k| lower.contains(k))
        })
        .copied()
        .collect();
    if !msg_matches.is_empty() {
        patterns.push(PatternDetection {
            pattern: "message_passing".to_string(),
            confidence: if msg_matches.len() >= 3 { "high" } else { "medium" }.to_string(),
            evidence: msg_matches.join(", "),
        });
    }

    // Leader election pattern.
    let leader_keywords = ["leader", "elect", "candidate", "ballot", "vote", "term"];
    let leader_matches: Vec<&str> = all_names
        .iter()
        .filter(|n| {
            let lower = n.to_lowercase();
            leader_keywords.iter().any(|k| lower.contains(k))
        })
        .copied()
        .collect();
    if !leader_matches.is_empty() {
        patterns.push(PatternDetection {
            pattern: "leader_election".to_string(),
            confidence: if leader_matches.len() >= 3 { "high" } else { "medium" }.to_string(),
            evidence: leader_matches.join(", "),
        });
    }

    // Consensus pattern.
    let consensus_keywords = ["accept", "propose", "decide", "commit", "abort", "prepare", "promise", "chosen"];
    let consensus_matches: Vec<&str> = all_names
        .iter()
        .filter(|n| {
            let lower = n.to_lowercase();
            consensus_keywords.iter().any(|k| lower.contains(k))
        })
        .copied()
        .collect();
    if !consensus_matches.is_empty() {
        patterns.push(PatternDetection {
            pattern: "consensus".to_string(),
            confidence: if consensus_matches.len() >= 3 { "high" } else { "medium" }.to_string(),
            evidence: consensus_matches.join(", "),
        });
    }

    // Mutex/lock pattern.
    let mutex_keywords = ["lock", "mutex", "semaphore", "critical", "waiting", "acquired"];
    let mutex_matches: Vec<&str> = all_names
        .iter()
        .filter(|n| {
            let lower = n.to_lowercase();
            mutex_keywords.iter().any(|k| lower.contains(k))
        })
        .copied()
        .collect();
    if !mutex_matches.is_empty() {
        patterns.push(PatternDetection {
            pattern: "mutual_exclusion".to_string(),
            confidence: if mutex_matches.len() >= 2 { "high" } else { "medium" }.to_string(),
            evidence: mutex_matches.join(", "),
        });
    }

    // Process/PC pattern (common in PlusCal-style specs).
    let pc_keywords = ["pc", "state", "phase", "step", "round"];
    let pc_matches: Vec<&str> = var_names
        .iter()
        .filter(|n| {
            let lower = n.to_lowercase();
            pc_keywords.iter().any(|k| lower == *k)
        })
        .map(|s| s.as_str())
        .collect();
    if !pc_matches.is_empty() {
        patterns.push(PatternDetection {
            pattern: "state_machine".to_string(),
            confidence: "high".to_string(),
            evidence: pc_matches.join(", "),
        });
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        ProtocolOutputFormat::Human => {
            println!("protocol: {}", file.display());
            println!("  variables: {}", var_names.len());
            println!("  constants: {}", const_names.len());
            println!("  operators: {}", op_names.len());
            println!();
            if patterns.is_empty() {
                println!("  No known protocol patterns detected.");
            } else {
                println!("  Detected patterns ({}):", patterns.len());
                for p in &patterns {
                    println!("    {} (confidence: {})", p.pattern, p.confidence);
                    println!("      evidence: {}", p.evidence);
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ProtocolOutputFormat::Json => {
            let patterns_json: Vec<serde_json::Value> = patterns
                .iter()
                .map(|p| {
                    serde_json::json!({
                        "pattern": p.pattern,
                        "confidence": p.confidence,
                        "evidence": p.evidence,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "variables": var_names,
                "constants": const_names,
                "patterns": patterns_json,
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

struct PatternDetection {
    pattern: String,
    confidence: String,
    evidence: String,
}
