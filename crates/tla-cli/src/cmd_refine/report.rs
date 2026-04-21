// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Output formatting for refinement check results.
//!
//! Supports two output formats:
//! - **Human**: colorful terminal output with violation details and traces.
//! - **JSON**: structured output suitable for tooling integration.

use std::path::Path;

use anyhow::{Context, Result};
use serde::Serialize;

use super::mapping::{MappingSource, RefinementMapping};
use super::types::{RefineResult, RefineStatistics, RefinementViolation, ViolationKind};

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

/// Print a human-readable refinement check report to stdout.
pub(super) fn print_human_report(
    impl_file: &Path,
    abstract_file: &Path,
    mapping: &RefinementMapping,
    result: &RefineResult,
    stats: &RefineStatistics,
) {
    println!("=== Refinement Check ===");
    println!();
    println!("Implementation: {}", impl_file.display());
    println!("Abstract spec:  {}", abstract_file.display());
    println!();

    // Mapping summary.
    print_mapping_summary(mapping);
    println!();

    // Result header.
    if result.passed {
        println!("Result: PASSED");
        println!();
        println!(
            "The implementation refines the abstract specification through the \
             given mapping. Every implementation behavior, when projected through \
             the refinement mapping, is a valid abstract behavior."
        );
    } else {
        println!("Result: FAILED ({} violation(s))", result.violations.len());
        println!();
        print_violations(&result.violations);
    }

    println!();
    print_statistics(stats);
}

/// Print the refinement mapping in human-readable form.
fn print_mapping_summary(mapping: &RefinementMapping) {
    let source_label = match mapping.source {
        MappingSource::File => "from file",
        MappingSource::Auto => "auto-inferred",
    };

    println!("Refinement mapping ({}, {} entries):", source_label, mapping.entries.len());
    if mapping.entries.is_empty() {
        println!("  (no entries)");
    } else {
        for entry in &mapping.entries {
            let tag = if entry.auto_inferred { " [auto]" } else { "" };
            if entry.impl_var == entry.abstract_var {
                println!("  {} (identity){}", entry.impl_var, tag);
            } else {
                println!("  {} |-> {}{}", entry.impl_var, entry.abstract_var, tag);
            }
        }
    }
}

/// Print violation details.
fn print_violations(violations: &[RefinementViolation]) {
    for (i, violation) in violations.iter().enumerate() {
        println!("--- Violation {} ---", i + 1);
        println!("Kind: {}", violation_kind_label(violation.kind));
        println!("Description: {}", violation.description);

        if let Some(ref state) = violation.impl_state {
            println!("Implementation state:");
            for (var, val) in state {
                println!("  {} = {}", var, val);
            }
        }

        if let Some(ref abs_state) = violation.mapped_abstract_state {
            println!("Mapped abstract state:");
            for (var, val) in abs_state {
                println!("  {} = {}", var, val);
            }
        }

        if !violation.trace.is_empty() {
            println!("Trace ({} steps):", violation.trace.len());
            for step in &violation.trace {
                let stutter_tag = if step.is_stuttering {
                    " [stuttering]"
                } else {
                    ""
                };
                println!("  Step {}{}", step.index, stutter_tag);
                for (var, val) in &step.state {
                    println!("    {} = {}", var, val);
                }
                if let Some(ref abs_state) = step.abstract_state {
                    println!("    -- mapped abstract --");
                    for (var, val) in abs_state {
                        println!("    {} = {}", var, val);
                    }
                }
            }
        }

        if let Some(idx) = violation.step_index {
            println!("At step index: {}", idx);
        }

        println!();
    }
}

/// Print statistics summary.
fn print_statistics(stats: &RefineStatistics) {
    println!("--- Statistics ---");
    println!("Implementation states explored: {}", stats.impl_states_explored);
    println!(
        "Implementation transitions explored: {}",
        stats.impl_transitions_explored
    );
    println!("Violations found: {}", stats.violations_found);
    println!("Mapping entries: {}", stats.mapping_entries);
    if !stats.unmapped_variables.is_empty() {
        println!(
            "Unmapped abstract variables: {}",
            stats.unmapped_variables.join(", ")
        );
    }
    println!("Elapsed: {:.3}s", stats.elapsed_secs);
}

/// Human label for violation kinds.
fn violation_kind_label(kind: ViolationKind) -> &'static str {
    match kind {
        ViolationKind::UnmappedVariables => "Unmapped Variables",
        ViolationKind::InitRefinement => "Init Refinement Violation",
        ViolationKind::TransitionRefinement => "Transition Refinement Violation",
        ViolationKind::InvariantViolation => "Invariant Violation",
        ViolationKind::StructuralError => "Structural Error",
        ViolationKind::MappingError => "Mapping Error",
    }
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

/// Structured JSON output for tooling integration.
#[derive(Debug, Serialize)]
struct JsonReport<'a> {
    command: &'static str,
    impl_file: String,
    abstract_file: String,
    mapping: JsonMappingInfo<'a>,
    result: JsonResultInfo<'a>,
    statistics: &'a RefineStatistics,
}

#[derive(Debug, Serialize)]
struct JsonMappingInfo<'a> {
    source: &'static str,
    entries: &'a [super::mapping::MappingEntry],
}

#[derive(Debug, Serialize)]
struct JsonResultInfo<'a> {
    passed: bool,
    violations: &'a [RefinementViolation],
}

/// Print a JSON refinement check report to stdout.
pub(super) fn print_json_report(
    impl_file: &Path,
    abstract_file: &Path,
    mapping: &RefinementMapping,
    result: &RefineResult,
    stats: &RefineStatistics,
) -> Result<()> {
    let source_label = match mapping.source {
        MappingSource::File => "file",
        MappingSource::Auto => "auto",
    };

    let report = JsonReport {
        command: "refine",
        impl_file: impl_file.display().to_string(),
        abstract_file: abstract_file.display().to_string(),
        mapping: JsonMappingInfo {
            source: source_label,
            entries: &mapping.entries,
        },
        result: JsonResultInfo {
            passed: result.passed,
            violations: &result.violations,
        },
        statistics: stats,
    };

    let json = serde_json::to_string_pretty(&report)
        .context("failed to serialize refinement report to JSON")?;
    println!("{json}");
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::mapping::MappingEntry;

    #[test]
    fn test_violation_kind_labels() {
        assert_eq!(
            violation_kind_label(ViolationKind::UnmappedVariables),
            "Unmapped Variables"
        );
        assert_eq!(
            violation_kind_label(ViolationKind::TransitionRefinement),
            "Transition Refinement Violation"
        );
        assert_eq!(
            violation_kind_label(ViolationKind::StructuralError),
            "Structural Error"
        );
    }

    #[test]
    fn test_json_serialization() {
        let stats = RefineStatistics {
            impl_states_explored: 10,
            impl_transitions_explored: 25,
            violations_found: 0,
            elapsed_secs: 0.123,
            mapping_entries: 3,
            unmapped_variables: vec![],
        };

        let result = RefineResult {
            passed: true,
            violations: vec![],
            states_explored: 10,
            transitions_explored: 25,
        };

        let mapping = RefinementMapping {
            entries: vec![MappingEntry {
                impl_var: "x".to_string(),
                abstract_var: "x".to_string(),
                auto_inferred: true,
            }],
            source: MappingSource::Auto,
        };

        let report = JsonReport {
            command: "refine",
            impl_file: "impl.tla".to_string(),
            abstract_file: "abstract.tla".to_string(),
            mapping: JsonMappingInfo {
                source: "auto",
                entries: &mapping.entries,
            },
            result: JsonResultInfo {
                passed: result.passed,
                violations: &result.violations,
            },
            statistics: &stats,
        };

        let json = serde_json::to_string_pretty(&report).expect("serialization should succeed");
        assert!(json.contains("\"command\": \"refine\""));
        assert!(json.contains("\"passed\": true"));
    }
}
