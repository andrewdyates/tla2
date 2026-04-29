// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 compose` — parallel composition of two TLA+ specifications.
//!
//! Analyzes two TLA+ specifications for composition compatibility and
//! reports shared variables, interface analysis, and composition metrics.
//! Generates a composed specification skeleton if the specs are compatible.

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the compose command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ComposeOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run parallel composition analysis on two TLA+ specs.
pub(crate) fn cmd_compose(file_a: &Path, file_b: &Path, format: ComposeOutputFormat) -> Result<()> {
    let start = Instant::now();

    // --- Parse both specs --------------------------------------------------

    let module_a = parse_and_lower(file_a, FileId(0))?;
    let module_b = parse_and_lower(file_b, FileId(1))?;

    // --- Extract metadata --------------------------------------------------

    let vars_a = extract_var_names(&module_a);
    let vars_b = extract_var_names(&module_b);
    let ops_a = extract_op_names(&module_a);
    let ops_b = extract_op_names(&module_b);
    let consts_a = extract_constant_names(&module_a);
    let consts_b = extract_constant_names(&module_b);

    // --- Compute composition analysis --------------------------------------

    let shared_vars: BTreeSet<String> = vars_a.intersection(&vars_b).cloned().collect();
    let only_a_vars: BTreeSet<String> = vars_a.difference(&vars_b).cloned().collect();
    let only_b_vars: BTreeSet<String> = vars_b.difference(&vars_a).cloned().collect();

    let shared_ops: BTreeSet<String> = ops_a.intersection(&ops_b).cloned().collect();
    let shared_consts: BTreeSet<String> = consts_a.intersection(&consts_b).cloned().collect();

    let all_vars: BTreeSet<String> = vars_a.union(&vars_b).cloned().collect();
    let all_consts: BTreeSet<String> = consts_a.union(&consts_b).cloned().collect();

    let has_init_a = ops_a.contains("Init");
    let has_init_b = ops_b.contains("Init");
    let has_next_a = ops_a.contains("Next");
    let has_next_b = ops_b.contains("Next");

    let composable =
        !shared_ops.contains("Init") || !shared_ops.contains("Next") || shared_vars.is_empty();

    let composition_type = if shared_vars.is_empty() {
        "independent"
    } else if shared_ops.is_empty() {
        "shared_state"
    } else {
        "interleaved"
    };

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        ComposeOutputFormat::Human => {
            println!("compose: {} || {}", file_a.display(), file_b.display());
            println!(
                "  module A: {} ({} vars, {} ops)",
                module_a.name.node,
                vars_a.len(),
                ops_a.len()
            );
            println!(
                "  module B: {} ({} vars, {} ops)",
                module_b.name.node,
                vars_b.len(),
                ops_b.len()
            );
            println!();

            println!("  Shared variables ({}):", shared_vars.len());
            if shared_vars.is_empty() {
                println!("    (none — independent composition)");
            } else {
                for v in &shared_vars {
                    println!("    {v}");
                }
            }

            if !only_a_vars.is_empty() {
                println!("  Only in A ({}):", only_a_vars.len());
                for v in &only_a_vars {
                    println!("    {v}");
                }
            }
            if !only_b_vars.is_empty() {
                println!("  Only in B ({}):", only_b_vars.len());
                for v in &only_b_vars {
                    println!("    {v}");
                }
            }

            if !shared_ops.is_empty() {
                println!();
                println!("  Shared operators ({}):", shared_ops.len());
                for op in &shared_ops {
                    println!("    {op}");
                }
            }

            if !shared_consts.is_empty() {
                println!();
                println!("  Shared constants ({}):", shared_consts.len());
                for c in &shared_consts {
                    println!("    {c}");
                }
            }

            println!();
            println!("  Composition type: {composition_type}");
            println!(
                "  Composable: {}",
                if composable {
                    "yes"
                } else {
                    "WARNING — operator name conflicts"
                }
            );
            println!("  Combined variables: {}", all_vars.len());
            println!("  Combined constants: {}", all_consts.len());
            println!("  Init available: A={}, B={}", has_init_a, has_init_b);
            println!("  Next available: A={}, B={}", has_next_a, has_next_b);
            println!("  elapsed: {elapsed:.2}s");

            if composable && has_init_a && has_init_b && has_next_a && has_next_b {
                println!();
                println!("  Composed specification skeleton:");
                println!("    Init_Composed == Init_A /\\ Init_B");
                println!("    Next_Composed == Next_A \\/ Next_B");
                println!(
                    "    vars_composed == <<{}>>",
                    all_vars.iter().cloned().collect::<Vec<_>>().join(", ")
                );
            }
        }
        ComposeOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "spec_a": {
                    "file": file_a.display().to_string(),
                    "module": module_a.name.node,
                    "variables": vars_a.iter().collect::<Vec<_>>(),
                    "operators": ops_a.iter().collect::<Vec<_>>(),
                    "constants": consts_a.iter().collect::<Vec<_>>(),
                },
                "spec_b": {
                    "file": file_b.display().to_string(),
                    "module": module_b.name.node,
                    "variables": vars_b.iter().collect::<Vec<_>>(),
                    "operators": ops_b.iter().collect::<Vec<_>>(),
                    "constants": consts_b.iter().collect::<Vec<_>>(),
                },
                "composition": {
                    "type": composition_type,
                    "composable": composable,
                    "shared_variables": shared_vars.iter().collect::<Vec<_>>(),
                    "shared_operators": shared_ops.iter().collect::<Vec<_>>(),
                    "shared_constants": shared_consts.iter().collect::<Vec<_>>(),
                    "combined_variables": all_vars.iter().collect::<Vec<_>>(),
                    "combined_constants": all_consts.iter().collect::<Vec<_>>(),
                },
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_and_lower(file: &Path, file_id: FileId) -> Result<Module> {
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(file_id, &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed for {}: {} error(s)",
            file.display(),
            lower_result.errors.len()
        );
    }
    lower_result
        .module
        .with_context(|| format!("lowering produced no module for {}", file.display()))
}

fn extract_var_names(module: &Module) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.insert(decl.node.clone());
            }
        }
    }
    vars
}

fn extract_op_names(module: &Module) -> BTreeSet<String> {
    let mut ops = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone());
        }
    }
    ops
}

fn extract_constant_names(module: &Module) -> BTreeSet<String> {
    let mut constants = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                constants.insert(decl.name.node.clone());
            }
        }
    }
    constants
}
