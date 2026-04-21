// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 merge` — merge two TLA+ specifications at the AST level.
//!
//! Applies a "patch" spec onto a "base" spec, unioning declarations and
//! detecting operator conflicts:
//! - EXTENDS: union of both extend lists
//! - VARIABLE/CONSTANT declarations: union (add new from patch)
//! - Operator definitions: keep base-only, add patch-only, detect conflicts
//! - INSTANCE declarations: union by module name
//!
//! Conflicts (same operator name, different body) are reported with markers
//! or resolved via `--force` (patch wins).

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{ConstantDecl, Module, OperatorDef, Unit};
use tla_core::{lower_main_module, pretty_expr, pretty_module, FileId, Spanned};

use crate::cli_schema::MergeOutputFormat;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_merge(
    base: &Path,
    patch: &Path,
    output: Option<&Path>,
    force: bool,
    format: MergeOutputFormat,
) -> Result<()> {
    let base_source = read_source(base)?;
    let patch_source = read_source(patch)?;

    let base_module = parse_and_lower(base, &base_source)?;
    let patch_module = parse_and_lower(patch, &patch_source)?;

    let merge_result = compute_merge(&base_module, &patch_module, &base_source, &patch_source);

    if !force && !merge_result.conflicts.is_empty() {
        match format {
            MergeOutputFormat::Human => {
                print_human_conflicts(base, patch, &merge_result);
                let merged = emit_merged_source_with_conflicts(
                    &base_module,
                    &base_source,
                    &merge_result,
                );
                write_output(output, &merged)?;
                bail!(
                    "merge has {} conflict(s); use --force to accept patch versions",
                    merge_result.conflicts.len()
                );
            }
            MergeOutputFormat::Json => {
                print_json(&merge_result);
                bail!(
                    "merge has {} conflict(s); use --force to accept patch versions",
                    merge_result.conflicts.len()
                );
            }
        }
    }

    match format {
        MergeOutputFormat::Human => {
            let merged_module =
                build_merged_module(&base_module, &patch_module, &merge_result, force);
            let merged_source = pretty_module(&merged_module);
            write_output(output, &merged_source)?;
            print_summary(&merge_result, force);
        }
        MergeOutputFormat::Json => {
            print_json(&merge_result);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Parse + lower helper (reused from cmd_diff pattern)
// ---------------------------------------------------------------------------

fn parse_and_lower(file: &Path, source: &str) -> Result<Module> {
    let parse_result = tla_core::parse(source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, source);
        }
        bail!(
            "parse failed for {}: {} error(s)",
            file.display(),
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, source);
        }
        bail!(
            "lower failed for {}: {} error(s)",
            file.display(),
            result.errors.len()
        );
    }
    result
        .module
        .context(format!("lower produced no module for {}", file.display()))
}

// ---------------------------------------------------------------------------
// Merge data structures
// ---------------------------------------------------------------------------

#[derive(Debug, Default, serde::Serialize)]
struct MergeResult {
    extends_added: Vec<String>,
    variables_added: Vec<String>,
    constants_added: Vec<String>,
    operators_kept: Vec<String>,
    operators_added: Vec<String>,
    operators_identical: Vec<String>,
    conflicts: Vec<Conflict>,
    instances_added: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
struct Conflict {
    name: String,
    base_body: String,
    patch_body: String,
}

// ---------------------------------------------------------------------------
// Merge computation
// ---------------------------------------------------------------------------

fn collect_variables(module: &Module) -> BTreeSet<String> {
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

fn format_constant_decl(decl: &ConstantDecl) -> String {
    match decl.arity {
        Some(arity) if arity > 0 => {
            let underscores: Vec<&str> = (0..arity).map(|_| "_").collect();
            format!("{}({})", decl.name.node, underscores.join(", "))
        }
        _ => decl.name.node.clone(),
    }
}

fn collect_constants(module: &Module) -> BTreeSet<String> {
    let mut consts = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                consts.insert(format_constant_decl(decl));
            }
        }
    }
    consts
}

fn collect_constant_names(module: &Module) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                names.insert(decl.name.node.clone());
            }
        }
    }
    names
}

fn collect_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}

fn collect_instances(module: &Module) -> BTreeSet<String> {
    let mut instances = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Instance(decl) = &unit.node {
            instances.insert(decl.module.node.clone());
        }
    }
    instances
}

fn compute_merge(
    base: &Module,
    patch: &Module,
    base_source: &str,
    patch_source: &str,
) -> MergeResult {
    let _ = (base_source, patch_source); // reserved for future line-number reporting
    let mut result = MergeResult::default();

    // EXTENDS: union
    let base_extends: BTreeSet<&str> = base.extends.iter().map(|s| s.node.as_str()).collect();
    let patch_extends: BTreeSet<&str> = patch.extends.iter().map(|s| s.node.as_str()).collect();
    for ext in &patch_extends {
        if !base_extends.contains(ext) {
            result.extends_added.push((*ext).to_string());
        }
    }

    // VARIABLES: union
    let base_vars = collect_variables(base);
    let patch_vars = collect_variables(patch);
    for var in &patch_vars {
        if !base_vars.contains(var) {
            result.variables_added.push(var.clone());
        }
    }

    // CONSTANTS: union by name
    let base_const_names = collect_constant_names(base);
    let patch_consts = collect_constants(patch);
    let patch_const_names = collect_constant_names(patch);
    for name in &patch_const_names {
        if !base_const_names.contains(name) {
            // Find the formatted version for this name in patch_consts
            for fc in &patch_consts {
                if fc == name || fc.starts_with(&format!("{name}(")) {
                    result.constants_added.push(fc.clone());
                    break;
                }
            }
        }
    }

    // OPERATORS: merge with conflict detection
    let base_ops = collect_operators(base);
    let patch_ops = collect_operators(patch);

    for (name, _) in &base_ops {
        if !patch_ops.contains_key(name) {
            result.operators_kept.push(name.clone());
        }
    }

    for (name, patch_def) in &patch_ops {
        match base_ops.get(name) {
            None => {
                result.operators_added.push(name.clone());
            }
            Some(base_def) => {
                let base_body = pretty_expr(&base_def.body.node);
                let patch_body = pretty_expr(&patch_def.body.node);
                if base_body == patch_body {
                    result.operators_identical.push(name.clone());
                } else {
                    result.conflicts.push(Conflict {
                        name: name.clone(),
                        base_body,
                        patch_body,
                    });
                }
            }
        }
    }

    // INSTANCES: union by module name
    let base_instances = collect_instances(base);
    let patch_instances = collect_instances(patch);
    for inst in &patch_instances {
        if !base_instances.contains(inst) {
            result.instances_added.push(inst.clone());
        }
    }

    result
}

// ---------------------------------------------------------------------------
// Build merged module
// ---------------------------------------------------------------------------

fn build_merged_module(
    base: &Module,
    patch: &Module,
    merge_result: &MergeResult,
    force: bool,
) -> Module {
    let mut merged = base.clone();

    // Add new EXTENDS
    for ext in &merge_result.extends_added {
        merged.extends.push(Spanned::dummy(ext.clone()));
    }

    // Add new VARIABLE declarations
    if !merge_result.variables_added.is_empty() {
        let new_vars: Vec<Spanned<String>> = merge_result
            .variables_added
            .iter()
            .map(|v| Spanned::dummy(v.clone()))
            .collect();
        merged
            .units
            .push(Spanned::dummy(Unit::Variable(new_vars)));
    }

    // Add new CONSTANT declarations
    if !merge_result.constants_added.is_empty() {
        let new_consts: Vec<ConstantDecl> = merge_result
            .constants_added
            .iter()
            .map(|c| {
                // Parse arity from the formatted string "Name(_, _)"
                let (name, arity) = if let Some(paren_pos) = c.find('(') {
                    let name = c[..paren_pos].to_string();
                    let inside = &c[paren_pos + 1..c.len() - 1];
                    let arity = inside.split(',').count();
                    (name, Some(arity))
                } else {
                    (c.clone(), None)
                };
                ConstantDecl {
                    name: Spanned::dummy(name),
                    arity,
                }
            })
            .collect();
        merged
            .units
            .push(Spanned::dummy(Unit::Constant(new_consts)));
    }

    // Handle conflicts: if --force, replace base operator body with patch version
    if force {
        let patch_ops = collect_operators(patch);
        for conflict in &merge_result.conflicts {
            if let Some(patch_def) = patch_ops.get(&conflict.name) {
                // Find and replace the operator in merged units
                for unit in &mut merged.units {
                    if let Unit::Operator(ref mut def) = unit.node {
                        if def.name.node == conflict.name {
                            def.body = (*patch_def).body.clone();
                            break;
                        }
                    }
                }
            }
        }
    }

    // Add new operators from patch
    let patch_ops = collect_operators(patch);
    for op_name in &merge_result.operators_added {
        if let Some(patch_def) = patch_ops.get(op_name) {
            merged
                .units
                .push(Spanned::dummy(Unit::Operator((*patch_def).clone())));
        }
    }

    // Add new INSTANCE declarations from patch
    for unit in &patch.units {
        if let Unit::Instance(decl) = &unit.node {
            if merge_result
                .instances_added
                .contains(&decl.module.node)
            {
                merged.units.push(unit.clone());
            }
        }
    }

    merged
}

// ---------------------------------------------------------------------------
// Emit merged source with conflict markers
// ---------------------------------------------------------------------------

fn emit_merged_source_with_conflicts(
    base: &Module,
    _base_source: &str,
    merge_result: &MergeResult,
) -> String {
    // Build a clean merged module first (without conflicting operators)
    let mut merged = base.clone();

    // Add new EXTENDS
    for ext in &merge_result.extends_added {
        merged.extends.push(Spanned::dummy(ext.clone()));
    }

    // Add new VARIABLE declarations
    if !merge_result.variables_added.is_empty() {
        let new_vars: Vec<Spanned<String>> = merge_result
            .variables_added
            .iter()
            .map(|v| Spanned::dummy(v.clone()))
            .collect();
        merged
            .units
            .push(Spanned::dummy(Unit::Variable(new_vars)));
    }

    // Add new CONSTANT declarations
    if !merge_result.constants_added.is_empty() {
        let new_consts: Vec<ConstantDecl> = merge_result
            .constants_added
            .iter()
            .map(|c| {
                let (name, arity) = if let Some(paren_pos) = c.find('(') {
                    let name = c[..paren_pos].to_string();
                    let inside = &c[paren_pos + 1..c.len() - 1];
                    let arity = inside.split(',').count();
                    (name, Some(arity))
                } else {
                    (c.clone(), None)
                };
                ConstantDecl {
                    name: Spanned::dummy(name),
                    arity,
                }
            })
            .collect();
        merged
            .units
            .push(Spanned::dummy(Unit::Constant(new_consts)));
    }

    // Pretty-print the base module content
    let mut output = pretty_module(&merged);

    // For each conflict, append conflict markers before the final ====
    if !merge_result.conflicts.is_empty() {
        // Find the final ==== line and insert conflict markers before it
        let separator = "\n====";
        if let Some(pos) = output.rfind(separator) {
            let mut insert = String::new();
            for conflict in &merge_result.conflicts {
                insert.push_str("\n\\* <<<<<<< base\n");
                insert.push_str(&format!(
                    "\\* {} == {}\n",
                    conflict.name, conflict.base_body
                ));
                insert.push_str("\\* =======\n");
                insert.push_str(&format!(
                    "\\* {} == {}\n",
                    conflict.name, conflict.patch_body
                ));
                insert.push_str("\\* >>>>>>>\n");
            }
            output.insert_str(pos, &insert);
        }
    }

    output
}

// ---------------------------------------------------------------------------
// Output helpers
// ---------------------------------------------------------------------------

fn write_output(output_path: Option<&Path>, content: &str) -> Result<()> {
    match output_path {
        Some(path) => {
            std::fs::write(path, content)
                .with_context(|| format!("write merged output to {}", path.display()))?;
            eprintln!("Merged output written to {}", path.display());
        }
        None => {
            print!("{content}");
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

fn print_summary(merge_result: &MergeResult, force: bool) {
    let total_ops = merge_result.operators_kept.len()
        + merge_result.operators_added.len()
        + merge_result.operators_identical.len()
        + merge_result.conflicts.len();

    eprintln!();
    eprintln!("Merge summary:");
    if !merge_result.extends_added.is_empty() {
        eprintln!(
            "  EXTENDS added:    {}",
            merge_result.extends_added.join(", ")
        );
    }
    if !merge_result.variables_added.is_empty() {
        eprintln!(
            "  Variables added:  {}",
            merge_result.variables_added.join(", ")
        );
    }
    if !merge_result.constants_added.is_empty() {
        eprintln!(
            "  Constants added:  {}",
            merge_result.constants_added.join(", ")
        );
    }
    if !merge_result.instances_added.is_empty() {
        eprintln!(
            "  Instances added:  {}",
            merge_result.instances_added.join(", ")
        );
    }
    eprintln!(
        "  Operators:        {} total ({} base-only, {} added, {} identical, {} {})",
        total_ops,
        merge_result.operators_kept.len(),
        merge_result.operators_added.len(),
        merge_result.operators_identical.len(),
        merge_result.conflicts.len(),
        if force {
            "resolved (patch wins)"
        } else {
            "conflicts"
        },
    );
    eprintln!();
}

fn print_human_conflicts(base: &Path, patch: &Path, merge_result: &MergeResult) {
    eprintln!("Conflicts detected merging:");
    eprintln!("  base:  {}", base.display());
    eprintln!("  patch: {}", patch.display());
    eprintln!();
    for conflict in &merge_result.conflicts {
        eprintln!("  \x1b[33mCONFLICT: {}\x1b[0m", conflict.name);
        eprintln!("    base:  {}", conflict.base_body);
        eprintln!("    patch: {}", conflict.patch_body);
        eprintln!();
    }
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

fn print_json(merge_result: &MergeResult) {
    let json = serde_json::to_string_pretty(merge_result)
        .expect("invariant: MergeResult is serializable");
    println!("{json}");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_module(source: &str) -> Module {
        let parse_result = tla_core::parse(source);
        assert!(
            parse_result.errors.is_empty(),
            "parse errors: {:?}",
            parse_result.errors
        );
        let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);
        let result = lower_main_module(FileId(0), &tree, None);
        assert!(
            result.errors.is_empty(),
            "lower errors: {:?}",
            result.errors
        );
        result.module.expect("should produce a module")
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_disjoint_operators() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            VARIABLE x
            Next == x' = x + 1
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert_eq!(result.operators_added, vec!["Next"]);
        assert_eq!(result.operators_kept, vec!["Init"]);
        assert!(result.conflicts.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_identical_operators() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert!(result.operators_added.is_empty());
        assert!(result.operators_kept.is_empty());
        assert!(result.conflicts.is_empty());
        assert_eq!(result.operators_identical, vec!["Init"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_conflicting_operators() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            VARIABLE x
            Init == x = 1
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert_eq!(result.conflicts.len(), 1);
        assert_eq!(result.conflicts[0].name, "Init");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_extends_union() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            EXTENDS Naturals
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            EXTENDS Naturals, Sequences
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert_eq!(result.extends_added, vec!["Sequences"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_new_variables() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            VARIABLE x, y
            Init == x = 0
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert_eq!(result.variables_added, vec!["y"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_merge_new_constants() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            CONSTANT N
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            CONSTANT N, M
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let result = compute_merge(&base, &patch, "", "");
        assert_eq!(result.constants_added, vec!["M"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_merged_module_force() {
        let base = parse_module(
            r#"
            ---- MODULE Base ----
            VARIABLE x
            Init == x = 0
            ====
            "#,
        );
        let patch = parse_module(
            r#"
            ---- MODULE Patch ----
            VARIABLE x
            Init == x = 1
            Next == x' = x + 1
            ====
            "#,
        );
        let merge_result = compute_merge(&base, &patch, "", "");
        assert_eq!(merge_result.conflicts.len(), 1);

        let merged = build_merged_module(&base, &patch, &merge_result, true);
        let source = pretty_module(&merged);
        // The merged module should have both Init (with patch body) and Next
        assert!(source.contains("Init"), "should contain Init");
        assert!(source.contains("Next"), "should contain Next");
    }
}
