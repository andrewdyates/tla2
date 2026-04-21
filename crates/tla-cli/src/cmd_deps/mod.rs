// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 deps` -- dependency graph analysis and visualization for TLA+ specifications.
//!
//! Parses a TLA+ spec and produces dependency information:
//! - Module dependencies (EXTENDS/INSTANCE)
//! - Operator call graph
//! - Variable usage per operator
//! - Root reachability (from Init/Next/invariants)
//! - Dead code detection (unreachable operators)
//! - Circular dependency detection (excluding RECURSIVE)

mod graph;
mod output;

use std::path::Path;

use anyhow::{bail, Context, Result};

use crate::cli_schema::DepsOutputFormat;
use crate::helpers::read_source;

use self::graph::DepGraph;

/// Run the deps analysis command.
pub(crate) fn cmd_deps(
    file: &Path,
    config_path: Option<&Path>,
    format: DepsOutputFormat,
    show_unused: bool,
    modules_only: bool,
) -> Result<()> {
    // Parse and lower the TLA+ source.
    let source = read_source(file)?;
    let parse_result = tla_core::parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic = tla_core::parse_error_diagnostic(
                &file_path,
                &err.message,
                err.start,
                err.end,
            );
            diagnostic.eprint(&file_path, &source);
        }
        bail!("parse failed with {} error(s)", parse_result.errors.len());
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = tla_core::lower_main_module(tla_core::FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    // Load extended and instanced modules.
    let mut loader = tla_core::ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    let _ = loader.load_extends(&module);
    let _ = loader.load_instances(&module);

    // Get loaded modules via the public API.
    let loaded_modules = loader.modules_for_model_checking(&module);

    // Optionally parse the config file for Init/Next/invariants/properties.
    let config = load_config(file, config_path);

    // Build the dependency graph.
    let dep_graph = DepGraph::build(&module, &loaded_modules, config.as_ref(), &source);

    // Emit output.
    match format {
        DepsOutputFormat::Tree => output::emit_tree(&dep_graph, show_unused, modules_only),
        DepsOutputFormat::Dot => output::emit_dot(&dep_graph, modules_only),
        DepsOutputFormat::Json => output::emit_json(&dep_graph, show_unused, modules_only),
    }

    Ok(())
}

/// Try to load a .cfg config file. Returns `None` if no config found (not an error
/// for deps -- we just won't know the roots from the config).
fn load_config(file: &Path, config_path: Option<&Path>) -> Option<tla_check::Config> {
    let config_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            if !cfg.exists() {
                return None;
            }
            cfg
        }
    };

    let config_source = std::fs::read_to_string(&config_path).ok()?;
    tla_check::Config::parse(&config_source).ok()
}
