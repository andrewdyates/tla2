// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `minimize` subcommand: reduce a TLA+ spec to a minimal reproducer.
//!
//! Given a spec that exhibits a particular model-checking result (invariant
//! violation, deadlock, etc.), this command systematically removes AST elements
//! to find the smallest spec that still exhibits the same result.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use tla_check::{
    check_module, resolve_spec_from_config_with_extends, Config, MinimizeConfig, Minimizer,
    ResultClass,
};
use tla_core::{lower_error_diagnostic, lower_main_module, pretty_module, FileId, ModuleLoader};

use crate::{parse_or_report, read_source};

pub(crate) fn cmd_minimize(
    file: &Path,
    config_path: Option<&Path>,
    max_oracle_calls: usize,
    no_fine: bool,
    output_path: Option<&Path>,
) -> Result<()> {
    // --- Parse and lower the source ---
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
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    // --- Load extended/instanced modules ---
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);

    if let Err(e) = loader.load_extends(&module) {
        bail!("Failed to load extended modules: {}", e);
    }
    if let Err(e) = loader.load_instances(&module) {
        bail!("Failed to load instanced modules: {}", e);
    }

    // --- Parse config ---
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            if !cfg.exists() {
                bail!(
                    "No config file specified and {} does not exist.\n\
                     Use --config to specify a configuration file.",
                    cfg.display()
                );
            }
            cfg
        }
    };

    let config_source = std::fs::read_to_string(&config_path_buf)
        .with_context(|| format!("read config {}", config_path_buf.display()))?;

    let mut config = Config::parse(&config_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive");
    }

    // Resolve SPECIFICATION if needed
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        let (extended_modules_for_resolve, _instanced_modules_for_resolve) =
            loader.modules_for_semantic_resolution(&module);
        let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
            .iter()
            .map(|m| m.name.node.as_str())
            .collect();
        let extended_syntax_trees: Vec<_> = spec_scope_module_names
            .iter()
            .filter_map(|name| loader.get(name).map(|l| &l.syntax_tree))
            .collect();

        match resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees) {
            Ok(resolved) => {
                if config.init.is_none() {
                    config.init = Some(resolved.init.clone());
                }
                if config.next.is_none() {
                    config.next = Some(resolved.next.clone());
                }
            }
            Err(e) => {
                bail!("Failed to resolve SPECIFICATION: {}", e);
            }
        }
    }
    config.normalize_resolved_specification();

    // --- Run initial model check to determine target ---
    eprintln!("Running initial model check to determine target property...");
    let initial_result = check_module(&module, &config);
    let target = ResultClass::from_check_result(&initial_result);

    eprintln!("Target result: {:?}", target);
    if target == ResultClass::Success {
        bail!(
            "The spec passes all checks. The minimizer requires a spec with a \
             violation (invariant violation, deadlock, etc.) to minimize."
        );
    }
    if target == ResultClass::Error {
        bail!(
            "The spec produces an error during model checking. Fix the error \
             before attempting minimization."
        );
    }

    // --- Run the minimizer ---
    eprintln!(
        "Minimizing spec ({} units, max {} oracle calls)...",
        module.units.len(),
        max_oracle_calls
    );
    let start = Instant::now();

    let minimize_config = MinimizeConfig {
        max_oracle_calls,
        fine_reduction: !no_fine,
        ..Default::default()
    };
    let minimizer = Minimizer::new(&config, target.clone(), minimize_config);
    let min_result = minimizer.minimize(&module);
    let elapsed = start.elapsed();

    // --- Output results ---
    let minimized_source = pretty_module(&min_result.module);

    eprintln!();
    eprintln!("Minimization complete ({:.2}s)", elapsed.as_secs_f64());
    eprintln!("  Oracle calls: {}", min_result.stats.oracle_calls);
    eprintln!(
        "  Successful reductions: {}",
        min_result.stats.successful_reductions
    );
    eprintln!(
        "  Units: {} -> {}",
        min_result.stats.original_units, min_result.stats.final_units
    );
    eprintln!(
        "  Operators: {} -> {}",
        min_result.stats.original_operators, min_result.stats.final_operators
    );
    eprintln!("  Target preserved: {:?}", min_result.target);

    if let Some(out_path) = output_path {
        std::fs::write(out_path, &minimized_source)
            .with_context(|| format!("write output to {}", out_path.display()))?;
        eprintln!("  Output written to: {}", out_path.display());
    } else {
        // Print minimized spec to stdout
        println!("{}", minimized_source);
    }

    Ok(())
}
