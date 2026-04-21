// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 vmt` subcommand: export a TLA+ spec as VMT format for external model checkers.
//!
//! VMT (Verification Modulo Theories) is an SMT-LIB2 extension used by tools
//! like nuXmv, ic3ia, and AVR. This command translates Init/Next/invariants
//! into VMT format with `.init`, `.trans`, and `.prop` predicates.
//!
//! Part of #3755: VMT output format for external model checkers (Apalache Gap 7).

use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_check::Config;
use tla_core::{lower_main_module, FileId, ModuleLoader};

use crate::helpers::read_source;

/// Run the VMT export command.
pub(crate) fn cmd_vmt(file: &Path, config_path: Option<&Path>) -> Result<()> {
    // Parse and lower the TLA+ source.
    let source = read_source(file)?;
    let parse_result = tla_core::parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("parse failed with {} error(s)", parse_result.errors.len());
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
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    // Load extended and instanced modules.
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader
        .load_extends(&module)
        .with_context(|| format!("load EXTENDS dependencies for `{}`", module.name.node))?;
    loader
        .load_instances(&module)
        .with_context(|| format!("load INSTANCE dependencies for `{}`", module.name.node))?;

    // Parse config file.
    let config_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg_path = file.to_path_buf();
            cfg_path.set_extension("cfg");
            if !cfg_path.exists() {
                bail!(
                    "No config file specified and {} does not exist.\n\
                     Use --config to specify a configuration file.",
                    cfg_path.display()
                );
            }
            cfg_path
        }
    };

    let config_source = std::fs::read_to_string(&config_path)
        .with_context(|| format!("read config {}", config_path.display()))?;
    let config = match Config::parse(&config_source) {
        Ok(c) => c,
        Err(errors) => {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path.display(), err.line(), err);
            }
            bail!("config parse failed with {} error(s)", errors.len());
        }
    };

    // Build evaluation context (same pattern as BMC/PDR CLI runners).
    let checker_modules = loader.modules_for_model_checking(&module);
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    for m in &checker_modules {
        ctx.load_module(m);
    }

    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, &config) {
        bail!("Failed to bind constants: {}", e);
    }

    // Export VMT.
    #[cfg(feature = "z4")]
    {
        let vmt =
            tla_check::export_vmt(&module, &config, &ctx).map_err(|e| anyhow::anyhow!("{e}"))?;

        print!("{}", vmt.content);

        eprintln!(
            "VMT export complete: {} variable(s), {} invariant(s)",
            vmt.num_vars, vmt.num_invariants
        );
        Ok(())
    }

    #[cfg(not(feature = "z4"))]
    {
        bail!("VMT export requires the z4 feature. Rebuild with --features z4");
    }
}
