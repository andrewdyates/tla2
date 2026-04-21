// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reusable helpers for source I/O, JSON error output, and simple subcommands.

use std::io::{Read, Write};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_check::{ErrorSuggestion, JsonOutput, SearchCompleteness};
use tla_core::{
    lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId, ModuleLoader,
    SyntaxNode,
};
use tla_tir::{lower_module_with_env, TirLoweringEnv};

use crate::cli_schema::OutputFormat;

pub(crate) fn read_source(file: &Path) -> Result<String> {
    if file.as_os_str() == "-" {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .context("read stdin")?;
        Ok(buf)
    } else {
        std::fs::read_to_string(file).with_context(|| format!("read {}", file.display()))
    }
}

pub(crate) fn parse_or_report(file: &Path, source: &str) -> Result<SyntaxNode> {
    let result = parse(source);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, source);
        }
        bail!("parse failed with {} error(s)", result.errors.len());
    }
    Ok(SyntaxNode::new_root(result.green_node))
}

pub(crate) fn guess_module_name(file: &Path) -> String {
    if file.as_os_str() == "-" {
        return "<stdin>".to_string();
    }
    file.file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .filter(|s| !s.trim().is_empty())
        .unwrap_or_else(|| "<unknown>".to_string())
}

/// Constant session context for JSON error reporting within a check run.
#[derive(Clone, Copy)]
pub(crate) struct JsonErrorCtx<'a> {
    pub(crate) output_format: OutputFormat,
    pub(crate) spec_file: &'a Path,
    pub(crate) config_file: Option<&'a Path>,
    pub(crate) module_name: Option<&'a str>,
    pub(crate) workers: usize,
    pub(crate) completeness: SearchCompleteness,
}

pub(crate) fn emit_check_cli_error(
    ctx: &JsonErrorCtx<'_>,
    error_code: &str,
    error_message: String,
    suggestion: Option<ErrorSuggestion>,
    diagnostics: impl IntoIterator<Item = String>,
) -> ! {
    debug_assert!(matches!(
        ctx.output_format,
        OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
    ));

    // ITF has no error representation; emit the error to stderr and exit.
    if matches!(ctx.output_format, OutputFormat::Itf) {
        eprintln!("Error: {}", error_message);
        std::process::exit(2);
    }

    let module_name_owned;
    let module_name = match ctx.module_name {
        Some(name) => name,
        None => {
            module_name_owned = guess_module_name(ctx.spec_file);
            module_name_owned.as_str()
        }
    };

    let mut json_output = JsonOutput::new(ctx.spec_file, ctx.config_file, module_name, ctx.workers)
        .with_completeness(ctx.completeness)
        .with_cli_error(error_code, error_message, suggestion);

    for msg in diagnostics {
        json_output.add_info(error_code, &msg);
    }

    let json_str = match ctx.output_format {
        OutputFormat::Json => json_output.to_json(),
        OutputFormat::Jsonl => json_output.to_json_compact(),
        OutputFormat::Human => unreachable!("emit_check_cli_error: human output"),
        OutputFormat::TlcTool => unreachable!("emit_check_cli_error: tlc-tool output"),
        OutputFormat::Itf => unreachable!("emit_check_cli_error: handled above"),
    };
    match json_str {
        Ok(s) => println!("{}", s),
        Err(e) => eprintln!("error: failed to serialize JSON output: {e}"),
    }
    std::process::exit(2);
}

pub(crate) fn cmd_parse(file: &Path) -> Result<()> {
    let source = read_source(file)?;
    let _ = parse_or_report(file, &source)?;
    Ok(())
}

pub(crate) fn cmd_ast(file: &Path, tir: bool) -> Result<()> {
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
    let mut stdout = std::io::stdout().lock();
    if tir {
        let tir_module = lower_module_to_tir(file, &tree, &module)?;
        writeln!(stdout, "{tir_module:#?}").context("write TIR debug output")?;
    } else {
        writeln!(stdout, "{module:#?}").context("write AST debug output")?;
    }
    Ok(())
}

pub(crate) fn lower_module_to_tir(
    file: &Path,
    tree: &SyntaxNode,
    module: &tla_core::ast::Module,
) -> Result<tla_tir::TirModule> {
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(tree, file);
    loader
        .load_extends(module)
        .with_context(|| format!("load EXTENDS dependencies for `{}`", module.name.node))?;
    loader
        .load_instances(module)
        .with_context(|| format!("load INSTANCE dependencies for `{}`", module.name.node))?;

    let mut env = TirLoweringEnv::new(module);
    for dep in loader.modules_for_model_checking(module) {
        env.add_module(dep);
    }

    lower_module_with_env(&env, module)
        .with_context(|| format!("lower module `{}` into TIR", module.name.node))
}
