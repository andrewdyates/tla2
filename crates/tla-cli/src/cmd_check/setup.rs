// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Shared context for extracted cmd_check helper functions.
pub(super) struct CheckCtx<'a> {
    pub(super) file: &'a Path,
    pub(super) config_path: Option<&'a Path>,
    pub(super) workers: usize,
    pub(super) max_states: usize,
    pub(super) max_depth: usize,
    pub(super) output_format: OutputFormat,
}

/// Read, parse, and lower a TLA+ source file. Returns (source, syntax tree, module).
pub(super) fn parse_and_lower(
    file: &Path,
    json_err_ctx: &JsonErrorCtx<'_>,
    output_format: OutputFormat,
) -> Result<(String, SyntaxNode, tla_core::ast::Module)> {
    let source = match read_source(file) {
        Ok(source) => source,
        Err(e) => {
            if matches!(
                output_format,
                OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
            ) {
                emit_check_cli_error(
                    json_err_ctx,
                    error_codes::SYS_IO_ERROR,
                    format!("Failed to read spec: {e:#}"),
                    Some(ErrorSuggestion::new(
                        "Ensure the spec file exists and is readable",
                    )),
                    std::iter::empty::<String>(),
                );
            }
            return Err(e);
        }
    };

    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        if matches!(
            output_format,
            OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
        ) {
            let diag: Vec<String> = parse_result
                .errors
                .iter()
                .map(|err| format!("{}..{}: {}", err.start, err.end, err.message))
                .collect();
            emit_check_cli_error(
                json_err_ctx,
                error_codes::TLA_PARSE_ERROR,
                format!(
                    "TLA+ parse failed with {} error(s)",
                    parse_result.errors.len()
                ),
                Some(ErrorSuggestion::new(
                    "Fix the TLA+ syntax error(s) and re-run",
                )),
                diag,
            );
        }
        if matches!(output_format, OutputFormat::TlcTool) {
            let diag: Vec<String> = parse_result
                .errors
                .iter()
                .map(|err| format!("{}..{}: {}", err.start, err.end, err.message))
                .collect();
            bail!(
                "TLA+ parse failed with {} error(s)\n{}",
                parse_result.errors.len(),
                diag.join("\n")
            );
        }
        let _ = parse_or_report(file, &source)?;
        unreachable!("parse_or_report should have returned an error");
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    // Use lower_main_module to correctly select the last (main) module in
    // multi-module files. The filename hint helps match when the file stem
    // corresponds to a specific module name.
    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        if matches!(
            output_format,
            OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
        ) {
            let diag: Vec<String> = result
                .errors
                .iter()
                .map(|err| format!("{}..{}: {}", err.span.start, err.span.end, err.message))
                .collect();
            emit_check_cli_error(
                json_err_ctx,
                error_codes::TLA_LOWER_ERROR,
                format!("TLA+ lowering failed with {} error(s)", result.errors.len()),
                Some(ErrorSuggestion::new(
                    "Fix the TLA+ lowering error(s) and re-run",
                )),
                diag,
            );
        }

        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    Ok((source, tree, module))
}

/// Load a set of modules (extends or instances), emitting JSON errors on failure.
pub(super) fn load_module_set<F>(
    loader: &mut ModuleLoader,
    module: &tla_core::ast::Module,
    load_fn: F,
    kind: &str,
    ctx: &CheckCtx<'_>,
) -> Result<Vec<String>>
where
    F: FnOnce(&mut ModuleLoader, &tla_core::ast::Module) -> Result<Vec<String>>,
{
    match load_fn(loader, module) {
        Ok(names) => {
            if !names.is_empty() && matches!(ctx.output_format, OutputFormat::Human) {
                eprintln!("Loaded {} modules: {}", kind, names.join(", "));
            }
            Ok(names)
        }
        Err(e) => {
            if matches!(
                ctx.output_format,
                OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
            ) {
                // ITF has no error representation; emit error to stderr and exit.
                if matches!(ctx.output_format, OutputFormat::Itf) {
                    eprintln!("Error: Failed to load {} modules: {e}", kind);
                    std::process::exit(2);
                }
                let json_output = JsonOutput::new(
                    ctx.file,
                    ctx.config_path,
                    &module.name.node,
                    ctx.workers,
                )
                .with_completeness(SearchCompleteness::from_bounds(
                    ctx.max_states,
                    ctx.max_depth,
                ))
                .with_cli_error(
                    error_codes::SYS_SETUP_ERROR,
                    format!("Failed to load {} modules: {e}", kind),
                    Some(
                        ErrorSuggestion::new(
                            "Ensure all referenced modules exist on the module search path",
                        )
                        .with_example(
                            "Create the missing module next to the spec, or fix EXTENDS/INSTANCE",
                        ),
                    ),
                );
                let json_str = if matches!(ctx.output_format, OutputFormat::Jsonl) {
                    json_output.to_json_compact().context("serialize JSON")?
                } else {
                    json_output.to_json().context("serialize JSON")?
                };
                println!("{}", json_str);
                std::process::exit(2);
            }
            bail!("Failed to load {} modules: {}", kind, e);
        }
    }
}

/// Run semantic analysis and report errors in the appropriate format.
pub(super) fn run_semantic_analysis(
    module: &tla_core::ast::Module,
    extended_modules: &[&tla_core::ast::Module],
    instanced_modules: &[&tla_core::ast::Module],
    json_err_ctx: &JsonErrorCtx<'_>,
    file: &Path,
    output_format: OutputFormat,
) -> Result<()> {
    let resolve_result = resolve_with_extends_and_instances_with_options(
        module,
        extended_modules,
        instanced_modules,
        ResolveOptions::model_checking(),
    );
    if resolve_result.errors.is_empty() {
        return Ok(());
    }

    if matches!(
        output_format,
        OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
    ) {
        let file_path = file.display().to_string();
        let diag: Vec<String> = resolve_result
            .errors
            .iter()
            .map(|err| format!("{file_path}: semantic error: {err}"))
            .collect();
        emit_check_cli_error(
            json_err_ctx,
            error_codes::SYS_SETUP_ERROR,
            format!(
                "semantic analysis failed with {} error(s)",
                resolve_result.errors.len()
            ),
            Some(ErrorSuggestion::new("Fix the semantic error(s) and re-run")),
            diag,
        );
    }

    if matches!(output_format, OutputFormat::TlcTool) {
        let file_path = file.display().to_string();
        let diag: Vec<String> = resolve_result
            .errors
            .iter()
            .map(|err| format!("{file_path}: semantic error: {err}"))
            .collect();
        bail!(
            "semantic analysis failed with {} error(s)\n{}",
            resolve_result.errors.len(),
            diag.join("\n")
        );
    }

    if matches!(output_format, OutputFormat::Human) {
        let file_path = file.display().to_string();
        for err in &resolve_result.errors {
            eprintln!("{}: semantic error: {}", file_path, err);
        }
    }
    bail!(
        "semantic analysis failed with {} error(s)",
        resolve_result.errors.len()
    );
}

/// Find, read, and parse the .cfg configuration file.
///
/// Returns the resolved config path, config source text, and parsed Config.
/// When `has_cli_init_next` is true, a missing .cfg file is tolerated and a
/// default empty Config is returned instead of an error. When neither .cfg
/// nor CLI flags exist, falls back to convention names "Init" and "Next"
/// (Part of #3759, #3779).
pub(super) fn load_and_parse_config(
    file: &Path,
    config_path: Option<&Path>,
    json_err_ctx: &JsonErrorCtx<'_>,
    output_format: OutputFormat,
    has_cli_init_next: bool,
) -> Result<(PathBuf, String, Config)> {
    let config_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg_path = file.to_path_buf();
            cfg_path.set_extension("cfg");
            if !cfg_path.exists() {
                // Part of #3759: If CLI flags provide --init and --next, allow
                // running without a .cfg file by returning a default Config.
                if has_cli_init_next {
                    return Ok((cfg_path, String::new(), Config::default()));
                }
                // Part of #3779: Fall back to convention names "Init" and "Next"
                // when neither .cfg nor --init/--next CLI flags are provided.
                // This matches Apalache behavior and enables config-free checking.
                if matches!(output_format, OutputFormat::Human) {
                    eprintln!("No config file found. Using convention names: Init, Next");
                }
                let mut default_config = Config::default();
                default_config.init = Some("Init".to_string());
                default_config.next = Some("Next".to_string());
                return Ok((cfg_path, String::new(), default_config));
            }
            cfg_path
        }
    };

    // Update json_err_ctx locally for subsequent errors in this function.
    let json_err_ctx = JsonErrorCtx {
        config_file: Some(&config_path),
        ..*json_err_ctx
    };

    if !config_path.exists() {
        if matches!(
            output_format,
            OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
        ) {
            emit_check_cli_error(
                &json_err_ctx,
                error_codes::SYS_SETUP_ERROR,
                format!("Config file {} does not exist.", config_path.display()),
                Some(
                    ErrorSuggestion::new("Fix the config path or create the config file")
                        .with_example("tla2 check Spec.tla --config Spec.cfg"),
                ),
                std::iter::empty::<String>(),
            );
        }
        bail!("Config file {} does not exist.", config_path.display());
    }

    let config_source = match std::fs::read_to_string(&config_path)
        .with_context(|| format!("read config {}", config_path.display()))
    {
        Ok(src) => src,
        Err(e) => {
            if matches!(
                output_format,
                OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
            ) {
                emit_check_cli_error(
                    &json_err_ctx,
                    error_codes::SYS_IO_ERROR,
                    format!("Failed to read config: {e:#}"),
                    Some(ErrorSuggestion::new(
                        "Ensure the config file exists and is readable",
                    )),
                    std::iter::empty::<String>(),
                );
            }
            return Err(e);
        }
    };

    let config = match Config::parse(&config_source) {
        Ok(config) => config,
        Err(errors) => {
            if matches!(
                output_format,
                OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
            ) {
                let diag: Vec<String> = errors
                    .iter()
                    .map(|err| format!("{}:{}: {}", config_path.display(), err.line(), err))
                    .collect();
                emit_check_cli_error(
                    &json_err_ctx,
                    error_codes::CFG_PARSE_ERROR,
                    format!("config parse failed with {} error(s)", errors.len()),
                    Some(ErrorSuggestion::new(
                        "Fix the config syntax error(s) and re-run",
                    )),
                    diag,
                );
            }
            if matches!(output_format, OutputFormat::TlcTool) {
                let diag: Vec<String> = errors
                    .iter()
                    .map(|err| format!("{}:{}: {}", config_path.display(), err.line(), err))
                    .collect();
                return Err(anyhow::anyhow!(
                    "config parse failed with {} error(s)\n{}",
                    errors.len(),
                    diag.join("\n")
                ));
            }

            if matches!(output_format, OutputFormat::Human) {
                for err in &errors {
                    eprintln!("{}:{}: {}", config_path.display(), err.line(), err);
                }
            }
            return Err(anyhow::anyhow!(
                "config parse failed with {} error(s)",
                errors.len()
            ));
        }
    };

    Ok((config_path, config_source, config))
}
