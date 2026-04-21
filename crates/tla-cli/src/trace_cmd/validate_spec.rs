// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spec-based trace validation using TraceValidationEngine.

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Context, Result};
use tla_check::{
    bind_constants_from_config, read_trace_events, resolve_spec_from_config_with_extends,
    resolve_trace_input_format, ActionLabelMode, Config, EvalCtx, TraceEventSink, TraceHeader,
    TraceInputFormatSelection, TraceSourceHint, TraceStep, TraceValidationEngine,
};
use tla_core::ast::Unit;
use tla_core::{
    lower_main_module, resolve_with_extends_and_instances_with_options, FileId, ModuleLoader,
    ResolveOptions, SyntaxNode,
};

use super::TraceInputFormatArg;

/// Spec-based trace validation using TraceValidationEngine.
pub(crate) fn cmd_trace_validate_with_spec(
    trace_path: &Path,
    input_format: TraceInputFormatArg,
    spec_path: &Path,
    config_path: Option<&Path>,
    action_label_mode: ActionLabelMode,
) -> Result<()> {
    // --- Parse trace ---
    let selection = TraceInputFormatSelection::from(input_format);
    let hint = if trace_path.as_os_str() == "-" {
        TraceSourceHint::Stdin
    } else {
        TraceSourceHint::Path(trace_path)
    };
    let format = resolve_trace_input_format(selection, hint);

    let reader: Box<dyn Read> = if trace_path.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(File::open(trace_path).with_context(|| format!("open {}", trace_path.display()))?)
    };

    let mut sink = CollectSink::default();
    let parse = read_trace_events(reader, format, &mut sink)
        .with_context(|| format!("parse trace {} as {:?}", trace_path.display(), format));
    if trace_path.as_os_str() == "-" && matches!(input_format, TraceInputFormatArg::Auto) {
        parse
            .context("hint: stdin `auto` defaults to JSON; use `--input-format jsonl` for JSONL")?;
    } else {
        parse?;
    }

    let header = sink
        .header
        .as_ref()
        .context("trace parser did not deliver a header")?;
    let steps = sink.steps;

    eprintln!(
        "Parsed {} trace steps (module {}, {} vars)",
        steps.len(),
        header.module,
        header.variables.len()
    );
    let trace_module_name = header.module.clone();

    // --- Parse and lower TLA+ spec ---
    let source = std::fs::read_to_string(spec_path)
        .with_context(|| format!("read spec {}", spec_path.display()))?;

    let tla_parse_result = tla_core::parse(&source);
    if !tla_parse_result.errors.is_empty() {
        let diag: Vec<String> = tla_parse_result
            .errors
            .iter()
            .map(|err| format!("{}..{}: {}", err.start, err.end, err.message))
            .collect();
        bail!(
            "TLA+ parse failed with {} error(s)\n{}",
            tla_parse_result.errors.len(),
            diag.join("\n")
        );
    }
    let tree = SyntaxNode::new_root(tla_parse_result.green_node);

    let hint_name = spec_path
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint_name);
    if !lower_result.errors.is_empty() {
        let diag: Vec<String> = lower_result
            .errors
            .iter()
            .map(|err| format!("{}..{}: {}", err.span.start, err.span.end, err.message))
            .collect();
        bail!(
            "TLA+ lowering failed with {} error(s)\n{}",
            lower_result.errors.len(),
            diag.join("\n")
        );
    }
    let module = lower_result.module.context("lower produced no module")?;

    // Warn if trace module name doesn't match spec module name
    if trace_module_name != module.name.node {
        eprintln!(
            "Warning: trace module name '{}' differs from spec module name '{}'",
            trace_module_name, module.name.node
        );
    }

    // --- Load extended modules ---
    let mut loader = ModuleLoader::new(spec_path);
    loader.seed_from_syntax_tree(&tree, spec_path);

    let extended_module_names = loader
        .load_extends(&module)
        .with_context(|| "failed to load extended modules")?;
    if !extended_module_names.is_empty() {
        eprintln!(
            "Loaded extended modules: {}",
            extended_module_names.join(", ")
        );
    }

    let instance_module_names = loader
        .load_instances(&module)
        .with_context(|| "failed to load instanced modules")?;
    if !instance_module_names.is_empty() {
        eprintln!(
            "Loaded instanced modules: {}",
            instance_module_names.join(", ")
        );
    }

    // Modules for semantic resolution
    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);

    // Syntax trees for SPECIFICATION resolution (extended + instanced modules)
    let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
        .iter()
        .chain(instanced_modules_for_resolve.iter())
        .map(|m| m.name.node.as_str())
        .collect();
    let spec_scope_syntax_trees: Vec<_> = spec_scope_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.syntax_tree))
        .collect();

    // --- Semantic analysis ---
    let resolve_result = resolve_with_extends_and_instances_with_options(
        &module,
        &extended_modules_for_resolve,
        &instanced_modules_for_resolve,
        ResolveOptions::model_checking(),
    );
    if !resolve_result.errors.is_empty() {
        let diag: Vec<String> = resolve_result
            .errors
            .iter()
            .map(|err| format!("semantic error: {err}"))
            .collect();
        bail!(
            "semantic analysis failed with {} error(s)\n{}",
            resolve_result.errors.len(),
            diag.join("\n")
        );
    }

    // --- Parse config file ---
    let resolved_config_path = match config_path {
        Some(p) => {
            let path = p.to_path_buf();
            if !path.exists() {
                bail!("Config file {} does not exist.", path.display());
            }
            path
        }
        None => {
            let mut cfg_path = spec_path.to_path_buf();
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

    let config_source = std::fs::read_to_string(&resolved_config_path)
        .with_context(|| format!("read config {}", resolved_config_path.display()))?;

    let mut config = Config::parse(&config_source).map_err(|errors| {
        let diag: Vec<String> = errors
            .iter()
            .map(|err| format!("{}:{}: {}", resolved_config_path.display(), err.line(), err))
            .collect();
        anyhow::anyhow!(
            "config parse failed with {} error(s)\n{}",
            errors.len(),
            diag.join("\n")
        )
    })?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive — use one or the other");
    }

    // Resolve Init/Next from SPECIFICATION if needed
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        match resolve_spec_from_config_with_extends(&config, &tree, &spec_scope_syntax_trees) {
            Ok(resolved) => {
                if config.init.is_none() {
                    config.init = Some(resolved.init.clone());
                }
                if config.next.is_none() {
                    config.next = Some(resolved.next.clone());
                }
            }
            Err(e) => {
                bail!("Failed to resolve Init/Next from SPECIFICATION: {e}");
            }
        }
    }
    config.normalize_resolved_specification();

    let init_name = config
        .init
        .as_ref()
        .context("config must specify INIT (or SPECIFICATION)")?;
    let next_name = config
        .next
        .as_ref()
        .context("config must specify NEXT (or SPECIFICATION)")?;

    eprintln!("Using Init={init_name}, Next={next_name}");

    // --- Set up EvalCtx ---
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    for m in &checker_modules {
        ctx.load_module(m);
    }

    // Bind constants from config
    bind_constants_from_config(&mut ctx, &config)
        .with_context(|| "failed to bind constants from config")?;

    // --- Get Init/Next operator definitions ---
    let init_def = ctx
        .get_op(init_name)
        .with_context(|| format!("Init operator '{init_name}' not found in spec"))?
        .clone();
    let next_def = ctx
        .get_op(next_name)
        .with_context(|| format!("Next operator '{next_name}' not found in spec"))?
        .clone();

    // --- Collect state variables ---
    let vars = collect_state_vars(&module, &checker_modules);
    if vars.is_empty() {
        bail!("No state variables found in spec");
    }
    eprintln!(
        "State variables: {:?}",
        vars.iter().map(|v| v.as_ref()).collect::<Vec<_>>()
    );

    // --- Run trace validation ---
    if action_label_mode == ActionLabelMode::Warn {
        eprintln!("Running trace validation (action labels: warn mode)...");
    } else {
        eprintln!("Running trace validation...");
    }
    let mut engine = TraceValidationEngine::new(&mut ctx, &init_def, &next_def, vars)
        .with_action_label_mode(action_label_mode);

    match engine.validate_trace(steps) {
        Ok(success) => {
            for w in &success.warnings {
                eprintln!("Warning: step {}: {}", w.step, w.message);
            }
            println!(
                "OK: trace validated ({} steps, {} total candidates enumerated)",
                success.steps_validated, success.total_candidates_enumerated
            );
            if !success.candidates_per_step.is_empty() {
                let max_candidates = success.candidates_per_step.iter().max().unwrap_or(&0);
                let min_candidates = success.candidates_per_step.iter().min().unwrap_or(&0);
                println!("  candidates per step: min={min_candidates}, max={max_candidates}");
            }
            if !success.warnings.is_empty() {
                println!("  action label warnings: {}", success.warnings.len());
            }
            Ok(())
        }
        Err(e) => {
            bail!("Trace validation failed: {e}");
        }
    }
}

/// Collect state variables from main module and extended modules.
fn collect_state_vars(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
) -> Vec<Arc<str>> {
    use std::collections::HashSet;

    let mut vars = Vec::new();
    let mut seen: HashSet<&str> = HashSet::new();

    // Collect from extended modules first (TLC-style order)
    for ext_mod in checker_modules {
        for unit in &ext_mod.units {
            if let Unit::Variable(var_names) = &unit.node {
                for var in var_names {
                    if seen.insert(var.node.as_str()) {
                        vars.push(Arc::from(var.node.as_str()));
                    }
                }
            }
        }
    }

    // Collect from main module
    for unit in &module.units {
        if let Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                if seen.insert(var.node.as_str()) {
                    vars.push(Arc::from(var.node.as_str()));
                }
            }
        }
    }

    vars
}

/// Sink that collects all trace steps for spec validation.
#[derive(Default)]
struct CollectSink {
    header: Option<TraceHeader>,
    steps: Vec<TraceStep>,
}

impl TraceEventSink for CollectSink {
    fn on_header(&mut self, header: TraceHeader) {
        self.header = Some(header);
    }

    fn on_step(&mut self, step: TraceStep) {
        self.steps.push(step);
    }
}
