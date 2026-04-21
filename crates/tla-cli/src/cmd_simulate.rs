// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `simulate` subcommand: random trace generation for TLA+ specifications.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use tla_check::{
    resolve_spec_from_config_with_extends, Config, ModelChecker, SimulationConfig, SimulationResult,
};
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader};

use crate::{parse_or_report, read_source};

pub(crate) fn cmd_simulate(
    file: &Path,
    config_path: Option<&Path>,
    num_traces: usize,
    max_trace_length: usize,
    seed: u64,
    no_invariants: bool,
) -> Result<()> {
    // Parse the TLA+ source file
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

    // Load extended modules
    let mut loader = ModuleLoader::new(file);

    // Seed the loader cache with inline modules from the main file.
    loader.seed_from_syntax_tree(&tree, file);

    let _extended_module_names = match loader.load_extends(&module) {
        Ok(names) => {
            if !names.is_empty() {
                eprintln!("Loaded extended modules: {}", names.join(", "));
            }
            names
        }
        Err(e) => {
            bail!("Failed to load extended modules: {}", e);
        }
    };

    let _instance_module_names = match loader.load_instances(&module) {
        Ok(names) => {
            if !names.is_empty() {
                eprintln!("Loaded instanced modules: {}", names.join(", "));
            }
            names
        }
        Err(e) => {
            bail!("Failed to load instanced modules: {}", e);
        }
    };

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);

    // Build the module slice passed into the model checker. The prefix ordering is load-bearing
    // for TLC-style unqualified imports (EXTENDS + standalone INSTANCE).
    let checker_modules = loader.modules_for_model_checking(&module);

    // Find and parse config file
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

    let mut config = Config::parse(&config_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive — use one or the other");
    }

    // Resolve Init/Next from SPECIFICATION if needed
    let mut sim_resolved_spec: Option<tla_check::ResolvedSpec> = None;
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
            .iter()
            .chain(instanced_modules_for_resolve.iter())
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
                sim_resolved_spec = Some(resolved);
            }
            Err(e) => {
                bail!("Failed to resolve SPECIFICATION: {}", e);
            }
        }
    }
    config.normalize_resolved_specification();

    // Print header
    println!("Simulating: {}", file.display());
    println!("Config: {}", config_path.display());
    if let Some(ref init) = config.init {
        println!("INIT: {}", init);
    }
    if let Some(ref next) = config.next {
        println!("NEXT: {}", next);
    }
    if !config.invariants.is_empty() && !no_invariants {
        println!("INVARIANTS: {}", config.invariants.join(", "));
    }
    println!("Traces: {}", num_traces);
    println!("Max trace length: {}", max_trace_length);
    if seed != 0 {
        println!("Seed: {}", seed);
    }
    println!();

    // Configure simulation
    // Use Default + field assignment because SimulationConfig is #[non_exhaustive]
    let mut sim_config = SimulationConfig::default();
    sim_config.num_traces = num_traces;
    sim_config.max_trace_length = max_trace_length;
    sim_config.seed = if seed == 0 { None } else { Some(seed) };
    sim_config.check_invariants = !no_invariants;
    sim_config.action_constraints = config.action_constraints.clone();

    // Run simulation
    let start = Instant::now();
    let mut checker = ModelChecker::new_with_extends(&module, &checker_modules, &config);
    // Register inline NEXT expression if present
    if let Some(ref resolved) = sim_resolved_spec {
        checker.register_inline_next(resolved)?;
    }
    let result = checker.simulate(&sim_config);
    let elapsed = start.elapsed();

    match result {
        SimulationResult::Success(stats) => {
            println!("Simulation complete: No errors found.");
            println!();
            println!("Statistics:");
            println!("  Traces generated: {}", stats.traces_generated);
            println!("  States visited: {}", stats.states_visited);
            println!("  Distinct states: {}", stats.distinct_states);
            println!("  Transitions: {}", stats.transitions);
            println!("  Max trace length: {}", stats.max_trace_length);
            println!("  Avg trace length: {:.1}", stats.avg_trace_length);
            println!("  Deadlocked traces: {}", stats.deadlocked_traces);
            println!("  Truncated traces: {}", stats.truncated_traces);
            println!("  Time: {:.3}s", elapsed.as_secs_f64());
            let states_per_sec = if elapsed.as_secs_f64() > 0.0 {
                stats.states_visited as f64 / elapsed.as_secs_f64()
            } else {
                0.0
            };
            println!("  States/sec: {:.0}", states_per_sec);
            Ok(())
        }
        SimulationResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            eprintln!(
                "Error: Invariant '{}' violated during simulation!",
                invariant
            );
            eprintln!();
            eprintln!("Counterexample trace ({} states):", trace.len());
            eprintln!("{}", trace);
            eprintln!("Statistics:");
            eprintln!("  Traces generated: {}", stats.traces_generated);
            eprintln!("  States visited: {}", stats.states_visited);
            eprintln!("  Distinct states: {}", stats.distinct_states);
            eprintln!("  Time: {:.3}s", elapsed.as_secs_f64());
            bail!("Invariant violation detected during simulation");
        }
        SimulationResult::Deadlock { trace, stats } => {
            eprintln!("Error: Deadlock reached during simulation!");
            eprintln!();
            eprintln!("Counterexample trace ({} states):", trace.len());
            eprintln!("{}", trace);
            eprintln!("Statistics:");
            eprintln!("  Traces generated: {}", stats.traces_generated);
            eprintln!("  States visited: {}", stats.states_visited);
            eprintln!("  Distinct states: {}", stats.distinct_states);
            eprintln!("  Time: {:.3}s", elapsed.as_secs_f64());
            bail!("Deadlock detected during simulation");
        }
        SimulationResult::Error { error, stats } => {
            eprintln!("Error: {}", error);
            eprintln!();
            eprintln!("Statistics:");
            eprintln!("  Traces generated: {}", stats.traces_generated);
            eprintln!("  States visited: {}", stats.states_visited);
            eprintln!("  Time: {:.3}s", elapsed.as_secs_f64());
            bail!("Simulation failed: {}", error);
        }
        _ => bail!(
            "Simulation produced a result variant unsupported by this tla2 version; upgrade tla2"
        ),
    }
}
