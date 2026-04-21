// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod cache_ops;
pub(crate) mod compiled;
mod config;
mod helpers;
mod runner;
mod setup;
mod soundness;
mod storage;

use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::{bail, Context, Result};
use tla_check::{
    error_codes, resolve_spec_from_config_with_extends, AdaptiveChecker, CheckResult, Config,
    ErrorSuggestion, JsonOutput, LivenessExecutionMode, ModelChecker, ParallelChecker, Progress,
    RandomWalkConfig, RandomWalkResult, SearchCompleteness, SoundnessMode, SoundnessProvenance,
    TraceFile, TraceLocationsStorage,
};
use tla_core::{
    lower_error_diagnostic, lower_main_module, parse,
    resolve_with_extends_and_instances_with_options, FileId, ModuleLoader, ResolveOptions,
    SyntaxNode,
};

use crate::cli_schema::{OutputFormat, SoundnessGate};
use crate::{
    cache, check_report, emit_check_cli_error, parse_or_report, read_source, tlc_codes, tlc_tool,
    JsonErrorCtx,
};

pub(crate) use self::config::CheckConfig;
pub(crate) use self::helpers::select_check_deadlock;

use self::cache_ops::{check_cache_hit, update_check_cache, CacheLookupCtx, CacheUpdateCtx};
use self::helpers::{
    apply_alias_transform, apply_allow_incomplete_overflow, make_progress_callback_with_estimate,
    merge_strategy_info, should_report_store_states_auto_enable, skip_liveness_for_benchmark,
};
use self::runner::{print_check_header, run_model_checker, CheckHeaderCtx, ModelCheckerRunCfg};
use self::setup::{
    load_and_parse_config, load_module_set, parse_and_lower, run_semantic_analysis, CheckCtx,
};
use self::soundness::{
    compute_cli_soundness_provenance, enforce_completeness_gate, enforce_soundness_gate,
    GateOutputCtx,
};
use self::storage::{
    log_and_validate_checkpoint, setup_fingerprint_storage, setup_tlc_tool_output,
    setup_trace_storage,
};

pub(crate) fn cmd_check(cfg: CheckConfig) -> Result<()> {
    // Compiled check: generate Rust, compile, and run instead of interpreting.
    if cfg.compiled {
        return compiled::run_compiled_check_with_config(&compiled::CompiledCheckConfig {
            file: &cfg.file,
            config_path: cfg.config_path.as_deref(),
            output_format: cfg.output_format,
            workers: cfg.workers,
            no_deadlock: cfg.no_deadlock,
            max_states: cfg.max_states,
        });
    }

    let file = &cfg.file as &Path;
    let config_path: Option<&Path> = cfg.config_path.as_deref();
    let random_walks = cfg.random_walks;
    let walk_depth = cfg.walk_depth;
    let workers = cfg.workers;
    let no_deadlock = cfg.no_deadlock;
    let max_states = cfg.max_states;
    let max_depth = cfg.max_depth;
    let memory_limit = cfg.memory_limit;
    let disk_limit = cfg.disk_limit;
    let soundness_gate = cfg.soundness_gate;
    let require_exhaustive = cfg.require_exhaustive;
    let bmc_depth = cfg.bmc_depth;
    let _bmc_incremental = cfg.bmc_incremental;
    let pdr_enabled = cfg.pdr_enabled;
    let kinduction_enabled = cfg.kinduction_enabled;
    let kinduction_max_k = cfg.kinduction_max_k;
    let kinduction_incremental = cfg.kinduction_incremental;
    let por_enabled = cfg.por_enabled;
    // Part of #3247: progress is now always-on for Human output (cfg.show_progress unused).
    let show_coverage = cfg.show_coverage;
    let _coverage_guided = cfg.coverage_guided;
    let _coverage_mix_ratio = cfg.coverage_mix_ratio;
    // State space estimation
    let show_estimate = cfg.estimate;
    let estimate_only_levels = cfg.estimate_only;
    let no_trace = cfg.no_trace;
    let store_states = cfg.store_states;
    let initial_capacity = cfg.initial_capacity;
    let mmap_fingerprints = cfg.mmap_fingerprints;
    let huge_pages = cfg.huge_pages;
    let disk_fingerprints = cfg.disk_fingerprints;
    let mmap_dir = cfg.mmap_dir;
    let trace_file_path = cfg.trace_file_path;
    let mmap_trace_locations = cfg.mmap_trace_locations;
    let checkpoint_dir = cfg.checkpoint_dir;
    let checkpoint_interval = cfg.checkpoint_interval;
    let resume_from = cfg.resume_from;
    let output_format = cfg.output_format;
    let trace_format = cfg.trace_format;
    let difftrace = cfg.difftrace;
    let explain_trace = cfg.explain_trace;
    let continue_on_error = cfg.continue_on_error;
    let allow_incomplete = cfg.allow_incomplete;
    let force = cfg.force;
    let profile_enum = cfg.profile_enum;
    let profile_enum_detail = cfg.profile_enum_detail;
    let profile_eval = cfg.profile_eval;
    let pipeline_enabled = cfg.pipeline;
    let strategy_arg = cfg.strategy;
    let fused_enabled = cfg.fused;
    let portfolio_enabled = cfg.portfolio;
    let portfolio_strategies = cfg.portfolio_strategies;
    let liveness_mode = cfg.liveness_mode;
    let jit_verify = cfg.jit_verify;
    let show_tiers = cfg.show_tiers;
    let type_specialize = cfg.type_specialize;
    // Part of #3759: CLI overrides for Init/Next/Invariant operators.
    let cli_init = cfg.cli_init;
    let cli_next = cfg.cli_next;
    let cli_invariants = cfg.cli_invariants;
    // Part of #3779: CLI overrides for --prop and --const.
    let cli_properties = cfg.cli_properties;
    let cli_constants = cfg.cli_constants;
    // Part of #3779: --no-config skips .cfg file entirely.
    let no_config = cfg.no_config;
    // Part of #3756: Inductive invariant check (Apalache Gap 8).
    let inductive_check_invariant = cfg.inductive_check_invariant;
    let trace_invariants = cfg.trace_invariants;
    // Part of #3757: Symbolic simulation (Apalache Gap 9).
    let symbolic_sim = cfg.symbolic_sim;
    let _symbolic_sim_runs = cfg.symbolic_sim_runs;
    let _symbolic_sim_length = cfg.symbolic_sim_length;
    // Parse collision detection mode.
    let collision_check_mode = tla_check::CollisionCheckMode::from_str_arg(&cfg.collision_check)
        .map_err(|e| anyhow::anyhow!("invalid --collision-check value: {e}"))?;
    // Set profiling env vars before any model checking code runs.
    // The checker code uses OnceLock-cached env checks, so these must be set early.
    if profile_enum {
        std::env::set_var("TLA2_PROFILE_ENUM", "1");
    }
    if profile_enum_detail {
        std::env::set_var("TLA2_PROFILE_ENUM_DETAIL", "1");
    }
    if profile_eval {
        std::env::set_var("TLA2_PROFILE_EVAL", "1");
    }
    if show_tiers {
        std::env::set_var("TLA2_SHOW_TIERS", "1");
    }
    // Part of #3989: Wire --type-specialize flag to the TLA2_JIT_SPECULATION env var.
    // The SpeculativeState orchestrator reads this at construction time.
    match type_specialize {
        crate::cli_schema::TypeSpecializeArg::Off => {
            std::env::set_var("TLA2_JIT_SPECULATION", "0");
        }
        crate::cli_schema::TypeSpecializeArg::On => {
            std::env::set_var("TLA2_JIT_SPECULATION", "1");
        }
        crate::cli_schema::TypeSpecializeArg::Auto => {
            // Auto: don't override the env var — let the default behavior
            // (enabled when JIT is active) take effect.
        }
    }
    let completeness = SearchCompleteness::from_bounds(max_states, max_depth);
    let mut json_err_ctx = JsonErrorCtx {
        output_format,
        spec_file: file,
        config_file: config_path,
        module_name: None,
        workers,
        completeness,
    };
    if bmc_depth > 0 && matches!(output_format, OutputFormat::TlcTool) {
        bail!("BMC output is not supported in --output tlc-tool mode");
    }
    let mut tool_out = setup_tlc_tool_output(output_format, workers)?;
    let check_ctx = CheckCtx {
        file,
        config_path,
        workers,
        max_states,
        max_depth,
        output_format,
    };

    // Part of #3754: Quint JSON IR path.
    let quint_mode = cfg.quint;

    // Parse and lower the source file (TLA+ or Quint JSON IR).
    let (source, tree, module) = if quint_mode {
        let source = read_source(file)?;
        let modules = tla_core::quint::parse_quint_json(&source)
            .map_err(|e| anyhow::anyhow!("Quint JSON import failed: {e}"))?;
        let module = modules
            .into_iter()
            .next()
            .ok_or_else(|| anyhow::anyhow!("Quint JSON contains no modules"))?;
        // For Quint specs, create a dummy syntax tree (not used for module loading).
        let dummy_tree = SyntaxNode::new_root(parse("").green_node);
        (source, dummy_tree, module)
    } else {
        parse_and_lower(file, &json_err_ctx, output_format)?
    };
    json_err_ctx.module_name = Some(&module.name.node);

    if let Some(out) = tool_out.as_mut() {
        out.emit(
            tlc_codes::ec::TLC_SANY_END,
            tlc_codes::mp::NONE,
            tlc_tool::format_tlc_sany_end_message(),
        );
    }

    // Load extended and instanced modules.
    let mut loader = ModuleLoader::new(file);
    if !quint_mode {
        loader.seed_from_syntax_tree(&tree, file);
    }

    let extended_module_names = load_module_set(
        &mut loader,
        &module,
        |l, m| Ok(l.load_extends(m)?),
        "extended",
        &check_ctx,
    )?;
    let instance_module_names = load_module_set(
        &mut loader,
        &module,
        |l, m| Ok(l.load_instances(m)?),
        "instanced",
        &check_ctx,
    )?;

    let mut all_module_names: Vec<String> = extended_module_names.clone();
    for name in instance_module_names {
        if !all_module_names.contains(&name) {
            all_module_names.push(name);
        }
    }

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);

    let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
        .iter()
        .chain(instanced_modules_for_resolve.iter())
        .map(|m| m.name.node.as_str())
        .collect();
    let extended_syntax_trees: Vec<_> = spec_scope_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.syntax_tree))
        .collect();

    // Skip semantic analysis for Quint specs (already resolved by Quint compiler).
    if !quint_mode {
        run_semantic_analysis(
            &module,
            &extended_modules_for_resolve,
            &instanced_modules_for_resolve,
            &json_err_ctx,
            file,
            output_format,
        )?;
    }

    // Part of #3779: --no-config skips .cfg file entirely. Use convention
    // names "Init" and "Next" as defaults (overridable by --init/--next).
    // Part of #3759: Determine if CLI flags can substitute for a missing .cfg.
    let has_cli_init_next = cli_init.is_some() && cli_next.is_some();
    let (config_path, config_source, mut config) = if no_config {
        let cfg_path = {
            let mut p = file.to_path_buf();
            p.set_extension("cfg");
            p
        };
        let mut default_config = Config::default();
        default_config.init = Some("Init".to_string());
        default_config.next = Some("Next".to_string());
        (cfg_path, String::new(), default_config)
    } else {
        load_and_parse_config(
            file,
            config_path,
            &json_err_ctx,
            output_format,
            has_cli_init_next,
        )?
    };

    // Part of #3759: Apply CLI overrides for --init, --next, --inv.
    // CLI flags take precedence over .cfg values. When CLI provides both
    // --init and --next, clear any SPECIFICATION from .cfg to avoid the
    // mutual-exclusivity check.
    if let Some(ref init_op) = cli_init {
        config.init = Some(init_op.clone());
    }
    if let Some(ref next_op) = cli_next {
        config.next = Some(next_op.clone());
    }
    if cli_init.is_some() && cli_next.is_some() && config.specification.is_some() {
        config.specification = None;
    }
    if !cli_invariants.is_empty() {
        config.invariants = cli_invariants;
    }
    // Part of #3779: CLI --prop overrides for temporal properties.
    if !cli_properties.is_empty() {
        config.properties = cli_properties;
    }
    // Part of #3779: CLI --const overrides for constant assignments.
    // Format: NAME=VALUE where VALUE is a TLA+ expression.
    if !cli_constants.is_empty() {
        config.constants.clear();
        config.constants_order.clear();
        for assignment in &cli_constants {
            if let Some((name, value)) = assignment.split_once('=') {
                let name = name.trim().to_string();
                let value = value.trim().to_string();
                config.add_constant(name, tla_check::ConstantValue::Value(value));
            } else {
                bail!(
                    "Invalid --const format: {:?}. Expected NAME=VALUE (e.g., --const N=3)",
                    assignment,
                );
            }
        }
    }
    // Part of #3752: trace invariants from CLI --trace-inv flags.
    if !trace_invariants.is_empty() {
        config.trace_invariants = trace_invariants;
    }

    config.liveness_execution = match liveness_mode {
        crate::cli_schema::LivenessModeArg::Full => LivenessExecutionMode::Full,
        crate::cli_schema::LivenessModeArg::OnTheFly => LivenessExecutionMode::OnTheFly,
    };

    // Set POR from CLI flag (Part of #541)
    if por_enabled {
        config.por_enabled = true;
    }
    config.jit_verify = jit_verify;

    // Part of #3175: Liveness checking no longer requires store_full_states.
    // Both sequential and parallel checkers cache BFS-time liveness data in fp-only
    // mode, so the auto-enable is no longer needed. Users can still use --store-states
    // for full counterexample trace reconstruction.
    let skip_liveness_for_benchmark = skip_liveness_for_benchmark();
    let has_properties = !config.properties.is_empty();
    // Part of #3175/#3222: --no-trace affects trace reconstruction, not whether
    // temporal properties are checked. Fp-only liveness replays from cached BFS
    // data, and symmetry+liveness upgrades to full-state storage in the checker.
    let soundness = compute_cli_soundness_provenance(
        pdr_enabled,
        config.por_enabled,
        bmc_depth,
        completeness,
        has_properties,
        skip_liveness_for_benchmark,
    );

    // Enforce gating before any cache hit or model checking.
    let gate_ctx = GateOutputCtx {
        file,
        config_path: &config_path,
        module_name: &module.name.node,
        workers,
        output_format,
    };
    enforce_soundness_gate(soundness_gate, &soundness, completeness, &gate_ctx)?;
    enforce_completeness_gate(require_exhaustive, &soundness, completeness, &gate_ctx)?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive — use one or the other");
    }

    // Resolve Init/Next/Fairness from SPECIFICATION if needed
    // Also search extended modules for the SPECIFICATION operator
    let mut resolved_fairness = Vec::new();
    let mut resolved_spec: Option<tla_check::ResolvedSpec> = None;
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        match resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees) {
            Ok(resolved) => {
                if config.init.is_none() {
                    config.init = Some(resolved.init.clone());
                }
                if config.next.is_none() {
                    config.next = Some(resolved.next.clone());
                }
                // Capture fairness constraints for liveness checking
                resolved_fairness = resolved.fairness.clone();
                // Store full resolved spec for inline NEXT handling
                resolved_spec = Some(resolved);
            }
            Err(e) => {
                bail!("Failed to resolve SPECIFICATION: {}", e);
            }
        }
    }

    let store_states_auto_enabled = should_report_store_states_auto_enable(
        &module,
        &checker_modules,
        &config,
        no_trace,
        store_states,
    )?;

    // Print header (only for human output format)
    if matches!(output_format, OutputFormat::Human) {
        print_check_header(&CheckHeaderCtx {
            file,
            config_path: &config_path,
            config: &config,
            workers,
            continue_on_error,
            max_states,
            max_depth,
            memory_limit,
            disk_limit,
            store_states,
            store_states_auto_enabled,
            no_trace,
            skip_liveness_for_benchmark,
            soundness: &soundness,
            completeness,
        });
    }

    // Incremental caching (Part of #706)
    let cache_path = cache::default_cache_path();
    let mut cache_file = match cache::load_cache(&cache_path) {
        Ok(c) => c,
        Err(e) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!(
                    "Warning: failed to load cache {}: {e}",
                    cache_path.display()
                );
            }
            cache::CacheFile::empty()
        }
    };

    let cache_key = cache::canonical_string(file);
    let config_key = cache::canonical_string(&config_path);

    let mut dependency_paths = Vec::new();
    for name in &all_module_names {
        if let Some(loaded) = loader.get(name) {
            if loaded.path != file {
                dependency_paths.push(loaded.path.clone());
            }
        }
    }
    let dependencies = cache::dependency_paths_to_strings(dependency_paths);

    let check_deadlock = select_check_deadlock(no_deadlock, resolved_spec.as_ref(), &config);

    let cache_options = cache::CheckOptions {
        no_deadlock,
        check_deadlock,
        max_states: max_states as u64,
        max_depth: max_depth as u64,
        bmc_depth: bmc_depth as u64,
        pdr_enabled,
        por_enabled,
        continue_on_error,
    };

    let signature = cache::compute_signature(
        file,
        source.as_bytes(),
        &config_path,
        config_source.as_bytes(),
        &dependencies,
        &cache_options,
    )
    .with_context(|| format!("compute cache signature for {}", file.display()))?;

    if check_cache_hit(&CacheLookupCtx {
        cache_file: &cache_file,
        cache_key: &cache_key,
        config_key: &config_key,
        signature: &signature,
        force,
        output_format,
        max_states,
        max_depth,
    })? {
        return Ok(());
    }

    // Multi-phase verification pipeline (Part of #3723).
    // --strategy <name> implies pipeline mode with a named strategy.
    // --pipeline (without --strategy) uses the default auto strategy.
    let effective_strategy = match strategy_arg {
        Some(crate::cli_schema::StrategyArg::Quick) => Some(tla_check::VerificationStrategy::Quick),
        Some(crate::cli_schema::StrategyArg::Full) => Some(tla_check::VerificationStrategy::Full),
        Some(crate::cli_schema::StrategyArg::Auto) => Some(tla_check::VerificationStrategy::Auto),
        None if pipeline_enabled => Some(tla_check::VerificationStrategy::Auto),
        None => None,
    };
    if let Some(strategy) = effective_strategy {
        return runner::run_pipeline_mode_with_strategy(
            &module,
            &checker_modules,
            &config,
            strategy,
            output_format,
        );
    }

    // Portfolio racing: parallel BFS + symbolic strategies (Part of #3717).
    if portfolio_enabled {
        return runner::run_portfolio_mode(
            &module,
            &checker_modules,
            &config,
            &portfolio_strategies,
            output_format,
        );
    }

    // Cooperative fused BFS+symbolic verification (Part of #3770).
    // Part of #3826: auto-escalate to fused mode when static analysis detects
    // exponential state space patterns (e.g., SUBSET(SUBSET Nodes)). The
    // evaluator's nested powerset optimization handles the combinatorial
    // reduction, but we still want symbolic engines running in parallel
    // for additional verification coverage.
    #[cfg(feature = "z4")]
    let fused_enabled = fused_enabled || {
        if let Some(ref signal) = tla_check::detect_exponential_complexity(&module) {
            eprintln!(
                "Auto-enabling fused mode: {} — BFS with evaluator optimization + symbolic engines",
                signal.reason
            );
            true
        } else {
            false
        }
    };
    if fused_enabled {
        return runner::run_fused_mode(
            &module,
            &checker_modules,
            &config,
            output_format,
            file,
            Some(config_path.as_path()),
            workers,
            completeness,
        );
    }

    // BMC mode (Part of #3702) - symbolic bounded bug finding via SAT unrolling.
    #[cfg(feature = "z4")]
    if bmc_depth > 0 {
        return runner::run_bmc_mode(
            &module,
            &checker_modules,
            &config,
            bmc_depth,
            _bmc_incremental,
            output_format,
        );
    }
    #[cfg(not(feature = "z4"))]
    if bmc_depth > 0 {
        bail!("BMC mode requires the z4 feature. Rebuild with --features z4");
    }

    // PDR mode (Part of #642, #3576) - symbolic safety checking via CHC/IC3.
    // Placed before explicit-state storage/checkpoint setup to avoid
    // initializing infrastructure that the symbolic runner cannot use.
    #[cfg(feature = "z4")]
    if pdr_enabled {
        return runner::run_pdr_mode(&module, &checker_modules, &config, output_format);
    }
    #[cfg(not(feature = "z4"))]
    if pdr_enabled {
        bail!("PDR mode requires the z4 feature. Rebuild with --features z4");
    }

    // K-induction mode (Part of #3722) - symbolic safety proving via inductive step.
    // Placed after BMC/PDR but before explicit-state storage to avoid
    // initializing infrastructure that the symbolic runner cannot use.
    #[cfg(feature = "z4")]
    if kinduction_enabled {
        return runner::run_kinduction_mode(
            &module,
            &checker_modules,
            &config,
            kinduction_max_k,
            kinduction_incremental,
            output_format,
        );
    }
    #[cfg(not(feature = "z4"))]
    if kinduction_enabled {
        bail!("K-induction mode requires the z4 feature. Rebuild with --features z4");
    }
    // Suppress unused warnings for kinduction fields in non-z4 builds.
    #[cfg(not(feature = "z4"))]
    let _ = kinduction_max_k;
    #[cfg(not(feature = "z4"))]
    let _ = kinduction_incremental;

    // Inductive invariant check mode (Part of #3756, Apalache Gap 8).
    #[cfg(feature = "z4")]
    if let Some(ref ind_inv) = inductive_check_invariant {
        return runner::run_inductive_check_mode(
            &module,
            &checker_modules,
            &config,
            ind_inv,
            output_format,
        );
    }
    #[cfg(not(feature = "z4"))]
    if inductive_check_invariant.is_some() {
        bail!("Inductive check mode requires the z4 feature. Rebuild with --features z4");
    }

    // Symbolic simulation mode (Part of #3757, Apalache Gap 9).
    #[cfg(feature = "z4")]
    if symbolic_sim {
        return runner::run_symbolic_sim_mode(
            &module,
            &checker_modules,
            &config,
            _symbolic_sim_runs,
            _symbolic_sim_length,
            output_format,
        );
    }
    #[cfg(not(feature = "z4"))]
    if symbolic_sim {
        bail!("Symbolic simulation mode requires the z4 feature. Rebuild with --features z4");
    }

    let fingerprint_storage = setup_fingerprint_storage(
        mmap_fingerprints,
        huge_pages,
        disk_fingerprints,
        initial_capacity,
        store_states,
        &mmap_dir,
        output_format,
    )?;

    let (trace_file, trace_locs_storage) = setup_trace_storage(
        &trace_file_path,
        store_states,
        mmap_trace_locations,
        &mmap_dir,
        output_format,
    )?;

    let progress_callback = make_progress_callback_with_estimate(show_estimate);

    // --estimate-only: set max_depth to limit exploration to N levels.
    let max_depth = if let Some(levels) = estimate_only_levels {
        if max_depth > 0 && max_depth < levels {
            max_depth
        } else {
            levels
        }
    } else {
        max_depth
    };

    log_and_validate_checkpoint(
        &checkpoint_dir,
        checkpoint_interval,
        &resume_from,
        workers,
        output_format,
    )?;

    if let Some(out) = tool_out.as_mut() {
        out.emit(
            tlc_codes::ec::TLC_MODE_MC,
            tlc_codes::mp::NONE,
            &tlc_tool::format_tlc_mode_message(workers.max(1)),
        );
        let now = chrono::Utc::now().format("%Y-%m-%d %H:%M:%S").to_string();
        out.emit(
            tlc_codes::ec::TLC_STARTING,
            tlc_codes::mp::NONE,
            &tlc_tool::format_tlc_starting_message(&now),
        );
    }

    // Pre-compute file path mappings for all loaded modules.
    let file_paths: Vec<(FileId, PathBuf)> = all_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| (l.file_id, l.path.clone())))
        .collect();

    // Random walk witness search (Part of #3720)
    // Runs before exhaustive BFS for fast shallow bug detection.
    if random_walks > 0 {
        if matches!(output_format, OutputFormat::Human) {
            eprintln!(
                "Running {} random walk(s) (up to {} steps each) before exhaustive BFS...",
                random_walks, walk_depth,
            );
        }
        let walk_config = RandomWalkConfig {
            num_walks: random_walks,
            max_depth: walk_depth,
            seed: None,
        };
        let runtime_config = config.runtime_model_config();
        let mut walk_checker =
            ModelChecker::new_with_extends(&module, &checker_modules, &runtime_config);
        walk_checker.set_deadlock_check(check_deadlock);
        let walk_result = walk_checker.random_walk(&walk_config);
        match walk_result {
            RandomWalkResult::InvariantViolation {
                ref invariant,
                ref trace,
                walk_id,
                depth,
            } => {
                if matches!(output_format, OutputFormat::Human) {
                    eprintln!(
                        "Random walk {} found invariant violation `{}` at depth {}",
                        walk_id, invariant, depth,
                    );
                }
                let check_result = CheckResult::InvariantViolation {
                    invariant: invariant.clone(),
                    trace: trace.clone(),
                    stats: tla_check::CheckStats::default(),
                };
                check_report::report_check_human(
                    check_result,
                    std::time::Duration::ZERO,
                    max_states,
                    max_depth,
                    trace_format,
                    difftrace,
                    explain_trace,
                )?;
                return Ok(());
            }
            RandomWalkResult::Deadlock {
                ref trace,
                walk_id,
                depth,
            } => {
                if matches!(output_format, OutputFormat::Human) {
                    eprintln!("Random walk {} found deadlock at depth {}", walk_id, depth,);
                }
                let check_result = CheckResult::Deadlock {
                    trace: trace.clone(),
                    stats: tla_check::CheckStats::default(),
                };
                check_report::report_check_human(
                    check_result,
                    std::time::Duration::ZERO,
                    max_states,
                    max_depth,
                    trace_format,
                    difftrace,
                    explain_trace,
                )?;
                return Ok(());
            }
            RandomWalkResult::NoViolationFound {
                walks_completed,
                total_steps,
            } => {
                if matches!(output_format, OutputFormat::Human) {
                    eprintln!(
                        "Random walks complete: {} walk(s), {} total steps, no violation found. Proceeding to exhaustive BFS...",
                        walks_completed, total_steps,
                    );
                }
            }
            RandomWalkResult::Error(e) => {
                if matches!(output_format, OutputFormat::Human) {
                    eprintln!(
                        "Warning: random walk failed: {}. Proceeding to exhaustive BFS...",
                        e,
                    );
                }
            }
        }
    }

    // Run model checker
    let start = Instant::now();
    let (result, strategy_info) = run_model_checker(ModelCheckerRunCfg {
        module: &module,
        checker_modules: &checker_modules,
        config: &config,
        workers,
        file,
        file_paths,
        resolved_spec: &resolved_spec,
        check_deadlock,
        show_coverage,
        continue_on_error,
        store_states,
        no_trace,
        fingerprint_storage: &fingerprint_storage,
        trace_file,
        trace_locs_storage,
        resolved_fairness: &resolved_fairness,
        max_states,
        max_depth,
        memory_limit,
        disk_limit,
        output_format,
        progress_callback,
        checkpoint_dir: &checkpoint_dir,
        checkpoint_interval,
        resume_from: &resume_from,
        config_path: &config_path,
        tool_out: &mut tool_out,
        collision_check_mode,
    })?;
    let elapsed = start.elapsed();

    // Update cache on PASS only (Part of #706).
    update_check_cache(CacheUpdateCtx {
        result: &result,
        cache_file: &mut cache_file,
        cache_path: &cache_path,
        cache_key: &cache_key,
        config_key: &config_key,
        signature: &signature,
        config: &config,
        dependencies: &dependencies,
        cache_options: &cache_options,
        elapsed,
        output_format,
    });

    let (result, incomplete_note) =
        apply_allow_incomplete_overflow(result, allow_incomplete, output_format);
    let strategy_info = merge_strategy_info(strategy_info, incomplete_note);

    // Part of #3012: Apply ALIAS transformation to traces before reporting.
    // TLC evaluates the ALIAS operator per-state in counterexample traces,
    // replacing raw state variables with user-defined views.
    let result = apply_alias_transform(
        result,
        &config,
        &module,
        &checker_modules,
        &extended_modules_for_resolve,
    );

    // Report results based on output format
    match output_format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            check_report::report_check_json(&check_report::JsonReportCtx {
                output_format,
                checker_modules: &checker_modules,
                module: &module,
                file,
                config_path: &config_path,
                workers,
                soundness: &soundness,
                completeness,
                config: &config,
                result: &result,
                elapsed,
                strategy_info: strategy_info.as_deref(),
                max_states,
                max_depth,
            })
        }
        OutputFormat::TlcTool => check_report::report_check_tlc_tool(tool_out, &result, elapsed),
        OutputFormat::Itf => check_report::report_check_itf(&result),
        OutputFormat::Human => {
            let report_result = check_report::report_check_human(
                result,
                elapsed,
                max_states,
                max_depth,
                trace_format,
                difftrace,
                explain_trace,
            );
            if let Some(ref info) = strategy_info {
                println!();
                println!("{info}");
            }
            report_result
        }
    }
}

#[cfg(test)]
mod tests;
