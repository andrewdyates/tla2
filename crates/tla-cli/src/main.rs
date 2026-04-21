// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[cfg(all(feature = "mimalloc", not(feature = "dhat-heap")))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod cache;
mod check_report;
mod cli_schema;
mod cmd_abstract;
mod cmd_audit;
mod cmd_bench;
mod cmd_bisect;
mod cmd_bound;
#[cfg(feature = "z4")]
mod cmd_aiger;
#[cfg(feature = "z4")]
mod cmd_btor2;
mod cmd_check;
mod cmd_codegen;
mod cmd_compare;
mod cmd_completions;
mod cmd_compose;
mod cmd_constrain;
mod cmd_deadlock;
mod cmd_convert;
mod cmd_coverage;
mod cmd_deps;
mod cmd_diagnose;
mod cmd_diff;
mod cmd_doc;
mod cmd_explain;
mod cmd_explore;
mod cmd_fmt;
mod cmd_graph;
mod cmd_import;
mod cmd_init;
mod cmd_inline;
mod cmd_lint;
mod cmd_merge;
mod cmd_minimize;
mod cmd_modeldiff;
mod cmd_partition;
mod cmd_profile;
mod cmd_project;
mod cmd_refactor;
mod cmd_reach;
mod cmd_refine;
mod cmd_repair;
mod cmd_scope;
mod cmd_search;
mod cmd_slice;
mod cmd_petri;
#[cfg(feature = "prove")]
mod cmd_prove;
mod cmd_simulate;
mod cmd_simreport;
mod cmd_actiongraph;
mod cmd_assumeguarantee;
mod cmd_census;
mod cmd_equiv;
mod cmd_induct;
mod cmd_invgen;
mod cmd_lasso;
mod cmd_predicateabs;
mod cmd_snapshot;
mod cmd_statefilter;
mod cmd_symmetry;
mod cmd_stats;
mod cmd_tracegen;
mod cmd_summary;
mod cmd_template;
mod cmd_test;
mod cmd_threadcheck;
mod cmd_typecheck;
mod cmd_unfold;
mod cmd_validate;
mod cmd_vmt;
mod cmd_watch;
mod cmd_witness;
mod cmd_sandbox;
mod cmd_timeline;
mod cmd_metric;
mod cmd_scaffold;
mod cmd_stutter;
mod cmd_quorum;
mod cmd_fingerprint;
mod cmd_normalize;
mod cmd_countex;
mod cmd_heatmap;
mod cmd_protocol;
mod cmd_hierarchy;
mod cmd_crossref;
mod cmd_invariantgen;
mod cmd_drift;
mod cmd_safety;
mod cmd_livenesscheck;
mod cmd_translate;
mod cmd_tableau;
mod cmd_alphabet;
mod cmd_weight;
mod cmd_absorb;
mod cmd_cluster;
mod cmd_rename;
mod cmd_reachset;
mod cmd_guard;
mod cmd_symmetrydetect;
mod cmd_deadlockfree;
mod cmd_actioncount;
mod cmd_constcheck;
mod cmd_specinfo;
mod cmd_vartrack;
mod cmd_cfggen;
mod cmd_depgraph;
mod cmd_initcount;
mod cmd_branchfactor;
mod cmd_stategraph;
mod cmd_predicate;
mod cmd_moduleinfo;
mod cmd_oparity;
mod cmd_unusedvar;
mod cmd_exprcount;
mod cmd_specsize;
mod cmd_constlist;
mod cmd_varlist;
mod cmd_unusedconst;
mod cmd_astdepth;
mod cmd_oplist;
mod cmd_extends;
mod cmd_setops;
mod cmd_quantcount;
mod cmd_primecount;
mod cmd_ifcount;
mod cmd_letcount;
mod cmd_choosecount;
mod cmd_casecount;
mod cmd_recordops;
mod cmd_temporalops;
mod cmd_unchanged;
mod cmd_enabled;
mod helpers;
mod tlc_codes;
mod tlc_tool;
mod trace_cmd;

pub(crate) use helpers::{emit_check_cli_error, parse_or_report, read_source, JsonErrorCtx};

use std::time::Instant;

use self::cli_schema::{Cli, Command, OutputFormat};
use self::cmd_check::{cmd_check, CheckConfig};
use self::cmd_petri::{cmd_mcc, cmd_petri, cmd_petri_simplify};
use anyhow::{bail, Context, Result};
use clap::Parser;
use tla_check::{error_codes, ErrorSuggestion, SearchCompleteness};

fn incompatible_check_simulate_flags(
    workers: usize,
    no_deadlock: bool,
    max_states: usize,
    max_depth: usize,
    memory_limit: usize,
    disk_limit: usize,
    soundness: cli_schema::SoundnessGate,
    require_exhaustive: bool,
    bmc: usize,
    #[cfg(feature = "z4")] pdr: bool,
    #[cfg(feature = "z4")] kinduction: bool,
    pipeline: bool,
    strategy: &Option<cli_schema::StrategyArg>,
    por: bool,
    coverage: bool,
    no_trace: bool,
    store_states: bool,
    initial_capacity: Option<usize>,
    mmap_fingerprints: Option<usize>,
    disk_fingerprints: Option<usize>,
    mmap_dir: &Option<std::path::PathBuf>,
    trace_file: &Option<std::path::PathBuf>,
    mmap_trace_locations: Option<usize>,
    checkpoint: &Option<std::path::PathBuf>,
    checkpoint_interval: u64,
    resume: &Option<std::path::PathBuf>,
    output: OutputFormat,
    tool: bool,
    trace_format: cli_schema::TraceFormat,
    difftrace: bool,
    continue_on_error: bool,
    allow_incomplete: bool,
    force: bool,
    profile_enum: bool,
    profile_enum_detail: bool,
    profile_eval: bool,
    liveness_mode: cli_schema::LivenessModeArg,
) -> Vec<&'static str> {
    let mut incompatible = Vec::new();
    if workers != 0 {
        incompatible.push("--workers");
    }
    if no_deadlock {
        incompatible.push("--no-deadlock");
    }
    if max_states != 0 {
        incompatible.push("--max-states");
    }
    if max_depth != 0 {
        incompatible.push("--max-depth");
    }
    if memory_limit != 0 {
        incompatible.push("--memory-limit");
    }
    if disk_limit != 0 {
        incompatible.push("--disk-limit");
    }
    if !matches!(soundness, cli_schema::SoundnessGate::Sound) {
        incompatible.push("--soundness");
    }
    if require_exhaustive {
        incompatible.push("--require-exhaustive");
    }
    if bmc != 0 {
        incompatible.push("--bmc");
    }
    #[cfg(feature = "z4")]
    if pdr {
        incompatible.push("--pdr");
    }
    #[cfg(feature = "z4")]
    if kinduction {
        incompatible.push("--kinduction");
    }
    if pipeline {
        incompatible.push("--pipeline");
    }
    if strategy.is_some() {
        incompatible.push("--strategy");
    }
    if por {
        incompatible.push("--por");
    }
    if coverage {
        incompatible.push("--coverage");
    }
    if no_trace {
        incompatible.push("--no-trace");
    }
    if store_states {
        incompatible.push("--store-states");
    }
    if initial_capacity.is_some() {
        incompatible.push("--initial-capacity");
    }
    if mmap_fingerprints.is_some() {
        incompatible.push("--mmap-fingerprints");
    }
    if disk_fingerprints.is_some() {
        incompatible.push("--disk-fingerprints");
    }
    if mmap_dir.is_some() {
        incompatible.push("--mmap-dir");
    }
    if trace_file.is_some() {
        incompatible.push("--trace-file");
    }
    if mmap_trace_locations.is_some() {
        incompatible.push("--mmap-trace-locations");
    }
    if checkpoint.is_some() {
        incompatible.push("--checkpoint");
    }
    if checkpoint_interval != 300 {
        incompatible.push("--checkpoint-interval");
    }
    if resume.is_some() {
        incompatible.push("--resume");
    }
    if !matches!(output, OutputFormat::Human) {
        incompatible.push("--output");
    }
    if tool {
        incompatible.push("--tool");
    }
    if !matches!(trace_format, cli_schema::TraceFormat::Text) {
        incompatible.push("--trace-format");
    }
    if difftrace {
        incompatible.push("--difftrace");
    }
    if continue_on_error {
        incompatible.push("--continue-on-error");
    }
    if allow_incomplete {
        incompatible.push("--allow-incomplete");
    }
    if force {
        incompatible.push("--force");
    }
    if profile_enum {
        incompatible.push("--profile-enum");
    }
    if profile_enum_detail {
        incompatible.push("--profile-enum-detail");
    }
    if profile_eval {
        incompatible.push("--profile-eval");
    }
    if !matches!(liveness_mode, cli_schema::LivenessModeArg::Full) {
        incompatible.push("--liveness-mode");
    }
    incompatible
}

/// Start the interactive JSON-RPC server for step-by-step state exploration.
///
/// Part of #3751: Apalache Gap 3.
fn cmd_server(
    file: &std::path::Path,
    config_path: Option<&std::path::Path>,
    port: u16,
) -> Result<()> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;
    let result = tla_core::lower(tla_core::FileId(0), &tree);
    if !result.errors.is_empty() {
        bail!("TLA+ lowering failed with {} error(s)", result.errors.len());
    }
    let module = result
        .module
        .ok_or_else(|| anyhow::anyhow!("no module produced"))?;

    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };
    let config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf).context("read config file")?;
        tla_check::Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        // Fall back to convention names Init / Next.
        tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    let module = std::sync::Arc::new(module);
    let mut server = tla_check::InteractiveServer::new(module, config);
    server.listen(port).map_err(|e| anyhow::anyhow!("{e}"))
}

// Use a larger stack size (64MB) to handle deeply recursive TLA+ expressions
// The default 2MB stack is insufficient for specs with deeply nested recursive functions
#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<()> {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    // Run the main logic in a thread with larger stack
    let result = std::thread::Builder::new()
        .name("tla2-main".to_string())
        .stack_size(64 * 1024 * 1024) // 64MB stack
        .spawn(|| {
            tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("failed to build tokio runtime")
                .block_on(async_main())
        })
        .expect("Failed to spawn main thread")
        .join()
        .expect("Main thread panicked");
    result
}

async fn async_main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Parse { file } => helpers::cmd_parse(&file),
        Command::Ast { file, tir } => helpers::cmd_ast(&file, tir),
        Command::Fmt {
            files,
            write,
            indent,
            width,
            check,
            diff,
        } => cmd_fmt::cmd_fmt(cmd_fmt::FmtConfig {
            files,
            write,
            indent,
            width,
            check,
            diff,
        }),
        Command::Trace { command } => trace_cmd::cmd_trace(command),
        Command::Petri {
            model,
            examination,
            args,
        } => cmd_petri(model, examination, args),
        Command::PetriSimplify {
            model_dir,
            examination,
        } => cmd_petri_simplify(model_dir, examination),
        Command::Mcc {
            model_dir,
            examination,
            args,
        } => cmd_mcc(model_dir, examination, args),
        Command::Check {
            file,
            config,
            compiled,
            quint,
            random_walks,
            walk_depth,
            simulate,
            workers,
            no_deadlock,
            max_states,
            max_depth,
            memory_limit,
            disk_limit,
            soundness,
            require_exhaustive,
            bmc,
            bmc_incremental,
            #[cfg(feature = "z4")]
            pdr,
            #[cfg(feature = "z4")]
            kinduction,
            #[cfg(feature = "z4")]
            kinduction_max_k,
            #[cfg(feature = "z4")]
            kinduction_incremental,
            bfs_only,
            pipeline,
            strategy,
            #[cfg(feature = "z4")]
            fused,
            portfolio,
            portfolio_strategies,
            por,
            estimate,
            estimate_only,
            coverage,
            coverage_guided,
            coverage_mix_ratio,
            profile_enum,
            profile_enum_detail,
            profile_eval,
            liveness_mode,
            strict_liveness,
            jit,
            jit_verify,
            show_tiers,
            type_specialize,
            no_trace,
            store_states,
            initial_capacity,
            mmap_fingerprints,
            huge_pages,
            disk_fingerprints,
            mmap_dir,
            trace_file,
            mmap_trace_locations,
            collision_check,
            checkpoint,
            checkpoint_interval,
            resume,
            output,
            tool,
            trace_format,
            difftrace,
            explain_trace,
            continue_on_error,
            allow_incomplete,
            force,
            init,
            next,
            invariants,
            properties,
            constants,
            no_config,
            no_preprocess,
            allow_io,
            trace_invariants,
            #[cfg(feature = "z4")]
            inductive_check,
            #[cfg(feature = "z4")]
            symbolic_sim,
            #[cfg(feature = "z4")]
            sim_runs,
            #[cfg(feature = "z4")]
            sim_length,
            incremental,
            distributed,
            nodes,
            node_id,
        } => {
            if simulate {
                let incompatible = incompatible_check_simulate_flags(
                    workers,
                    no_deadlock,
                    max_states,
                    max_depth,
                    memory_limit,
                    disk_limit,
                    soundness,
                    require_exhaustive,
                    bmc,
                    #[cfg(feature = "z4")]
                    pdr,
                    #[cfg(feature = "z4")]
                    kinduction,
                    pipeline,
                    &strategy,
                    por,
                    coverage,
                    no_trace,
                    store_states,
                    initial_capacity,
                    mmap_fingerprints,
                    disk_fingerprints,
                    &mmap_dir,
                    &trace_file,
                    mmap_trace_locations,
                    &checkpoint,
                    checkpoint_interval,
                    &resume,
                    output,
                    tool,
                    trace_format,
                    difftrace,
                    continue_on_error,
                    allow_incomplete,
                    force,
                    profile_enum,
                    profile_enum_detail,
                    profile_eval,
                    liveness_mode,
                );
                if !incompatible.is_empty() {
                    bail!(
                        "`tla2 check --simulate` is a compatibility alias for `tla2 simulate`. \
                         Unsupported check-only flags: {}. Use `tla2 simulate` for simulation \
                         controls such as `--num-traces`, `--max-trace-length`, `--seed`, and \
                         `--no-invariants`.",
                        incompatible.join(", ")
                    );
                }
                return cmd_simulate::cmd_simulate(&file, config.as_deref(), 1000, 100, 0, false);
            }
            #[cfg(feature = "z4")]
            let pdr_enabled = pdr;
            #[cfg(not(feature = "z4"))]
            let pdr_enabled = false;
            #[cfg(feature = "z4")]
            let kinduction_enabled = kinduction;
            #[cfg(not(feature = "z4"))]
            let kinduction_enabled = false;
            #[cfg(feature = "z4")]
            let kinduction_max_k_val = kinduction_max_k;
            #[cfg(not(feature = "z4"))]
            let kinduction_max_k_val: usize = 20;
            #[cfg(feature = "z4")]
            let kinduction_incremental_val = kinduction_incremental;
            #[cfg(not(feature = "z4"))]
            let kinduction_incremental_val = false;
            #[cfg(feature = "z4")]
            let inductive_check_invariant = inductive_check;
            #[cfg(not(feature = "z4"))]
            let inductive_check_invariant: Option<String> = None;
            // Part of #3953: CDEMC/fused is the default when z4 is enabled.
            // Auto-enable unless the user explicitly requested --bfs-only,
            // selected another explicit mode, or uses features that require
            // the full BFS CLI path (checkpoint, trace-file, tlc-tool output).
            #[cfg(feature = "z4")]
            let fused_enabled = if bfs_only {
                false
            } else if fused {
                // Explicit --fused (deprecated but still accepted).
                true
            } else if pdr || kinduction || bmc > 0 || pipeline || strategy.is_some() || portfolio {
                // User requested a specific mode — don't override.
                false
            } else {
                // Fall back to BFS for features the fused path doesn't wire.
                let needs_full_bfs = tool
                    || checkpoint.is_some()
                    || resume.is_some()
                    || trace_file.is_some();
                !needs_full_bfs
            };
            #[cfg(not(feature = "z4"))]
            let fused_enabled = false;
            #[cfg(not(feature = "z4"))]
            let _ = bfs_only;
            #[cfg(feature = "z4")]
            let symbolic_sim_enabled = symbolic_sim;
            #[cfg(not(feature = "z4"))]
            let symbolic_sim_enabled = false;
            #[cfg(feature = "z4")]
            let sim_runs_val = sim_runs;
            #[cfg(not(feature = "z4"))]
            let sim_runs_val: usize = 100;
            #[cfg(feature = "z4")]
            let sim_length_val = sim_length;
            #[cfg(not(feature = "z4"))]
            let sim_length_val: usize = 10;
            let output_format = if tool { OutputFormat::TlcTool } else { output };
            let effective_workers =
                if matches!(output_format, OutputFormat::TlcTool) && workers == 0 {
                    // Tool mode prioritizes Toolbox compatibility (especially error traces).
                    // Today, traces are only reconstructed in sequential mode.
                    1
                } else {
                    workers
                };
            // Part of #3746: Wire --strict-liveness to env var before OnceLock init.
            if strict_liveness {
                std::env::set_var("TLA2_STRICT_LIVENESS", "1");
            }
            // Part of #4035: Wire --jit to env var before OnceLock init.
            // JIT is off by default; --jit enables it at runtime.
            if jit {
                #[cfg(feature = "jit")]
                {
                    std::env::set_var("TLA2_JIT", "1");
                }
                #[cfg(not(feature = "jit"))]
                {
                    eprintln!(
                        "Warning: --jit flag ignored. Binary was compiled without JIT support. \
                         Rebuild with `cargo build --features jit` to enable JIT compilation."
                    );
                }
            }
            if no_preprocess {
                std::env::set_var("TLA2_NO_PREPROCESS", "1");
            }
            // Part of #3965: Wire --allow-io to enable IOExec command execution.
            if allow_io {
                tla_check::eval::set_io_exec_allowed(true);
                eprintln!(
                    "Warning: --allow-io is enabled. IOExec and related operators can execute \
                     arbitrary shell commands. Only use this with trusted specs."
                );
            }
            let tool_cli_started = Instant::now();
            // Auto-detect Quint JSON IR from file extension.
            let quint_mode = quint || tla_core::quint::is_quint_json_path(&file);
            let result = cmd_check(CheckConfig {
                file: file.clone(),
                config_path: config.clone(),
                compiled,
                quint: quint_mode,
                random_walks,
                walk_depth,
                workers: effective_workers,
                no_deadlock,
                max_states,
                max_depth,
                memory_limit,
                disk_limit,
                soundness_gate: soundness,
                require_exhaustive,
                bmc_depth: bmc,
                bmc_incremental,
                pdr_enabled,
                kinduction_enabled,
                kinduction_max_k: kinduction_max_k_val,
                kinduction_incremental: kinduction_incremental_val,
                por_enabled: por,
                // show_progress removed: always-on for Human output (#3247)
                show_coverage: coverage || coverage_guided,
                coverage_guided,
                coverage_mix_ratio,
                estimate: estimate || estimate_only.is_some(),
                estimate_only,
                no_trace,
                store_states,
                initial_capacity,
                mmap_fingerprints,
                huge_pages: huge_pages || std::env::var("TLA2_HUGE_PAGES").is_ok(),
                disk_fingerprints,
                mmap_dir,
                trace_file_path: trace_file,
                mmap_trace_locations,
                checkpoint_dir: checkpoint,
                checkpoint_interval,
                resume_from: resume,
                output_format,
                trace_format,
                difftrace,
                explain_trace,
                continue_on_error,
                allow_incomplete,
                force,
                profile_enum,
                profile_enum_detail,
                profile_eval,
                liveness_mode,
                strict_liveness,
                jit,
                jit_verify,
                show_tiers,
                type_specialize,
                pipeline,
                strategy,
                fused: fused_enabled,
                portfolio,
                portfolio_strategies,
                cli_init: init,
                cli_next: next,
                cli_invariants: invariants,
                cli_properties: properties,
                cli_constants: constants,
                no_config,
                no_preprocess,
                allow_io,
                trace_invariants,
                inductive_check_invariant,
                symbolic_sim: symbolic_sim_enabled,
                symbolic_sim_runs: sim_runs_val,
                symbolic_sim_length: sim_length_val,
                collision_check,
                incremental,
                distributed,
                distributed_nodes: nodes,
                distributed_node_id: node_id,
            });

            if matches!(
                output_format,
                OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Itf
            ) {
                if let Err(e) = result {
                    let completeness = SearchCompleteness::from_bounds(max_states, max_depth);
                    emit_check_cli_error(
                        &JsonErrorCtx {
                            output_format,
                            spec_file: &file,
                            config_file: config.as_deref(),
                            module_name: None,
                            workers: effective_workers,
                            completeness,
                        },
                        error_codes::SYS_SETUP_ERROR,
                        format!("{e:#}"),
                        Some(ErrorSuggestion::new(
                            "Fix the spec/config error, then re-run the command",
                        )),
                        std::iter::empty::<String>(),
                    );
                }
                Ok(())
            } else if matches!(output_format, OutputFormat::TlcTool) {
                if let Err(e) = result {
                    let completeness = SearchCompleteness::from_bounds(max_states, max_depth);
                    tlc_tool::emit_check_tool_cli_error(
                        &file,
                        config.as_deref(),
                        effective_workers,
                        completeness,
                        tool_cli_started.elapsed(),
                        &format!("{e}"),
                    );
                }
                Ok(())
            } else {
                result
            }
        }
        Command::Watch {
            file,
            config,
            workers,
            no_deadlock,
            debounce_ms,
            clear,
        } => cmd_watch::cmd_watch(cmd_watch::WatchConfig {
            file,
            config_path: config,
            on_error_only: false,
            debounce_ms,
            clear,
            workers,
            no_deadlock,
            max_states: 0,
            max_depth: 0,
        }),
        Command::Test {
            file,
            config,
            runs,
            depth,
            seed,
            workers,
            no_deadlock,
        } => cmd_test::cmd_test(cmd_test::TestConfig {
            file,
            config_path: config,
            runs,
            depth,
            seed,
            workers,
            no_deadlock,
        }),
        Command::Simulate {
            file,
            config,
            num_traces,
            max_trace_length,
            seed,
            no_invariants,
        } => cmd_simulate::cmd_simulate(
            &file,
            config.as_deref(),
            num_traces,
            max_trace_length,
            seed,
            no_invariants,
        ),
        Command::Lsp => {
            tla_lsp::run_server().await;
            Ok(())
        }
        Command::Server { file, config, port } => cmd_server(&file, config.as_deref(), port),
        Command::Explore {
            file,
            config,
            port,
            mode,
            engine,
            max_symbolic_depth,
            no_invariants,
        } => {
            let explore_mode = match mode {
                cli_schema::ExploreModeArg::Repl => cmd_explore::ExploreMode::Repl,
                cli_schema::ExploreModeArg::Http => cmd_explore::ExploreMode::Http,
            };
            let explore_engine = match engine {
                cli_schema::ExploreEngineArg::Concrete => tla_check::ServerExploreMode::Concrete,
                cli_schema::ExploreEngineArg::Symbolic => tla_check::ServerExploreMode::Symbolic,
            };
            cmd_explore::cmd_explore(
                &file,
                config.as_deref(),
                port,
                explore_mode,
                explore_engine,
                max_symbolic_depth,
                no_invariants,
            )
        }
        #[cfg(feature = "prove")]
        Command::Prove {
            file,
            timeout,
            theorem,
        } => cmd_prove::cmd_prove(&file, timeout, theorem.as_deref()),
        Command::Lint {
            file,
            config,
            format,
            severity,
        } => {
            let min_severity = match severity {
                cli_schema::LintSeverityArg::Warning => cmd_lint::LintSeverity::Warning,
                cli_schema::LintSeverityArg::Info => cmd_lint::LintSeverity::Info,
            };
            cmd_lint::cmd_lint(&file, config.as_deref(), format, min_severity)
        }
        Command::Search {
            pattern,
            paths,
            kind,
            format,
        } => {
            let search_kind = match kind {
                cli_schema::SearchKind::Operator => cmd_search::SearchKind::Operator,
                cli_schema::SearchKind::Variable => cmd_search::SearchKind::Variable,
                cli_schema::SearchKind::Constant => cmd_search::SearchKind::Constant,
                cli_schema::SearchKind::Expr => cmd_search::SearchKind::Pattern,
                cli_schema::SearchKind::Action => cmd_search::SearchKind::All,
            };
            let search_format = match format {
                cli_schema::SearchOutputFormat::Human => cmd_search::SearchOutputFormat::Human,
                cli_schema::SearchOutputFormat::Json => cmd_search::SearchOutputFormat::Json,
            };
            cmd_search::cmd_search(&pattern, &paths, search_kind, search_format)
        }
        Command::Doc {
            file,
            config,
            format,
            output,
        } => cmd_doc::cmd_doc(&file, config.as_deref(), format, output.as_deref()),
        Command::Typecheck {
            file,
            output,
            infer_types,
        } => cmd_typecheck::cmd_typecheck(&file, output, infer_types),
        Command::Deps {
            file,
            config,
            format,
            unused,
            modules_only,
        } => cmd_deps::cmd_deps(&file, config.as_deref(), format, unused, modules_only),
        Command::Diagnose(args) => cmd_diagnose::cmd_diagnose(args),
        Command::Bench {
            files,
            config,
            iterations,
            workers,
            baseline,
            save_baseline,
            format,
        } => cmd_bench::cmd_bench(cmd_bench::BenchConfig {
            files,
            config,
            iterations,
            workers,
            baseline,
            save_baseline,
            format,
        }),
        Command::Summary {
            files,
            config,
            workers,
            format,
            sort,
            status,
        } => {
            let sum_format = match format {
                cli_schema::SummaryOutputFormat::Human => cmd_summary::SummaryOutputFormat::Human,
                cli_schema::SummaryOutputFormat::Json => cmd_summary::SummaryOutputFormat::Json,
                cli_schema::SummaryOutputFormat::Csv => cmd_summary::SummaryOutputFormat::Csv,
            };
            let sum_sort = match sort {
                cli_schema::SummarySortBy::Name => cmd_summary::SummarySortField::Name,
                cli_schema::SummarySortBy::Time => cmd_summary::SummarySortField::Time,
                cli_schema::SummarySortBy::States => cmd_summary::SummarySortField::States,
                cli_schema::SummarySortBy::Status => cmd_summary::SummarySortField::Status,
            };
            cmd_summary::cmd_summary(
                &files,
                config.as_deref(),
                workers,
                sum_format,
                sum_sort,
                status.as_deref(),
            )
        }
        Command::Minimize {
            file,
            config,
            max_oracle_calls,
            no_fine,
            output,
        } => cmd_minimize::cmd_minimize(
            &file,
            config.as_deref(),
            max_oracle_calls,
            no_fine,
            output.as_deref(),
        ),
        Command::Codegen {
            file,
            config,
            output,
            tir,
            checker,
            checker_map,
            kani,
            proptest,
            scaffold,
            source_map,
        } => {
            if scaffold {
                cmd_codegen::cmd_codegen_scaffold(
                    &file,
                    config.as_deref(),
                    output.as_deref(),
                    kani,
                    tir,
                )
            } else if tir {
                cmd_codegen::cmd_codegen_tir(&file, config.as_deref(), output.as_deref())
            } else {
                cmd_codegen::cmd_codegen(
                    &file,
                    output.as_deref(),
                    checker,
                    checker_map.as_deref(),
                    kani,
                    proptest,
                    source_map,
                )
            }
        }
        Command::Explain {
            trace_file,
            spec,
            config,
            invariant,
            diff,
            verbose,
            format,
        } => {
            let explain_format = match format {
                cli_schema::ExplainOutputFormat::Human => cmd_explain::ExplainFormat::Human,
                cli_schema::ExplainOutputFormat::Json => cmd_explain::ExplainFormat::Json,
            };
            cmd_explain::cmd_explain(cmd_explain::ExplainConfig {
                trace_file,
                spec_file: spec,
                config_file: config,
                invariant,
                diff_mode: diff,
                verbose,
                format: explain_format,
            })
        }
        Command::Coverage {
            trace_file,
            spec,
            config,
            format,
        } => cmd_coverage::cmd_coverage(
            &trace_file,
            spec.as_deref(),
            config.as_deref(),
            format,
        ),
        Command::Graph {
            trace_file,
            format,
            max_states,
            highlight_error,
            cluster_by_action,
        } => {
            let graph_format = match format {
                cli_schema::GraphOutputFormat::Dot => cmd_graph::GraphOutputFormat::Dot,
                cli_schema::GraphOutputFormat::Mermaid => cmd_graph::GraphOutputFormat::Mermaid,
                cli_schema::GraphOutputFormat::Json => cmd_graph::GraphOutputFormat::Json,
            };
            cmd_graph::cmd_graph(&trace_file, graph_format, max_states, highlight_error, cluster_by_action)
        }
        Command::Vmt { file, config } => cmd_vmt::cmd_vmt(&file, config.as_deref()),
        #[cfg(feature = "z4")]
        Command::Btor2 {
            file,
            verbose,
            witness,
            timeout,
        } => cmd_btor2::cmd_btor2(&file, verbose, witness.as_deref(), timeout),
        #[cfg(feature = "z4")]
        Command::Aiger {
            file,
            verbose,
            witness,
            timeout,
            engine,
            portfolio,
        } => cmd_aiger::cmd_aiger(&file, verbose, witness.as_deref(), timeout, engine, portfolio),
        Command::Repair {
            trace_file,
            spec,
            config,
            invariant,
            max_suggestions,
            format,
        } => {
            let repair_format = match format {
                cli_schema::RepairOutputFormat::Human => cmd_repair::RepairFormat::Human,
                cli_schema::RepairOutputFormat::Json => cmd_repair::RepairFormat::Json,
            };
            cmd_repair::cmd_repair(cmd_repair::RepairConfig {
                trace_file,
                spec_file: spec,
                config_file: config,
                invariant,
                max_suggestions,
                format: repair_format,
            })
        }
        Command::Profile {
            file,
            config,
            workers,
            format,
            top,
            memory,
        } => cmd_profile::cmd_profile(cmd_profile::ProfileConfig {
            file,
            config,
            workers,
            format,
            top,
            memory,
        }),
        Command::Diff {
            old,
            new,
            old_config,
            new_config,
            format,
            operators_only,
        } => cmd_diff::cmd_diff(
            &old,
            &new,
            old_config.as_deref(),
            new_config.as_deref(),
            format,
            operators_only,
        ),
        Command::Convert {
            input,
            from,
            to,
            output,
        } => {
            let from = from.unwrap_or_else(|| {
                match input.extension().and_then(|e| e.to_str()) {
                    Some("tla") => cli_schema::ConvertFrom::Tla,
                    Some("json") => {
                        // Heuristic: if filename contains "trace" or "output", treat as Trace
                        let stem = input.file_stem().and_then(|s| s.to_str()).unwrap_or("");
                        if stem.contains("trace") || stem.contains("output") {
                            cli_schema::ConvertFrom::Trace
                        } else {
                            cli_schema::ConvertFrom::Json
                        }
                    }
                    _ => cli_schema::ConvertFrom::Tla,
                }
            });
            cmd_convert::cmd_convert(cmd_convert::ConvertConfig {
                input,
                from,
                to,
                output,
            })
        }
        Command::Stats {
            file,
            config,
            format,
        } => cmd_stats::cmd_stats(&file, config.as_deref(), format),
        Command::Init {
            name,
            template,
            dir,
            force,
        } => cmd_init::cmd_init(&name, template, &dir, force),
        Command::Completions { shell } => cmd_completions::cmd_completions(shell),
        Command::Refactor { action } => cmd_refactor::cmd_refactor(action),
        Command::Snapshot {
            files,
            config,
            snapshot_dir,
            update,
            format,
        } => cmd_snapshot::cmd_snapshot(
            &files,
            config.as_deref(),
            &snapshot_dir,
            update,
            format,
        ),
        Command::Bisect {
            file,
            config,
            constant,
            low,
            high,
            state_count,
            timeout,
            format,
        } => {
            let mode = match state_count {
                Some(threshold) => cmd_bisect::BisectMode::StateCount { threshold },
                None => cmd_bisect::BisectMode::Violation,
            };
            cmd_bisect::cmd_bisect(&file, &config, &constant, low, high, mode, format, timeout)
        }
        Command::Merge {
            base,
            patch,
            output,
            force,
            format,
        } => cmd_merge::cmd_merge(&base, &patch, output.as_deref(), force, format),
        Command::Validate {
            file,
            config,
            format,
            strict,
        } => cmd_validate::cmd_validate(&file, config.as_deref(), format, strict),
        Command::Template {
            kind,
            name,
            processes,
            output_dir,
            stdout,
        } => {
            let tmpl_kind = match kind {
                cli_schema::TemplateKind::Mutex => cmd_template::TemplateKind::Mutex,
                cli_schema::TemplateKind::Consensus => cmd_template::TemplateKind::Consensus,
                cli_schema::TemplateKind::Cache => cmd_template::TemplateKind::Cache,
                cli_schema::TemplateKind::Queue => cmd_template::TemplateKind::Queue,
                cli_schema::TemplateKind::Leader => cmd_template::TemplateKind::Leader,
                cli_schema::TemplateKind::TokenRing => cmd_template::TemplateKind::TokenRing,
            };
            cmd_template::cmd_template(tmpl_kind, &name, processes, &output_dir, stdout)
        }
        Command::Deadlock {
            file,
            config,
            mode,
            format,
        } => {
            let dl_mode = match mode {
                cli_schema::DeadlockMode::Quick => cmd_deadlock::DeadlockMode::Quick,
                cli_schema::DeadlockMode::Full => cmd_deadlock::DeadlockMode::Full,
            };
            let dl_format = match format {
                cli_schema::DeadlockOutputFormat::Human => cmd_deadlock::DeadlockOutputFormat::Human,
                cli_schema::DeadlockOutputFormat::Json => cmd_deadlock::DeadlockOutputFormat::Json,
            };
            cmd_deadlock::cmd_deadlock(&file, config.as_deref(), dl_mode, dl_format)
        }
        Command::Abstract {
            file,
            config,
            format,
            detail,
        } => {
            let abs_format = match format {
                cli_schema::AbstractOutputFormat::Human => cmd_abstract::AbstractOutputFormat::Human,
                cli_schema::AbstractOutputFormat::Json => cmd_abstract::AbstractOutputFormat::Json,
                cli_schema::AbstractOutputFormat::Mermaid => cmd_abstract::AbstractOutputFormat::Mermaid,
            };
            let abs_detail = match detail {
                cli_schema::AbstractDetail::Brief => cmd_abstract::AbstractDetail::Brief,
                cli_schema::AbstractDetail::Normal => cmd_abstract::AbstractDetail::Normal,
                cli_schema::AbstractDetail::Full => cmd_abstract::AbstractDetail::Full,
            };
            cmd_abstract::cmd_abstract(&file, config.as_deref(), abs_format, abs_detail)
        }
        Command::Import {
            file,
            from,
            output,
        } => {
            let import_format = match from {
                cli_schema::ImportFormat::JsonStateMachine => cmd_import::ImportFormat::JsonStateMachine,
                cli_schema::ImportFormat::Promela => cmd_import::ImportFormat::Promela,
                cli_schema::ImportFormat::Alloy => cmd_import::ImportFormat::Alloy,
            };
            cmd_import::cmd_import(&file, import_format, output.as_deref())
        }
        Command::Witness {
            file,
            config,
            target,
            max_depth,
            count,
            format,
        } => {
            let w_format = match format {
                cli_schema::WitnessOutputFormat::Human => cmd_witness::WitnessOutputFormat::Human,
                cli_schema::WitnessOutputFormat::Json => cmd_witness::WitnessOutputFormat::Json,
            };
            cmd_witness::cmd_witness(&file, config.as_deref(), &target, max_depth, count, w_format)
        }
        Command::Compare {
            left,
            right,
            format,
        } => {
            let c_format = match format {
                cli_schema::CompareOutputFormat::Human => cmd_compare::CompareOutputFormat::Human,
                cli_schema::CompareOutputFormat::Json => cmd_compare::CompareOutputFormat::Json,
            };
            cmd_compare::cmd_compare(&left, &right, c_format)
        }
        Command::Inline {
            file,
            output,
            keep_comments,
        } => cmd_inline::cmd_inline(&file, output.as_deref(), keep_comments),
        Command::Scope { file, format } => {
            let scope_format = match format {
                cli_schema::ScopeOutputFormat::Human => cmd_scope::ScopeOutputFormat::Human,
                cli_schema::ScopeOutputFormat::Json => cmd_scope::ScopeOutputFormat::Json,
                cli_schema::ScopeOutputFormat::Dot => cmd_scope::ScopeOutputFormat::Dot,
            };
            cmd_scope::cmd_scope(&file, scope_format)
        }
        Command::Constrain {
            file,
            config,
            strategy,
            output,
        } => {
            let c_strategy = match strategy {
                cli_schema::ConstrainStrategy::Minimize => cmd_constrain::ConstrainStrategy::Minimize,
                cli_schema::ConstrainStrategy::Incremental => cmd_constrain::ConstrainStrategy::Incremental,
                cli_schema::ConstrainStrategy::Symmetric => cmd_constrain::ConstrainStrategy::Symmetric,
            };
            cmd_constrain::cmd_constrain(&file, &config, c_strategy, output.as_deref())
        }
        Command::Audit { dir, format } => {
            let audit_format = match format {
                cli_schema::AuditOutputFormat::Human => cmd_audit::AuditOutputFormat::Human,
                cli_schema::AuditOutputFormat::Json => cmd_audit::AuditOutputFormat::Json,
            };
            cmd_audit::cmd_audit(&dir, audit_format)
        }
        Command::Symmetry { file, config, format } => {
            let sym_format = match format {
                cli_schema::SymmetryOutputFormat::Human => cmd_symmetry::SymmetryOutputFormat::Human,
                cli_schema::SymmetryOutputFormat::Json => cmd_symmetry::SymmetryOutputFormat::Json,
            };
            cmd_symmetry::cmd_symmetry(&file, config.as_deref(), sym_format)
        }
        Command::Partition {
            file,
            config,
            partitions,
            format,
        } => {
            let part_format = match format {
                cli_schema::PartitionOutputFormat::Human => cmd_partition::PartitionOutputFormat::Human,
                cli_schema::PartitionOutputFormat::Json => cmd_partition::PartitionOutputFormat::Json,
            };
            cmd_partition::cmd_partition(&file, config.as_deref(), partitions, part_format)
        }
        Command::SimReport {
            file,
            config,
            num_traces,
            max_depth,
            format,
        } => {
            let sr_format = match format {
                cli_schema::SimReportOutputFormat::Human => cmd_simreport::SimReportOutputFormat::Human,
                cli_schema::SimReportOutputFormat::Json => cmd_simreport::SimReportOutputFormat::Json,
            };
            cmd_simreport::cmd_sim_report(&file, config.as_deref(), num_traces, max_depth, sr_format)
        }
        Command::TraceGen {
            file,
            config,
            mode,
            target,
            count,
            max_depth,
            format,
        } => {
            let tg_mode = match mode {
                cli_schema::TraceGenMode::Target => cmd_tracegen::TraceGenMode::Target,
                cli_schema::TraceGenMode::Coverage => cmd_tracegen::TraceGenMode::Coverage,
                cli_schema::TraceGenMode::Random => cmd_tracegen::TraceGenMode::Random,
            };
            let tg_format = match format {
                cli_schema::TraceGenOutputFormat::Human => cmd_tracegen::TraceGenOutputFormat::Human,
                cli_schema::TraceGenOutputFormat::Json => cmd_tracegen::TraceGenOutputFormat::Json,
                cli_schema::TraceGenOutputFormat::Itf => cmd_tracegen::TraceGenOutputFormat::Itf,
            };
            cmd_tracegen::cmd_trace_gen(&file, config.as_deref(), tg_mode, target.as_deref(), count, max_depth, tg_format)
        }
        Command::InvGen {
            file,
            config,
            verify,
            format,
        } => {
            let ig_format = match format {
                cli_schema::InvGenOutputFormat::Human => cmd_invgen::InvGenOutputFormat::Human,
                cli_schema::InvGenOutputFormat::Json => cmd_invgen::InvGenOutputFormat::Json,
                cli_schema::InvGenOutputFormat::Tla => cmd_invgen::InvGenOutputFormat::Tla,
            };
            cmd_invgen::cmd_inv_gen(&file, config.as_deref(), verify, ig_format)
        }
        Command::ActionGraph {
            file,
            config,
            format,
        } => {
            let ag_format = match format {
                cli_schema::ActionGraphOutputFormat::Human => cmd_actiongraph::ActionGraphOutputFormat::Human,
                cli_schema::ActionGraphOutputFormat::Json => cmd_actiongraph::ActionGraphOutputFormat::Json,
                cli_schema::ActionGraphOutputFormat::Dot => cmd_actiongraph::ActionGraphOutputFormat::Dot,
            };
            cmd_actiongraph::cmd_action_graph(&file, config.as_deref(), ag_format)
        }
        Command::Refine {
            impl_file,
            abstract_file,
            config,
            mapping,
            max_states,
            format,
        } => {
            let rf_format = match format {
                cli_schema::RefineOutputFormat::Human => cmd_refine::RefineOutputFormat::Human,
                cli_schema::RefineOutputFormat::Json => cmd_refine::RefineOutputFormat::Json,
            };
            cmd_refine::cmd_refine(&impl_file, &abstract_file, config.as_deref(), mapping.as_deref(), max_states, rf_format)
        }
        Command::ModelDiff {
            old_file,
            new_file,
            format,
        } => {
            let md_format = match format {
                cli_schema::ModelDiffOutputFormat::Human => cmd_modeldiff::ModelDiffOutputFormat::Human,
                cli_schema::ModelDiffOutputFormat::Json => cmd_modeldiff::ModelDiffOutputFormat::Json,
            };
            cmd_modeldiff::cmd_model_diff(&old_file, &new_file, md_format)
        }
        Command::StateFilter {
            file,
            config,
            filter,
            max_states,
            max_results,
            format,
        } => {
            let sf_format = match format {
                cli_schema::StateFilterOutputFormat::Human => cmd_statefilter::StateFilterOutputFormat::Human,
                cli_schema::StateFilterOutputFormat::Json => cmd_statefilter::StateFilterOutputFormat::Json,
            };
            cmd_statefilter::cmd_state_filter(&file, config.as_deref(), &filter, max_states, max_results, sf_format)
        }
        Command::Lasso {
            file,
            config,
            property,
            max_states,
            format,
        } => {
            let l_format = match format {
                cli_schema::LassoOutputFormat::Human => cmd_lasso::LassoOutputFormat::Human,
                cli_schema::LassoOutputFormat::Json => cmd_lasso::LassoOutputFormat::Json,
            };
            cmd_lasso::cmd_lasso(&file, config.as_deref(), property.as_deref(), max_states, l_format)
        }
        Command::AssumeGuarantee {
            file,
            config,
            max_states,
            format,
        } => {
            let ag_format = match format {
                cli_schema::AssumeGuaranteeOutputFormat::Human => cmd_assumeguarantee::AssumeGuaranteeOutputFormat::Human,
                cli_schema::AssumeGuaranteeOutputFormat::Json => cmd_assumeguarantee::AssumeGuaranteeOutputFormat::Json,
            };
            cmd_assumeguarantee::cmd_assume_guarantee(&file, config.as_deref(), max_states, ag_format)
        }
        Command::PredicateAbs {
            file,
            config,
            predicate,
            max_states,
            format,
        } => {
            let pa_format = match format {
                cli_schema::PredicateAbsOutputFormat::Human => cmd_predicateabs::PredicateAbsOutputFormat::Human,
                cli_schema::PredicateAbsOutputFormat::Json => cmd_predicateabs::PredicateAbsOutputFormat::Json,
            };
            let preds = if predicate.is_empty() { None } else { Some(predicate.as_slice()) };
            cmd_predicateabs::cmd_predicate_abs(&file, config.as_deref(), preds, max_states, pa_format)
        }
        Command::Census {
            file,
            config,
            max_states,
            format,
        } => {
            let c_format = match format {
                cli_schema::CensusOutputFormat::Human => cmd_census::CensusOutputFormat::Human,
                cli_schema::CensusOutputFormat::Json => cmd_census::CensusOutputFormat::Json,
            };
            cmd_census::cmd_census(&file, config.as_deref(), max_states, c_format)
        }
        Command::Equiv {
            file_a,
            file_b,
            config_a,
            config_b,
            max_states,
            format,
        } => {
            let e_format = match format {
                cli_schema::EquivOutputFormat::Human => cmd_equiv::EquivOutputFormat::Human,
                cli_schema::EquivOutputFormat::Json => cmd_equiv::EquivOutputFormat::Json,
            };
            cmd_equiv::cmd_equiv(&file_a, &file_b, config_a.as_deref(), config_b.as_deref(), max_states, e_format)
        }
        Command::Induct {
            file,
            config,
            invariant,
            max_states,
            format,
        } => {
            let i_format = match format {
                cli_schema::InductOutputFormat::Human => cmd_induct::InductOutputFormat::Human,
                cli_schema::InductOutputFormat::Json => cmd_induct::InductOutputFormat::Json,
            };
            cmd_induct::cmd_induct(&file, config.as_deref(), &invariant, max_states, i_format)
        }
        Command::Slice {
            file,
            target,
            format,
        } => {
            let s_format = match format {
                cli_schema::SliceOutputFormat::Human => cmd_slice::SliceOutputFormat::Human,
                cli_schema::SliceOutputFormat::Json => cmd_slice::SliceOutputFormat::Json,
            };
            cmd_slice::cmd_slice(&file, &target, s_format)
        }
        Command::Reach {
            file,
            config,
            target,
            max_states,
            format,
        } => {
            let r_format = match format {
                cli_schema::ReachOutputFormat::Human => cmd_reach::ReachOutputFormat::Human,
                cli_schema::ReachOutputFormat::Json => cmd_reach::ReachOutputFormat::Json,
            };
            cmd_reach::cmd_reach(&file, config.as_deref(), &target, max_states, r_format)
        }
        Command::Compose {
            file_a,
            file_b,
            format,
        } => {
            let c_format = match format {
                cli_schema::ComposeOutputFormat::Human => cmd_compose::ComposeOutputFormat::Human,
                cli_schema::ComposeOutputFormat::Json => cmd_compose::ComposeOutputFormat::Json,
            };
            cmd_compose::cmd_compose(&file_a, &file_b, c_format)
        }
        Command::Unfold {
            file,
            target,
            max_depth,
            format,
        } => {
            let u_format = match format {
                cli_schema::UnfoldOutputFormat::Human => cmd_unfold::UnfoldOutputFormat::Human,
                cli_schema::UnfoldOutputFormat::Json => cmd_unfold::UnfoldOutputFormat::Json,
            };
            cmd_unfold::cmd_unfold(&file, &target, max_depth, u_format)
        }
        Command::Project {
            file,
            config,
            variable,
            max_states,
            format,
        } => {
            let p_format = match format {
                cli_schema::ProjectOutputFormat::Human => cmd_project::ProjectOutputFormat::Human,
                cli_schema::ProjectOutputFormat::Json => cmd_project::ProjectOutputFormat::Json,
            };
            cmd_project::cmd_project(&file, config.as_deref(), &variable, max_states, p_format)
        }
        Command::Bound {
            file,
            config,
            format,
        } => {
            let b_format = match format {
                cli_schema::BoundOutputFormat::Human => cmd_bound::BoundOutputFormat::Human,
                cli_schema::BoundOutputFormat::Json => cmd_bound::BoundOutputFormat::Json,
            };
            cmd_bound::cmd_bound(&file, config.as_deref(), b_format)
        }
        Command::Sandbox {
            file,
            config,
            max_states,
            max_depth,
            timeout,
            format,
        } => {
            let s_format = match format {
                cli_schema::SandboxOutputFormat::Human => cmd_sandbox::SandboxOutputFormat::Human,
                cli_schema::SandboxOutputFormat::Json => cmd_sandbox::SandboxOutputFormat::Json,
            };
            cmd_sandbox::cmd_sandbox(&file, config.as_deref(), max_states, max_depth, timeout, s_format)
        }
        Command::Timeline {
            file,
            config,
            format,
        } => {
            let t_format = match format {
                cli_schema::TimelineOutputFormat::Human => cmd_timeline::TimelineOutputFormat::Human,
                cli_schema::TimelineOutputFormat::Json => cmd_timeline::TimelineOutputFormat::Json,
            };
            cmd_timeline::cmd_timeline(&file, config.as_deref(), t_format)
        }
        Command::Metric {
            file,
            format,
        } => {
            let m_format = match format {
                cli_schema::MetricOutputFormat::Human => cmd_metric::MetricOutputFormat::Human,
                cli_schema::MetricOutputFormat::Json => cmd_metric::MetricOutputFormat::Json,
            };
            cmd_metric::cmd_metric(&file, m_format)
        }
        Command::Scaffold {
            file,
            format,
        } => {
            let s_format = match format {
                cli_schema::ScaffoldOutputFormat::Human => cmd_scaffold::ScaffoldOutputFormat::Human,
                cli_schema::ScaffoldOutputFormat::Json => cmd_scaffold::ScaffoldOutputFormat::Json,
            };
            cmd_scaffold::cmd_scaffold(&file, s_format)
        }
        Command::Stutter {
            file,
            config,
            format,
        } => {
            let s_format = match format {
                cli_schema::StutterOutputFormat::Human => cmd_stutter::StutterOutputFormat::Human,
                cli_schema::StutterOutputFormat::Json => cmd_stutter::StutterOutputFormat::Json,
            };
            cmd_stutter::cmd_stutter(&file, config.as_deref(), s_format)
        }
        Command::Quorum {
            file,
            format,
        } => {
            let q_format = match format {
                cli_schema::QuorumOutputFormat::Human => cmd_quorum::QuorumOutputFormat::Human,
                cli_schema::QuorumOutputFormat::Json => cmd_quorum::QuorumOutputFormat::Json,
            };
            cmd_quorum::cmd_quorum(&file, q_format)
        }
        Command::Fingerprint {
            file,
            config,
            max_states,
            format,
        } => {
            let f_format = match format {
                cli_schema::FingerprintOutputFormat::Human => cmd_fingerprint::FingerprintOutputFormat::Human,
                cli_schema::FingerprintOutputFormat::Json => cmd_fingerprint::FingerprintOutputFormat::Json,
            };
            cmd_fingerprint::cmd_fingerprint(&file, config.as_deref(), max_states, f_format)
        }
        Command::Normalize {
            file,
            format,
        } => {
            let n_format = match format {
                cli_schema::NormalizeOutputFormat::Human => cmd_normalize::NormalizeOutputFormat::Human,
                cli_schema::NormalizeOutputFormat::Json => cmd_normalize::NormalizeOutputFormat::Json,
            };
            cmd_normalize::cmd_normalize(&file, n_format)
        }
        Command::Countex {
            file,
            config,
            max_states,
            format,
        } => {
            let c_format = match format {
                cli_schema::CountexOutputFormat::Human => cmd_countex::CountexOutputFormat::Human,
                cli_schema::CountexOutputFormat::Json => cmd_countex::CountexOutputFormat::Json,
            };
            cmd_countex::cmd_countex(&file, config.as_deref(), max_states, c_format)
        }
        Command::Heatmap {
            file,
            config,
            max_states,
            format,
        } => {
            let h_format = match format {
                cli_schema::HeatmapOutputFormat::Human => cmd_heatmap::HeatmapOutputFormat::Human,
                cli_schema::HeatmapOutputFormat::Json => cmd_heatmap::HeatmapOutputFormat::Json,
            };
            cmd_heatmap::cmd_heatmap(&file, config.as_deref(), max_states, h_format)
        }
        Command::Protocol {
            file,
            format,
        } => {
            let p_format = match format {
                cli_schema::ProtocolOutputFormat::Human => cmd_protocol::ProtocolOutputFormat::Human,
                cli_schema::ProtocolOutputFormat::Json => cmd_protocol::ProtocolOutputFormat::Json,
            };
            cmd_protocol::cmd_protocol(&file, p_format)
        }
        Command::Hierarchy {
            file,
            format,
        } => {
            let h_format = match format {
                cli_schema::HierarchyOutputFormat::Human => cmd_hierarchy::HierarchyOutputFormat::Human,
                cli_schema::HierarchyOutputFormat::Json => cmd_hierarchy::HierarchyOutputFormat::Json,
            };
            cmd_hierarchy::cmd_hierarchy(&file, h_format)
        }
        Command::Crossref {
            file,
            format,
        } => {
            let c_format = match format {
                cli_schema::CrossrefOutputFormat::Human => cmd_crossref::CrossrefOutputFormat::Human,
                cli_schema::CrossrefOutputFormat::Json => cmd_crossref::CrossrefOutputFormat::Json,
            };
            cmd_crossref::cmd_crossref(&file, c_format)
        }
        Command::Invariantgen {
            file,
            format,
        } => {
            let i_format = match format {
                cli_schema::InvariantgenOutputFormat::Human => cmd_invariantgen::InvariantgenOutputFormat::Human,
                cli_schema::InvariantgenOutputFormat::Json => cmd_invariantgen::InvariantgenOutputFormat::Json,
            };
            cmd_invariantgen::cmd_invariantgen(&file, i_format)
        }
        Command::Drift {
            file_a,
            file_b,
            format,
        } => {
            let d_format = match format {
                cli_schema::DriftOutputFormat::Human => cmd_drift::DriftOutputFormat::Human,
                cli_schema::DriftOutputFormat::Json => cmd_drift::DriftOutputFormat::Json,
            };
            cmd_drift::cmd_drift(&file_a, &file_b, d_format)
        }
        Command::Safety {
            file,
            config,
            format,
        } => {
            let s_format = match format {
                cli_schema::SafetyOutputFormat::Human => cmd_safety::SafetyOutputFormat::Human,
                cli_schema::SafetyOutputFormat::Json => cmd_safety::SafetyOutputFormat::Json,
            };
            cmd_safety::cmd_safety(&file, config.as_deref(), s_format)
        }
        Command::LivenessCheck {
            file,
            config,
            format,
        } => {
            let l_format = match format {
                cli_schema::LivenesscheckOutputFormat::Human => cmd_livenesscheck::LivenesscheckOutputFormat::Human,
                cli_schema::LivenesscheckOutputFormat::Json => cmd_livenesscheck::LivenesscheckOutputFormat::Json,
            };
            cmd_livenesscheck::cmd_livenesscheck(&file, config.as_deref(), l_format)
        }
        Command::Translate {
            file,
            format,
        } => {
            let t_format = match format {
                cli_schema::TranslateOutputFormat::Human => cmd_translate::TranslateOutputFormat::Human,
                cli_schema::TranslateOutputFormat::Json => cmd_translate::TranslateOutputFormat::Json,
            };
            cmd_translate::cmd_translate(&file, t_format)
        }
        Command::Tableau {
            file,
            config,
            format,
        } => {
            let t_format = match format {
                cli_schema::TableauOutputFormat::Human => cmd_tableau::TableauOutputFormat::Human,
                cli_schema::TableauOutputFormat::Json => cmd_tableau::TableauOutputFormat::Json,
            };
            cmd_tableau::cmd_tableau(&file, config.as_deref(), t_format)
        }
        Command::Alphabet {
            file,
            config,
            format,
        } => {
            let a_format = match format {
                cli_schema::AlphabetOutputFormat::Human => cmd_alphabet::AlphabetOutputFormat::Human,
                cli_schema::AlphabetOutputFormat::Json => cmd_alphabet::AlphabetOutputFormat::Json,
            };
            cmd_alphabet::cmd_alphabet(&file, config.as_deref(), a_format)
        }
        Command::Weight {
            file,
            config,
            format,
        } => {
            let w_format = match format {
                cli_schema::WeightOutputFormat::Human => cmd_weight::WeightOutputFormat::Human,
                cli_schema::WeightOutputFormat::Json => cmd_weight::WeightOutputFormat::Json,
            };
            cmd_weight::cmd_weight(&file, config.as_deref(), w_format)
        }
        Command::Absorb {
            file,
            config,
            format,
        } => {
            let a_format = match format {
                cli_schema::AbsorbOutputFormat::Human => cmd_absorb::AbsorbOutputFormat::Human,
                cli_schema::AbsorbOutputFormat::Json => cmd_absorb::AbsorbOutputFormat::Json,
            };
            cmd_absorb::cmd_absorb(&file, config.as_deref(), a_format)
        }
        Command::Cluster {
            file,
            format,
        } => {
            let c_format = match format {
                cli_schema::ClusterOutputFormat::Human => cmd_cluster::ClusterOutputFormat::Human,
                cli_schema::ClusterOutputFormat::Json => cmd_cluster::ClusterOutputFormat::Json,
            };
            cmd_cluster::cmd_cluster(&file, c_format)
        }
        Command::Rename {
            file,
            from,
            to,
            format,
        } => {
            let r_format = match format {
                cli_schema::RenameOutputFormat::Human => cmd_rename::RenameOutputFormat::Human,
                cli_schema::RenameOutputFormat::Json => cmd_rename::RenameOutputFormat::Json,
            };
            cmd_rename::cmd_rename(&file, &from, &to, r_format)
        }
        Command::Reachset {
            file,
            config,
            max_states,
            format,
        } => {
            let r_format = match format {
                cli_schema::ReachsetOutputFormat::Human => cmd_reachset::ReachsetOutputFormat::Human,
                cli_schema::ReachsetOutputFormat::Json => cmd_reachset::ReachsetOutputFormat::Json,
            };
            cmd_reachset::cmd_reachset(&file, config.as_deref(), max_states, r_format)
        }
        Command::Guard {
            file,
            config,
            format,
        } => {
            let g_format = match format {
                cli_schema::GuardOutputFormat::Human => cmd_guard::GuardOutputFormat::Human,
                cli_schema::GuardOutputFormat::Json => cmd_guard::GuardOutputFormat::Json,
            };
            cmd_guard::cmd_guard(&file, config.as_deref(), g_format)
        }
        Command::SymmetryDetect {
            file,
            config,
            format,
        } => {
            let s_format = match format {
                cli_schema::SymmetrydetectOutputFormat::Human => cmd_symmetrydetect::SymmetrydetectOutputFormat::Human,
                cli_schema::SymmetrydetectOutputFormat::Json => cmd_symmetrydetect::SymmetrydetectOutputFormat::Json,
            };
            cmd_symmetrydetect::cmd_symmetrydetect(&file, config.as_deref(), s_format)
        }
        Command::DeadlockFree {
            file,
            config,
            max_states,
            format,
        } => {
            let d_format = match format {
                cli_schema::DeadlockfreeOutputFormat::Human => cmd_deadlockfree::DeadlockfreeOutputFormat::Human,
                cli_schema::DeadlockfreeOutputFormat::Json => cmd_deadlockfree::DeadlockfreeOutputFormat::Json,
            };
            cmd_deadlockfree::cmd_deadlockfree(&file, config.as_deref(), max_states, d_format)
        }
        Command::ActionCount {
            file,
            config,
            format,
        } => {
            let a_format = match format {
                cli_schema::ActioncountOutputFormat::Human => cmd_actioncount::ActioncountOutputFormat::Human,
                cli_schema::ActioncountOutputFormat::Json => cmd_actioncount::ActioncountOutputFormat::Json,
            };
            cmd_actioncount::cmd_actioncount(&file, config.as_deref(), a_format)
        }
        Command::ConstCheck {
            file,
            config,
            format,
        } => {
            let c_format = match format {
                cli_schema::ConstcheckOutputFormat::Human => cmd_constcheck::ConstcheckOutputFormat::Human,
                cli_schema::ConstcheckOutputFormat::Json => cmd_constcheck::ConstcheckOutputFormat::Json,
            };
            cmd_constcheck::cmd_constcheck(&file, config.as_deref(), c_format)
        }
        Command::SpecInfo {
            file,
            format,
        } => {
            let s_format = match format {
                cli_schema::SpecinfoOutputFormat::Human => cmd_specinfo::SpecinfoOutputFormat::Human,
                cli_schema::SpecinfoOutputFormat::Json => cmd_specinfo::SpecinfoOutputFormat::Json,
            };
            cmd_specinfo::cmd_specinfo(&file, s_format)
        }
        Command::VarTrack {
            file,
            format,
        } => {
            let v_format = match format {
                cli_schema::VartrackOutputFormat::Human => cmd_vartrack::VartrackOutputFormat::Human,
                cli_schema::VartrackOutputFormat::Json => cmd_vartrack::VartrackOutputFormat::Json,
            };
            cmd_vartrack::cmd_vartrack(&file, v_format)
        }
        Command::CfgGen {
            file,
            format,
        } => {
            let c_format = match format {
                cli_schema::CfggenOutputFormat::Human => cmd_cfggen::CfggenOutputFormat::Human,
                cli_schema::CfggenOutputFormat::Json => cmd_cfggen::CfggenOutputFormat::Json,
            };
            cmd_cfggen::cmd_cfggen(&file, c_format)
        }
        Command::DepGraph {
            file,
            format,
        } => {
            let d_format = match format {
                cli_schema::DepgraphOutputFormat::Human => cmd_depgraph::DepgraphOutputFormat::Human,
                cli_schema::DepgraphOutputFormat::Json => cmd_depgraph::DepgraphOutputFormat::Json,
                cli_schema::DepgraphOutputFormat::Dot => cmd_depgraph::DepgraphOutputFormat::Dot,
            };
            cmd_depgraph::cmd_depgraph(&file, d_format)
        }
        Command::InitCount {
            file,
            config,
            format,
        } => {
            let i_format = match format {
                cli_schema::InitcountOutputFormat::Human => cmd_initcount::InitcountOutputFormat::Human,
                cli_schema::InitcountOutputFormat::Json => cmd_initcount::InitcountOutputFormat::Json,
            };
            cmd_initcount::cmd_initcount(&file, config.as_deref(), i_format)
        }
        Command::BranchFactor {
            file,
            config,
            max_states,
            format,
        } => {
            let b_format = match format {
                cli_schema::BranchfactorOutputFormat::Human => cmd_branchfactor::BranchfactorOutputFormat::Human,
                cli_schema::BranchfactorOutputFormat::Json => cmd_branchfactor::BranchfactorOutputFormat::Json,
            };
            cmd_branchfactor::cmd_branchfactor(&file, config.as_deref(), max_states, b_format)
        }
        Command::StateGraph {
            file,
            config,
            max_states,
            format,
        } => {
            let s_format = match format {
                cli_schema::StategraphOutputFormat::Human => cmd_stategraph::StategraphOutputFormat::Human,
                cli_schema::StategraphOutputFormat::Json => cmd_stategraph::StategraphOutputFormat::Json,
            };
            cmd_stategraph::cmd_stategraph(&file, config.as_deref(), max_states, s_format)
        }
        Command::Predicate {
            file,
            format,
        } => {
            let p_format = match format {
                cli_schema::PredicateOutputFormat::Human => cmd_predicate::PredicateOutputFormat::Human,
                cli_schema::PredicateOutputFormat::Json => cmd_predicate::PredicateOutputFormat::Json,
            };
            cmd_predicate::cmd_predicate(&file, p_format)
        }
        Command::ModuleInfo {
            file,
            format,
        } => {
            let m_format = match format {
                cli_schema::ModuleinfoOutputFormat::Human => cmd_moduleinfo::ModuleinfoOutputFormat::Human,
                cli_schema::ModuleinfoOutputFormat::Json => cmd_moduleinfo::ModuleinfoOutputFormat::Json,
            };
            cmd_moduleinfo::cmd_moduleinfo(&file, m_format)
        }
        Command::OpArity {
            file,
            format,
        } => {
            let o_format = match format {
                cli_schema::OparityOutputFormat::Human => cmd_oparity::OparityOutputFormat::Human,
                cli_schema::OparityOutputFormat::Json => cmd_oparity::OparityOutputFormat::Json,
            };
            cmd_oparity::cmd_oparity(&file, o_format)
        }
        Command::UnusedVar {
            file,
            format,
        } => {
            let u_format = match format {
                cli_schema::UnusedvarOutputFormat::Human => cmd_unusedvar::UnusedvarOutputFormat::Human,
                cli_schema::UnusedvarOutputFormat::Json => cmd_unusedvar::UnusedvarOutputFormat::Json,
            };
            cmd_unusedvar::cmd_unusedvar(&file, u_format)
        }
        Command::ExprCount {
            file,
            format,
        } => {
            let e_format = match format {
                cli_schema::ExprcountOutputFormat::Human => cmd_exprcount::ExprcountOutputFormat::Human,
                cli_schema::ExprcountOutputFormat::Json => cmd_exprcount::ExprcountOutputFormat::Json,
            };
            cmd_exprcount::cmd_exprcount(&file, e_format)
        }
        Command::SpecSize {
            file,
            format,
        } => {
            let s_format = match format {
                cli_schema::SpecsizeOutputFormat::Human => cmd_specsize::SpecsizeOutputFormat::Human,
                cli_schema::SpecsizeOutputFormat::Json => cmd_specsize::SpecsizeOutputFormat::Json,
            };
            cmd_specsize::cmd_specsize(&file, s_format)
        }
        Command::ConstList {
            file,
            format,
        } => {
            let c_format = match format {
                cli_schema::ConstlistOutputFormat::Human => cmd_constlist::ConstlistOutputFormat::Human,
                cli_schema::ConstlistOutputFormat::Json => cmd_constlist::ConstlistOutputFormat::Json,
            };
            cmd_constlist::cmd_constlist(&file, c_format)
        }
        Command::VarList {
            file,
            format,
        } => {
            let v_format = match format {
                cli_schema::VarlistOutputFormat::Human => cmd_varlist::VarlistOutputFormat::Human,
                cli_schema::VarlistOutputFormat::Json => cmd_varlist::VarlistOutputFormat::Json,
            };
            cmd_varlist::cmd_varlist(&file, v_format)
        }
        Command::UnusedConst {
            file,
            format,
        } => {
            let u_format = match format {
                cli_schema::UnusedconstOutputFormat::Human => cmd_unusedconst::UnusedconstOutputFormat::Human,
                cli_schema::UnusedconstOutputFormat::Json => cmd_unusedconst::UnusedconstOutputFormat::Json,
            };
            cmd_unusedconst::cmd_unusedconst(&file, u_format)
        }
        Command::AstDepth {
            file,
            format,
        } => {
            let a_format = match format {
                cli_schema::AstdepthOutputFormat::Human => cmd_astdepth::AstdepthOutputFormat::Human,
                cli_schema::AstdepthOutputFormat::Json => cmd_astdepth::AstdepthOutputFormat::Json,
            };
            cmd_astdepth::cmd_astdepth(&file, a_format)
        }
        Command::OpList {
            file,
            format,
        } => {
            let o_format = match format {
                cli_schema::OplistOutputFormat::Human => cmd_oplist::OplistOutputFormat::Human,
                cli_schema::OplistOutputFormat::Json => cmd_oplist::OplistOutputFormat::Json,
            };
            cmd_oplist::cmd_oplist(&file, o_format)
        }
        Command::Extends {
            file,
            format,
        } => {
            let e_format = match format {
                cli_schema::ExtendsOutputFormat::Human => cmd_extends::ExtendsOutputFormat::Human,
                cli_schema::ExtendsOutputFormat::Json => cmd_extends::ExtendsOutputFormat::Json,
            };
            cmd_extends::cmd_extends(&file, e_format)
        }
        Command::SetOps {
            file,
            format,
        } => {
            let s_format = match format {
                cli_schema::SetopsOutputFormat::Human => cmd_setops::SetopsOutputFormat::Human,
                cli_schema::SetopsOutputFormat::Json => cmd_setops::SetopsOutputFormat::Json,
            };
            cmd_setops::cmd_setops(&file, s_format)
        }
        Command::QuantCount {
            file,
            format,
        } => {
            let q_format = match format {
                cli_schema::QuantcountOutputFormat::Human => cmd_quantcount::QuantcountOutputFormat::Human,
                cli_schema::QuantcountOutputFormat::Json => cmd_quantcount::QuantcountOutputFormat::Json,
            };
            cmd_quantcount::cmd_quantcount(&file, q_format)
        }
        Command::PrimeCount { file, format } => {
            let p_format = match format {
                cli_schema::PrimecountOutputFormat::Human => cmd_primecount::PrimecountOutputFormat::Human,
                cli_schema::PrimecountOutputFormat::Json => cmd_primecount::PrimecountOutputFormat::Json,
            };
            cmd_primecount::cmd_primecount(&file, p_format)
        }
        Command::IfCount { file, format } => {
            let i_format = match format {
                cli_schema::IfcountOutputFormat::Human => cmd_ifcount::IfcountOutputFormat::Human,
                cli_schema::IfcountOutputFormat::Json => cmd_ifcount::IfcountOutputFormat::Json,
            };
            cmd_ifcount::cmd_ifcount(&file, i_format)
        }
        Command::LetCount { file, format } => {
            let l_format = match format {
                cli_schema::LetcountOutputFormat::Human => cmd_letcount::LetcountOutputFormat::Human,
                cli_schema::LetcountOutputFormat::Json => cmd_letcount::LetcountOutputFormat::Json,
            };
            cmd_letcount::cmd_letcount(&file, l_format)
        }
        Command::ChooseCount { file, format } => {
            let f = match format {
                cli_schema::ChoosecountOutputFormat::Human => cmd_choosecount::ChoosecountOutputFormat::Human,
                cli_schema::ChoosecountOutputFormat::Json => cmd_choosecount::ChoosecountOutputFormat::Json,
            };
            cmd_choosecount::cmd_choosecount(&file, f)
        }
        Command::CaseCount { file, format } => {
            let f = match format {
                cli_schema::CasecountOutputFormat::Human => cmd_casecount::CasecountOutputFormat::Human,
                cli_schema::CasecountOutputFormat::Json => cmd_casecount::CasecountOutputFormat::Json,
            };
            cmd_casecount::cmd_casecount(&file, f)
        }
        Command::RecordOps { file, format } => {
            let f = match format {
                cli_schema::RecordopsOutputFormat::Human => cmd_recordops::RecordopsOutputFormat::Human,
                cli_schema::RecordopsOutputFormat::Json => cmd_recordops::RecordopsOutputFormat::Json,
            };
            cmd_recordops::cmd_recordops(&file, f)
        }
        Command::TemporalOps { file, format } => {
            let f = match format {
                cli_schema::TemporalopsOutputFormat::Human => cmd_temporalops::TemporalopsOutputFormat::Human,
                cli_schema::TemporalopsOutputFormat::Json => cmd_temporalops::TemporalopsOutputFormat::Json,
            };
            cmd_temporalops::cmd_temporalops(&file, f)
        }
        Command::Unchanged { file, format } => {
            let f = match format {
                cli_schema::UnchangedOutputFormat::Human => cmd_unchanged::UnchangedOutputFormat::Human,
                cli_schema::UnchangedOutputFormat::Json => cmd_unchanged::UnchangedOutputFormat::Json,
            };
            cmd_unchanged::cmd_unchanged(&file, f)
        }
        Command::Enabled { file, format } => {
            let f = match format {
                cli_schema::EnabledOutputFormat::Human => cmd_enabled::EnabledOutputFormat::Human,
                cli_schema::EnabledOutputFormat::Json => cmd_enabled::EnabledOutputFormat::Json,
            };
            cmd_enabled::cmd_enabled(&file, f)
        }
        Command::ThreadCheck { file, workers, max_states, max_depth, emit_tla, output } => {
            cmd_threadcheck::cmd_threadcheck(&file, workers, max_states, max_depth, emit_tla, output)
        }
    }
}

#[cfg(test)]
mod tests {
    use clap::Parser;

    use super::cli_schema::{Cli, Command};
    use super::cmd_check::select_check_deadlock;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn deadlock_check_not_disabled_by_stuttering_allowed() {
        let config = tla_check::Config {
            check_deadlock: true,
            check_deadlock_explicit: false,
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };

        let tree = tla_core::parse_to_syntax_tree(
            r#"
            ---- MODULE M ----
            VARIABLE x
            Init == x = 0
            Next == x' = x
            ====
        "#,
        );
        let resolved = tla_check::resolve_spec_from_config(&config, &tree).unwrap();

        assert!(select_check_deadlock(false, Some(&resolved), &config));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn no_deadlock_flag_disables_deadlock_check() {
        let config = tla_check::Config::default();
        assert!(!select_check_deadlock(true, None, &config));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn petri_command_parses_shared_petri_args() {
        let cli = Cli::try_parse_from([
            "tla2",
            "petri",
            "models/TokenRing/model.pnml",
            "--examination",
            "ReachabilityDeadlock",
            "--threads",
            "4",
            "--storage",
            "disk",
        ])
        .expect("petri command should parse");

        match cli.command {
            Command::Petri {
                model,
                examination,
                args,
            } => {
                assert_eq!(
                    model,
                    std::path::PathBuf::from("models/TokenRing/model.pnml")
                );
                assert_eq!(examination, "ReachabilityDeadlock");
                assert_eq!(args.threads, 4);
                assert_eq!(args.storage, tla_petri::cli::RequestedStorageMode::Disk);
            }
            _ => panic!("expected petri command"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn mcc_command_allows_env_style_missing_examination() {
        let cli = Cli::try_parse_from(["tla2", "mcc", "benchmarks/mcc/TokenRing"])
            .expect("mcc command should parse");

        match cli.command {
            Command::Mcc {
                model_dir,
                examination,
                args,
            } => {
                assert_eq!(
                    model_dir,
                    Some(std::path::PathBuf::from("benchmarks/mcc/TokenRing"))
                );
                assert_eq!(examination, None);
                assert_eq!(args.threads, 1);
            }
            _ => panic!("expected mcc command"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn petri_command_rejects_zero_threads() {
        let err = Cli::try_parse_from([
            "tla2",
            "petri",
            "models/TokenRing/model.pnml",
            "--examination",
            "ReachabilityDeadlock",
            "--threads",
            "0",
        ])
        .expect_err("--threads 0 should be rejected");
        assert!(err.to_string().contains("--threads"));
        assert!(err.to_string().contains(">= 1"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn mcc_command_rejects_zero_checkpoint_interval() {
        let err = Cli::try_parse_from([
            "tla2",
            "mcc",
            "benchmarks/mcc/TokenRing",
            "--checkpoint-interval-states",
            "0",
        ])
        .expect_err("--checkpoint-interval-states 0 should be rejected");
        assert!(err.to_string().contains("--checkpoint-interval-states"));
        assert!(err.to_string().contains(">= 1"));
    }

    /// Part of #3759: --init, --next, --inv CLI flags parse correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_init_next_inv_flags() {
        let cli = Cli::try_parse_from([
            "tla2", "check", "Spec.tla", "--init", "MyInit", "--next", "MyNext", "--inv", "TypeOK",
            "--inv", "Safety",
        ])
        .expect("check command with --init/--next/--inv should parse");

        match cli.command {
            Command::Check {
                init,
                next,
                invariants,
                ..
            } => {
                assert_eq!(init.as_deref(), Some("MyInit"));
                assert_eq!(next.as_deref(), Some("MyNext"));
                assert_eq!(invariants, vec!["TypeOK", "Safety"]);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3759: --init without --next is allowed (partial override).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_init_only() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--init", "MyInit"])
            .expect("check command with --init only should parse");

        match cli.command {
            Command::Check { init, next, .. } => {
                assert_eq!(init.as_deref(), Some("MyInit"));
                assert!(next.is_none());
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3759: --inv without --init/--next is allowed (override invariants only).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_inv_only() {
        let cli = Cli::try_parse_from([
            "tla2", "check", "Spec.tla", "--inv", "TypeOK", "--inv", "Safe",
        ])
        .expect("check command with --inv only should parse");

        match cli.command {
            Command::Check {
                init,
                next,
                invariants,
                ..
            } => {
                assert!(init.is_none());
                assert!(next.is_none());
                assert_eq!(invariants, vec!["TypeOK", "Safe"]);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3779: --prop flags parse correctly (single and multiple).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_prop_flags() {
        let cli = Cli::try_parse_from([
            "tla2", "check", "Spec.tla", "--prop", "Liveness", "--prop", "Fairness",
        ])
        .expect("check command with --prop should parse");

        match cli.command {
            Command::Check { properties, .. } => {
                assert_eq!(properties, vec!["Liveness", "Fairness"]);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3779: --const flags parse correctly (single and multiple).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_const_flags() {
        let cli = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--const",
            "N=3",
            "--const",
            "Procs={p1,p2,p3}",
        ])
        .expect("check command with --const should parse");

        match cli.command {
            Command::Check { constants, .. } => {
                assert_eq!(constants, vec!["N=3", "Procs={p1,p2,p3}"]);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3779: --no-config conflicts with --config.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_no_config_conflicts_with_config() {
        let err = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--no-config",
            "--config",
            "Spec.cfg",
        ])
        .expect_err("--no-config and --config should conflict");
        let msg = err.to_string();
        assert!(
            msg.contains("--no-config") || msg.contains("--config"),
            "error should mention the conflicting flags: {msg}"
        );
    }

    /// Part of #3779: full config-free CLI parses all flags together.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_full_config_free_flags() {
        let cli = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--no-config",
            "--init",
            "MyInit",
            "--next",
            "MyNext",
            "--inv",
            "TypeOK",
            "--prop",
            "Liveness",
            "--const",
            "N=3",
        ])
        .expect("full config-free flags should parse");

        match cli.command {
            Command::Check {
                init,
                next,
                invariants,
                properties,
                constants,
                no_config,
                ..
            } => {
                assert_eq!(init.as_deref(), Some("MyInit"));
                assert_eq!(next.as_deref(), Some("MyNext"));
                assert_eq!(invariants, vec!["TypeOK"]);
                assert_eq!(properties, vec!["Liveness"]);
                assert_eq!(constants, vec!["N=3"]);
                assert!(no_config);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3723: --strategy flag parses correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_strategy_quick() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--strategy", "quick"])
            .expect("check command with --strategy quick should parse");

        match cli.command {
            Command::Check {
                strategy, pipeline, ..
            } => {
                assert!(
                    matches!(strategy, Some(crate::cli_schema::StrategyArg::Quick)),
                    "strategy should be Quick"
                );
                assert!(
                    !pipeline,
                    "pipeline should not be set when using --strategy"
                );
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3723: --strategy full parses correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_strategy_full() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--strategy", "full"])
            .expect("check command with --strategy full should parse");

        match cli.command {
            Command::Check { strategy, .. } => {
                assert!(
                    matches!(strategy, Some(crate::cli_schema::StrategyArg::Full)),
                    "strategy should be Full"
                );
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3723: --strategy auto parses correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_strategy_auto() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--strategy", "auto"])
            .expect("check command with --strategy auto should parse");

        match cli.command {
            Command::Check { strategy, .. } => {
                assert!(
                    matches!(strategy, Some(crate::cli_schema::StrategyArg::Auto)),
                    "strategy should be Auto"
                );
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3723: --strategy conflicts with --pipeline.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_strategy_conflicts_with_pipeline() {
        let err = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--strategy",
            "quick",
            "--pipeline",
        ])
        .expect_err("--strategy and --pipeline should conflict");
        let msg = err.to_string();
        assert!(
            msg.contains("--pipeline") || msg.contains("--strategy"),
            "error should mention the conflicting flags: {msg}"
        );
    }

    /// Part of #3780: --trace-inv flags parse correctly (single and multiple).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_trace_inv_flags() {
        let cli = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--trace-inv",
            "MonotonicTrace",
            "--trace-inv",
            "ConservedTrace",
        ])
        .expect("check command with --trace-inv should parse");

        match cli.command {
            Command::Check {
                trace_invariants, ..
            } => {
                assert_eq!(
                    trace_invariants,
                    vec!["MonotonicTrace", "ConservedTrace"],
                    "expected two trace invariants"
                );
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3780: --trace-invariant long-form alias parses the same as --trace-inv.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_trace_invariant_alias() {
        let cli = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--trace-invariant",
            "MonotonicTrace",
            "--trace-invariant",
            "ConservedTrace",
        ])
        .expect("check command with --trace-invariant alias should parse");

        match cli.command {
            Command::Check {
                trace_invariants, ..
            } => {
                assert_eq!(
                    trace_invariants,
                    vec!["MonotonicTrace", "ConservedTrace"],
                    "expected two trace invariants from --trace-invariant alias"
                );
            }
            _ => panic!("expected Check command"),
        }
    }

    /// Part of #3780: --trace-inv can be combined with --inv.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_trace_inv_with_regular_inv() {
        let cli = Cli::try_parse_from([
            "tla2",
            "check",
            "Spec.tla",
            "--inv",
            "TypeOK",
            "--trace-inv",
            "HistoryInv",
        ])
        .expect("check command with --inv and --trace-inv should parse");

        match cli.command {
            Command::Check {
                invariants,
                trace_invariants,
                ..
            } => {
                assert_eq!(invariants, vec!["TypeOK"]);
                assert_eq!(trace_invariants, vec!["HistoryInv"]);
            }
            _ => panic!("expected Check command"),
        }
    }

    /// #4035: --jit flag parses correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_jit_flag() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--jit"])
            .expect("check command with --jit should parse");

        match cli.command {
            Command::Check { jit, .. } => {
                assert!(jit, "--jit should be true");
            }
            _ => panic!("expected Check command"),
        }
    }

    /// #4035: --jit defaults to false (JIT is opt-in).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_jit_default_false() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla"])
            .expect("check command without --jit should parse");

        match cli.command {
            Command::Check { jit, .. } => {
                assert!(!jit, "--jit should default to false");
            }
            _ => panic!("expected Check command"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_parses_jit_verify_flag() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla", "--jit-verify"])
            .expect("check command with --jit-verify should parse");

        match cli.command {
            Command::Check { jit_verify, .. } => {
                assert!(jit_verify, "--jit-verify should be true");
            }
            _ => panic!("expected Check command"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn check_command_jit_verify_default_false() {
        let cli = Cli::try_parse_from(["tla2", "check", "Spec.tla"])
            .expect("check command without --jit-verify should parse");

        match cli.command {
            Command::Check { jit_verify, .. } => {
                assert!(!jit_verify, "--jit-verify should default to false");
            }
            _ => panic!("expected Check command"),
        }
    }
}
