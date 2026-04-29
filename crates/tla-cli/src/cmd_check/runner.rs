// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::soundness::print_provenance_human;
use super::*;

#[cfg(test)]
mod tests;

/// Context for human-readable model checking header output.
pub(super) struct CheckHeaderCtx<'a> {
    pub(super) file: &'a Path,
    pub(super) config_path: &'a Path,
    pub(super) config: &'a tla_check::Config,
    pub(super) workers: usize,
    pub(super) continue_on_error: bool,
    pub(super) max_states: usize,
    pub(super) max_depth: usize,
    pub(super) memory_limit: usize,
    pub(super) disk_limit: usize,
    pub(super) store_states: bool,
    pub(super) store_states_auto_enabled: bool,
    pub(super) no_trace: bool,
    pub(super) skip_liveness_for_benchmark: bool,
    pub(super) soundness: &'a SoundnessProvenance,
    pub(super) completeness: SearchCompleteness,
}

fn no_trace_status_line() -> &'static str {
    "Requested --no-trace: trace-file reconstruction is disabled; safety counterexample traces may be unavailable."
}

fn auto_sequential_reason(
    config: &tla_check::Config,
    workers: usize,
    _continue_on_error: bool,
) -> Option<&'static str> {
    if workers != 0 {
        return None;
    }
    // Fixes #4021: Force sequential mode in auto (workers=0) whenever invariants
    // are present, regardless of --continue-on-error. The parallel BFS enumerator
    // can produce ghost states for specs with state-dependent CHOOSE (e.g., btree's
    // ChooseFreeNode), causing false invariant violations and deadlock detection.
    // Previously, this only triggered when !continue_on_error, so `tla2 diagnose`
    // (which passes --continue-on-error) would run btree in parallel and fail.
    // TLC always checks invariants sequentially; this matches that behavior.
    if !config.invariants.is_empty() {
        return Some("invariant-stop TLC parity");
    }
    None
}

/// Print the human-readable header for model checking.
pub(super) fn print_check_header(ctx: &CheckHeaderCtx<'_>) {
    println!("Model checking: {}", ctx.file.display());
    println!("Config: {}", ctx.config_path.display());
    if let Some(ref spec) = ctx.config.specification {
        println!(
            "SPECIFICATION: {} (resolved to INIT: {}, NEXT: {})",
            spec,
            ctx.config.init.as_deref().unwrap_or("?"),
            ctx.config.next.as_deref().unwrap_or("?")
        );
    } else {
        if let Some(ref init) = ctx.config.init {
            println!("INIT: {}", init);
        }
        if let Some(ref next) = ctx.config.next {
            println!("NEXT: {}", next);
        }
    }
    if !ctx.config.invariants.is_empty() {
        println!("INVARIANTS: {}", ctx.config.invariants.join(", "));
    }
    if !ctx.config.trace_invariants.is_empty() {
        println!(
            "TRACE INVARIANTS: {}",
            ctx.config.trace_invariants.join(", ")
        );
    }
    if !ctx.config.properties.is_empty() {
        println!("PROPERTIES: {}", ctx.config.properties.join(", "));
    }
    if ctx.config.liveness_execution.uses_on_the_fly() && !ctx.config.properties.is_empty() {
        println!("Liveness: on-the-fly");
    }
    if let Some(reason) = auto_sequential_reason(ctx.config, ctx.workers, ctx.continue_on_error) {
        println!("Mode: sequential (auto: {reason})");
    } else if ctx.workers == 0 {
        println!("Mode: auto (adaptive strategy selection)");
    } else if ctx.workers == 1 {
        println!("Mode: sequential (1 worker)");
    } else {
        println!("Mode: parallel ({} workers)", ctx.workers);
    }
    println!();

    if cfg!(debug_assertions) {
        println!(
            "Note: running an unoptimized debug build; for performance runs use a release build (e.g., `cargo run --release --bin tla2 -- check ...`)."
        );
        println!();
    }
    if ctx.skip_liveness_for_benchmark && !ctx.config.properties.is_empty() {
        println!("Note: `TLA2_SKIP_LIVENESS=1` set; PROPERTY/liveness checking will be skipped.");
        println!();
    }
    if ctx.max_states > 0 {
        println!("Max states: {}", ctx.max_states);
    }
    if ctx.max_depth > 0 {
        println!("Max depth: {}", ctx.max_depth);
    }
    if ctx.memory_limit > 0 {
        println!("Memory limit: {} MB", ctx.memory_limit);
    }
    if ctx.disk_limit > 0 {
        println!("Disk limit: {} MB", ctx.disk_limit);
    }
    if ctx.store_states_auto_enabled {
        println!(
            "Store-states mode: full states in memory (42x more memory; auto-enabled for PROPERTY/liveness checking)"
        );
    } else if ctx.store_states {
        println!("Store-states mode: full states in memory (42x more memory)");
    } else if ctx.no_trace {
        println!("{}", no_trace_status_line());
    }
    println!();
    print_provenance_human(ctx.soundness, ctx.completeness);
    println!();
}

#[cfg(feature = "z4")]
fn print_structured_symbolic_result(
    output_format: OutputFormat,
    value: &serde_json::Value,
) -> Result<()> {
    let rendered = if matches!(output_format, OutputFormat::Json) {
        serde_json::to_string_pretty(value)?
    } else {
        serde_json::to_string(value)?
    };
    println!("{rendered}");
    Ok(())
}

#[cfg(feature = "z4")]
fn print_bmc_trace_human(trace: &[tla_check::BmcState]) {
    eprintln!("Counterexample trace ({} states):", trace.len());
    for state in trace {
        eprintln!("  State {}:", state.step);
        let mut assignments: Vec<_> = state.assignments.iter().collect();
        assignments.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
        for (var, value) in assignments {
            match value {
                tla_check::BmcValue::Bool(v) => eprintln!("    {} = {}", var, v),
                tla_check::BmcValue::Int(v) => eprintln!("    {} = {}", var, v),
                tla_check::BmcValue::BigInt(v) => eprintln!("    {} = {}", var, v),
                tla_check::BmcValue::Set(members) => {
                    eprintln!(
                        "    {} = {{{}}} ({} elements)",
                        var,
                        members.len(),
                        members.len()
                    );
                }
                tla_check::BmcValue::Sequence(elems) => {
                    eprintln!("    {} = <<...>> ({} elements)", var, elems.len());
                }
                tla_check::BmcValue::Function(entries) => {
                    eprintln!("    {} = [func] ({} entries)", var, entries.len());
                }
                tla_check::BmcValue::Record(fields) => {
                    let field_names: Vec<&str> =
                        fields.iter().map(|(name, _)| name.as_str()).collect();
                    eprintln!("    {} = [{}]", var, field_names.join(", "));
                }
                tla_check::BmcValue::Tuple(elems) => {
                    eprintln!("    {} = <<...>> ({} elements, tuple)", var, elems.len());
                }
            }
        }
    }
}

/// Run BMC symbolic bug finding (extracted from cmd_check).
#[cfg(feature = "z4")]
pub(super) fn run_bmc_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    max_depth: usize,
    incremental: bool,
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{check_bmc, BmcConfig, BmcResult};

    if matches!(output_format, OutputFormat::TlcTool) {
        bail!("BMC output is not supported in --output tlc-tool mode");
    }

    if matches!(output_format, OutputFormat::Human) {
        println!("BMC mode: symbolic bounded model checking via z4");
        println!("Depth bound: {}", max_depth);
        if incremental {
            println!("Incremental solving: enabled (reusing solver across depths)");
        }
        println!();
    }

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(module);
    for m in checker_modules {
        ctx.load_module(m);
    }

    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
        bail!("Failed to bind constants: {}", e);
    }

    let start = Instant::now();
    let bmc_config = BmcConfig {
        max_depth,
        incremental,
        ..BmcConfig::default()
    };
    let bmc_result = check_bmc(module, config, &ctx, bmc_config);
    let elapsed = start.elapsed();

    match bmc_result {
        Ok(BmcResult::BoundReached { max_depth }) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("BMC: NO BUG FOUND up to depth {}.", max_depth);
                println!();
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "result": "no_bug_found",
                    "max_depth": max_depth,
                    "time_secs": elapsed.as_secs_f64(),
                });
                print_structured_symbolic_result(output_format, &value)?;
            }
            Ok(())
        }
        Ok(BmcResult::Violation { depth, trace }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("BMC: VIOLATION - Counterexample found at depth {}.", depth);
                eprintln!();
                print_bmc_trace_human(&trace);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("BMC found counterexample at depth {}", depth);
            }

            let value = serde_json::json!({
                "result": "violation",
                "depth": depth,
                "trace_length": trace.len(),
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Ok(BmcResult::Unknown { depth, reason }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("BMC: UNKNOWN - Could not determine safety.");
                eprintln!("Depth: {}", depth);
                eprintln!("Reason: {}", reason);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("BMC result inconclusive at depth {}: {}", depth, reason);
            }

            let value = serde_json::json!({
                "result": "unknown",
                "depth": depth,
                "reason": reason,
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("BMC error: {}", e);
            bail!("BMC failed: {}", e);
        }
    }
}

/// Run PDR/IC3 symbolic safety checking (extracted from cmd_check).
#[cfg(feature = "z4")]
pub(super) fn run_pdr_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{check_pdr, PdrResult};

    if matches!(output_format, OutputFormat::TlcTool) {
        bail!("PDR output is not supported in --output tlc-tool mode");
    }

    if matches!(output_format, OutputFormat::Human) {
        println!("PDR mode: symbolic safety checking via CHC/IC3");
        println!();
    }

    // Set up evaluation context
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(module);
    for m in checker_modules {
        ctx.load_module(m);
    }

    // Bind constants from config
    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
        bail!("Failed to bind constants: {}", e);
    }

    // Run PDR
    let start = Instant::now();
    let pdr_result = check_pdr(module, config, &ctx);
    let elapsed = start.elapsed();

    match pdr_result {
        Ok(PdrResult::Safe { invariant }) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("PDR: SAFE - All invariants hold.");
                println!();
                println!("Synthesized invariant:");
                println!("  {}", invariant);
                println!();
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "result": "safe",
                    "invariant": invariant,
                    "time_secs": elapsed.as_secs_f64(),
                });
                print_structured_symbolic_result(output_format, &value)?;
            }
            Ok(())
        }
        Ok(PdrResult::Unsafe { trace }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("PDR: UNSAFE - Counterexample found!");
                eprintln!();
                eprintln!("Counterexample trace ({} states):", trace.len());
                for (i, state) in trace.iter().enumerate() {
                    eprintln!("  State {}:", i);
                    for (var, val) in &state.assignments {
                        eprintln!("    {} = {}", var, val);
                    }
                }
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("PDR found counterexample");
            }

            let value = serde_json::json!({
                "result": "unsafe",
                "trace_length": trace.len(),
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Ok(PdrResult::Unknown { reason }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("PDR: UNKNOWN - Could not determine safety.");
                eprintln!("Reason: {}", reason);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("PDR result inconclusive: {}", reason);
            }

            let value = serde_json::json!({
                "result": "unknown",
                "reason": reason,
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("PDR error: {}", e);
            bail!("PDR failed: {}", e);
        }
    }
}

/// Run k-induction symbolic safety proving (Part of #3722).
#[cfg(feature = "z4")]
pub(super) fn run_kinduction_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    max_k: usize,
    incremental: bool,
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{check_kinduction, KInductionConfig, KInductionResult};

    if matches!(output_format, OutputFormat::TlcTool) {
        bail!("K-induction output is not supported in --output tlc-tool mode");
    }

    if matches!(output_format, OutputFormat::Human) {
        println!("K-induction mode: symbolic safety proving via z4");
        println!("Maximum induction depth: {}", max_k);
        if incremental {
            println!("Incremental solving: enabled (reusing solver across depths)");
        }
        println!();
    }

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(module);
    for m in checker_modules {
        ctx.load_module(m);
    }

    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
        bail!("Failed to bind constants: {}", e);
    }

    let start = Instant::now();
    let kind_config = KInductionConfig {
        max_k,
        incremental,
        ..KInductionConfig::default()
    };
    let kind_result = check_kinduction(module, config, &ctx, kind_config);
    let elapsed = start.elapsed();

    match kind_result {
        Ok(KInductionResult::Proved { k }) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("K-INDUCTION: PROVED - All invariants hold (k={}).", k);
                println!();
                println!(
                    "The property is {}-inductive: it holds for ALL reachable states.",
                    k
                );
                println!();
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "result": "proved",
                    "k": k,
                    "time_secs": elapsed.as_secs_f64(),
                });
                print_structured_symbolic_result(output_format, &value)?;
            }
            Ok(())
        }
        Ok(KInductionResult::Counterexample { depth, trace }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!(
                    "K-INDUCTION: VIOLATION - Counterexample found at depth {}.",
                    depth
                );
                eprintln!();
                print_bmc_trace_human(&trace);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("K-induction found counterexample at depth {}", depth);
            }

            let value = serde_json::json!({
                "result": "violation",
                "depth": depth,
                "trace_length": trace.len(),
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Ok(KInductionResult::Unknown { max_k, reason }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("K-INDUCTION: UNKNOWN - Could not prove safety.");
                eprintln!("Max depth: {}", max_k);
                eprintln!("Reason: {}", reason);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!(
                    "K-induction result inconclusive at depth {}: {}",
                    max_k,
                    reason
                );
            }

            let value = serde_json::json!({
                "result": "unknown",
                "max_k": max_k,
                "reason": reason,
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("K-induction error: {}", e);
            bail!("K-induction failed: {}", e);
        }
    }
}

/// Run symbolic simulation mode (Part of #3757, Apalache Gap 9).
///
/// Uses z4 SMT solving to explore random execution paths symbolically.
/// Each run follows one path by solving Init, then iteratively solving
/// Next to find concrete successor states, checking invariants at each step.
#[cfg(feature = "z4")]
pub(super) fn run_symbolic_sim_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    num_runs: usize,
    max_depth: usize,
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{symbolic_simulate, SymbolicSimConfig, SymbolicSimResult};

    if matches!(output_format, OutputFormat::TlcTool) {
        bail!("Symbolic simulation output is not supported in --output tlc-tool mode");
    }

    if matches!(output_format, OutputFormat::Human) {
        println!(
            "Symbolic simulation mode (Apalache-style): z4 SMT-based random trace exploration"
        );
        println!("Runs: {}", num_runs);
        println!("Max depth per run: {}", max_depth);
        println!();
    }

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(module);
    for m in checker_modules {
        ctx.load_module(m);
    }

    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
        bail!("Failed to bind constants: {}", e);
    }

    let start = Instant::now();
    let sim_config = SymbolicSimConfig {
        num_runs,
        max_depth,
        ..SymbolicSimConfig::default()
    };
    let result = symbolic_simulate(module, config, &ctx, sim_config);
    let elapsed = start.elapsed();

    match result {
        Ok(SymbolicSimResult::NoViolation {
            runs_completed,
            max_depth_reached,
            total_states,
        }) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("Symbolic simulation complete: No invariant violation found.");
                println!();
                println!("Statistics:");
                println!("  Runs completed: {}", runs_completed);
                println!("  Max depth reached: {}", max_depth_reached);
                println!("  Total states explored: {}", total_states);
                println!("  Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "mode": "symbolic_simulation",
                    "result": "no_violation",
                    "runs_completed": runs_completed,
                    "max_depth_reached": max_depth_reached,
                    "total_states": total_states,
                    "time_secs": elapsed.as_secs_f64(),
                });
                print_structured_symbolic_result(output_format, &value)?;
            }
            Ok(())
        }
        Ok(SymbolicSimResult::Violation {
            run_index,
            depth,
            trace,
        }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!(
                    "Symbolic simulation: VIOLATION found in run {} at depth {}.",
                    run_index, depth
                );
                eprintln!();
                print_bmc_trace_human(&trace);
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!(
                    "Symbolic simulation found counterexample in run {} at depth {}",
                    run_index,
                    depth
                );
            }

            let value = serde_json::json!({
                "mode": "symbolic_simulation",
                "result": "violation",
                "run_index": run_index,
                "depth": depth,
                "trace_length": trace.len(),
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Ok(SymbolicSimResult::Timeout {
            runs_completed,
            total_states,
            reason,
        }) => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("Symbolic simulation: TIMEOUT");
                eprintln!("Reason: {}", reason);
                eprintln!("Runs completed before timeout: {}", runs_completed);
                eprintln!("Total states explored: {}", total_states);
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
                bail!("Symbolic simulation timed out: {}", reason);
            }

            let value = serde_json::json!({
                "mode": "symbolic_simulation",
                "result": "timeout",
                "runs_completed": runs_completed,
                "total_states": total_states,
                "reason": reason,
                "time_secs": elapsed.as_secs_f64(),
            });
            print_structured_symbolic_result(output_format, &value)?;
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("Symbolic simulation error: {}", e);
            bail!("Symbolic simulation failed: {}", e);
        }
    }
}

/// Run inductive invariant check (Part of #3756, Apalache Gap 8).
#[cfg(feature = "z4")]
pub(super) fn run_inductive_check_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    invariant: &str,
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{check_inductive, InductiveCheckConfig, InductiveCheckResult};

    if matches!(output_format, OutputFormat::TlcTool) {
        bail!("Inductive check output is not supported in --output tlc-tool mode");
    }

    if matches!(output_format, OutputFormat::Human) {
        println!("Inductive invariant check mode (Apalache-style)");
        println!("Invariant: {}", invariant);
        println!("Phase 1: Init => {}", invariant);
        println!("Phase 2: {} /\\ Next => {}\'", invariant, invariant);
        println!();
    }

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(module);
    for m in checker_modules {
        ctx.load_module(m);
    }

    if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
        bail!("Failed to bind constants: {}", e);
    }

    let start = Instant::now();
    let ind_config = InductiveCheckConfig::new(invariant.to_string());
    let result = check_inductive(module, config, &ctx, &ind_config);
    let elapsed = start.elapsed();

    match result {
        Ok(InductiveCheckResult::Proved) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("INDUCTIVE CHECK: PROVED");
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "result": "proved",
                    "invariant": invariant,
                    "time_secs": elapsed.as_secs_f64(),
                });
                print_structured_symbolic_result(output_format, &value)?;
            }
            Ok(())
        }
        Ok(InductiveCheckResult::InitiationFailed { reason }) => {
            eprintln!("INDUCTIVE CHECK: FAILED (Phase 1 - Initiation)");
            eprintln!("Reason: {}", reason);
            bail!("Inductive check failed: initiation");
        }
        Ok(InductiveCheckResult::ConsecutionFailed { reason }) => {
            eprintln!("INDUCTIVE CHECK: FAILED (Phase 2 - Consecution)");
            eprintln!("Reason: {}", reason);
            bail!("Inductive check failed: consecution");
        }
        Ok(InductiveCheckResult::Unknown { phase, reason }) => {
            eprintln!("INDUCTIVE CHECK: UNKNOWN (Phase: {})", phase);
            eprintln!("Reason: {}", reason);
            bail!("Inductive check inconclusive");
        }
        Err(e) => bail!("Inductive check error: {}", e),
    }
}

/// Apply checker configuration common to all three modes (adaptive, sequential, parallel).
macro_rules! apply_common_checker_config {
    ($checker:expr, $cfg:expr) => {
        $checker.set_deadlock_check($cfg.check_deadlock);
        $checker.set_continue_on_error($cfg.continue_on_error);
        // `false` is semantically meaningful here: the sequential checker uses
        // set_store_states(false) to enable fp-only liveness caching (#3175).
        $checker.set_store_states($cfg.store_states);
        if let Some(ref storage) = $cfg.fingerprint_storage {
            $checker.set_fingerprint_storage(storage.clone());
        }
        $checker.set_collision_check_mode($cfg.collision_check_mode);
        if !$cfg.resolved_fairness.is_empty() {
            $checker.set_fairness($cfg.resolved_fairness.to_vec());
        }
        if $cfg.max_states > 0 {
            $checker.set_max_states($cfg.max_states);
        }
        if $cfg.max_depth > 0 {
            $checker.set_max_depth($cfg.max_depth);
        }
        if $cfg.memory_limit > 0 {
            // Convert megabytes to bytes; saturate to prevent silent wrapping
            // on 32-bit targets (Part of #2751).
            let limit_bytes = $cfg.memory_limit.saturating_mul(1024 * 1024);
            $checker.set_memory_limit(limit_bytes);
        } else {
            // Part of #2751: auto-detect system RAM so memory monitoring is
            // active by default. Users get a warning at ~72% of RAM and
            // graceful stop at ~85% instead of an OOM kill with no warning.
            // Multi-instance aware: divides budget by concurrent tla2 processes.
            if let Some((limit_bytes, total_bytes, instances)) =
                tla_check::memory_policy_system_default_info()
            {
                $checker.set_memory_limit(limit_bytes);
                tla_check::log_memory_budget(limit_bytes, total_bytes, instances);
            }
        }
        if $cfg.disk_limit > 0 {
            // Part of #3282: Convert megabytes to bytes for disk limit.
            let limit_bytes = $cfg.disk_limit.saturating_mul(1024 * 1024);
            $checker.set_disk_limit(limit_bytes);
        } else {
            // Part of #3282: auto-detect available disk so disk monitoring is
            // active by default. Users get a graceful stop instead of filling
            // the disk and crashing (TLC disk-exhaustion post-mortem).
            if let Some(limit_bytes) = tla_check::disk_limit_system_default() {
                $checker.set_disk_limit(limit_bytes);
            }
        }
    };
}

/// Register file paths and resolved spec — shared by adaptive and sequential modes.
macro_rules! register_files_and_spec {
    ($checker:expr, $cfg:expr) => {
        $checker.register_file_path(FileId(0), $cfg.file.to_path_buf());
        for (fid, path) in &$cfg.file_paths {
            $checker.register_file_path(*fid, path.clone());
        }
        if let Some(ref resolved) = $cfg.resolved_spec {
            $checker.register_inline_next(resolved)?;
            $checker.set_stuttering_allowed(resolved.stuttering_allowed);
        }
    };
}

/// Set up TLC tool output format callbacks for the sequential model checker.
///
/// Emits the TLC_COMPUTING_INIT message immediately and installs init-progress
/// and BFS-progress callbacks that produce TLC-compatible machine-readable output.
fn setup_tlc_tool_callbacks(
    checker: &mut ModelChecker<'_>,
    tool_out: &mut Option<tlc_tool::TlcToolOutput>,
) {
    if let Some(out) = tool_out.as_mut() {
        out.emit(
            tlc_codes::ec::TLC_COMPUTING_INIT,
            tlc_codes::mp::NONE,
            tlc_tool::format_tlc_computing_init_message(),
        );
    }
    checker.set_init_progress_callback(Box::new(|init| {
        let now = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
        let mut out = tlc_tool::TlcToolOutput::new();
        out.emit(
            tlc_codes::ec::TLC_INIT_GENERATED1,
            tlc_codes::mp::NONE,
            &tlc_tool::format_tlc_init_generated1_message(init.distinct_states as u64, &now),
        );
    }));

    let last_emit = std::sync::Arc::new(std::sync::Mutex::new(0.0f64));
    let last_emit2 = std::sync::Arc::clone(&last_emit);
    checker.set_progress_callback(Box::new(move |progress| {
        let should_emit = match last_emit2.lock() {
            Ok(mut last) => {
                if progress.elapsed_secs - *last >= 5.0 {
                    *last = progress.elapsed_secs;
                    true
                } else {
                    false
                }
            }
            Err(_) => true,
        };
        if !should_emit {
            return;
        }
        let now = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
        let mut out = tlc_tool::TlcToolOutput::new();
        out.emit(
            tlc_codes::ec::TLC_PROGRESS_STATS,
            tlc_codes::mp::NONE,
            &tlc_tool::format_tlc_progress_stats_message(
                progress.current_depth as u64,
                progress.states_found as u64,
                progress.states_found as u64,
                progress.queue_size as u64,
                &now,
                progress.elapsed_secs,
            ),
        );
        // Emit memory usage as a separate info line (not part of TLC protocol)
        if let Some(rss) = progress.memory_usage_bytes {
            let mb = rss as f64 / (1024.0 * 1024.0);
            eprintln!("  Memory: {mb:.1} MB RSS");
        }
    }));
}

/// Configuration for a model checker run (auto, sequential, or parallel).
pub(super) struct ModelCheckerRunCfg<'a> {
    pub(super) module: &'a tla_core::ast::Module,
    pub(super) checker_modules: &'a [&'a tla_core::ast::Module],
    pub(super) config: &'a Config,
    pub(super) workers: usize,
    pub(super) file: &'a Path,
    pub(super) file_paths: Vec<(FileId, PathBuf)>,
    pub(super) resolved_spec: &'a Option<tla_check::ResolvedSpec>,
    pub(super) check_deadlock: bool,
    pub(super) show_coverage: bool,
    pub(super) continue_on_error: bool,
    pub(super) store_states: bool,
    pub(super) no_trace: bool,
    pub(super) fingerprint_storage: &'a Option<std::sync::Arc<dyn tla_check::FingerprintSet>>,
    pub(super) trace_file: Option<TraceFile>,
    pub(super) trace_locs_storage: Option<TraceLocationsStorage>,
    pub(super) resolved_fairness: &'a [tla_check::FairnessConstraint],
    pub(super) max_states: usize,
    pub(super) max_depth: usize,
    /// Part of #2751: memory limit in megabytes (0 = unlimited).
    pub(super) memory_limit: usize,
    /// Part of #3282: disk limit in megabytes (0 = unlimited).
    pub(super) disk_limit: usize,
    pub(super) output_format: OutputFormat,
    pub(super) progress_callback: Box<dyn Fn(&Progress) + Send + Sync>,
    pub(super) checkpoint_dir: &'a Option<PathBuf>,
    pub(super) checkpoint_interval: u64,
    pub(super) resume_from: &'a Option<PathBuf>,
    pub(super) config_path: &'a Path,
    pub(super) tool_out: &'a mut Option<tlc_tool::TlcToolOutput>,
    /// Fingerprint collision detection mode.
    pub(super) collision_check_mode: tla_check::CollisionCheckMode,
}

/// Run the model checker in auto, sequential, or parallel mode (extracted from cmd_check).
pub(super) fn run_model_checker(
    cfg: ModelCheckerRunCfg<'_>,
) -> Result<(CheckResult, Option<String>)> {
    let force_sequential_auto =
        auto_sequential_reason(cfg.config, cfg.workers, cfg.continue_on_error).is_some();
    if cfg.workers == 0 && !force_sequential_auto {
        // Auto mode: use adaptive checker
        if cfg.trace_file.is_some() {
            bail!("--trace-file is only supported with --workers 1 (sequential mode)");
        }
        if cfg.trace_locs_storage.is_some() {
            bail!("--mmap-trace-locations is only supported with --workers 1 (sequential mode)");
        }
        let runtime_config = cfg.config.runtime_model_config();
        let mut checker =
            AdaptiveChecker::new_with_extends(cfg.module, cfg.checker_modules, &runtime_config);
        register_files_and_spec!(checker, cfg);
        apply_common_checker_config!(checker, cfg);
        checker.set_collect_coverage(cfg.show_coverage);
        if cfg.no_trace {
            checker.set_auto_create_trace_file(false);
        }
        // Part of #3247: progress always on for Human output.
        if matches!(cfg.output_format, OutputFormat::Human) {
            checker.set_progress_callback(cfg.progress_callback);
        }
        let (result, analysis) = checker.check();
        let strategy_info = analysis.map(|a| {
            format!(
                "Strategy: {} (estimated {} states, branching factor {:.2})",
                a.strategy, a.estimated_states, a.avg_branching_factor
            )
        });
        Ok((result, strategy_info))
    } else if cfg.workers == 1 || force_sequential_auto {
        let forced_strategy_info =
            auto_sequential_reason(cfg.config, cfg.workers, cfg.continue_on_error)
                .map(|reason| format!("Strategy: sequential (auto: {reason})"));

        let runtime_config = cfg.config.runtime_model_config();
        let mut checker =
            ModelChecker::new_with_extends(cfg.module, cfg.checker_modules, &runtime_config);
        register_files_and_spec!(checker, cfg);
        apply_common_checker_config!(checker, cfg);
        checker.set_collect_coverage(cfg.show_coverage);
        if cfg.no_trace {
            checker.set_auto_create_trace_file(false);
        }
        if let Some(tf) = cfg.trace_file {
            checker.set_trace_file(tf);
        }
        if let Some(storage) = cfg.trace_locs_storage {
            checker.set_trace_locations_storage(storage);
        }
        if matches!(cfg.output_format, OutputFormat::TlcTool) {
            setup_tlc_tool_callbacks(&mut checker, cfg.tool_out);
        } else if matches!(cfg.output_format, OutputFormat::Human) {
            // Part of #3247: progress always on for Human output.
            checker.set_progress_callback(cfg.progress_callback);
        }
        if cfg.checkpoint_dir.is_some() || cfg.resume_from.is_some() {
            checker.set_checkpoint_paths(
                Some(cfg.file.to_string_lossy().to_string()),
                Some(cfg.config_path.to_string_lossy().to_string()),
            );
        }
        if let Some(ref dir) = cfg.checkpoint_dir {
            checker.set_checkpoint(
                dir.clone(),
                std::time::Duration::from_secs(cfg.checkpoint_interval),
            );
        }
        let result = if let Some(ref resume_dir) = cfg.resume_from {
            checker.check_with_resume(resume_dir).with_context(|| {
                format!("Failed to resume from checkpoint: {}", resume_dir.display())
            })?
        } else {
            checker.check()
        };
        Ok((result, forced_strategy_info))
    } else {
        // Parallel mode
        if cfg.trace_file.is_some() {
            bail!("--trace-file is only supported with --workers 1 (sequential mode)");
        }
        if cfg.trace_locs_storage.is_some() {
            bail!("--mmap-trace-locations is only supported with --workers 1 (sequential mode)");
        }
        if cfg.show_coverage {
            bail!("--coverage is only supported with --workers 0 or --workers 1");
        }
        let runtime_config = cfg.config.runtime_model_config();
        let mut checker = ParallelChecker::new_with_extends(
            cfg.module,
            cfg.checker_modules,
            &runtime_config,
            cfg.workers,
        );
        register_files_and_spec!(checker, cfg);
        apply_common_checker_config!(checker, cfg);
        // Part of #3247: progress always on for Human output.
        if matches!(cfg.output_format, OutputFormat::Human) {
            checker.set_progress_callback(cfg.progress_callback);
        }
        // Part of #2749: Wire checkpoint/resume for parallel mode.
        if cfg.checkpoint_dir.is_some() || cfg.resume_from.is_some() {
            checker.set_checkpoint_paths(
                Some(cfg.file.to_string_lossy().to_string()),
                Some(cfg.config_path.to_string_lossy().to_string()),
            );
        }
        if let Some(ref dir) = cfg.checkpoint_dir {
            checker.set_checkpoint(
                dir.clone(),
                std::time::Duration::from_secs(cfg.checkpoint_interval),
            );
        }
        let result = if let Some(ref resume_dir) = cfg.resume_from {
            checker.check_with_resume(resume_dir).with_context(|| {
                format!("Failed to resume from checkpoint: {}", resume_dir.display())
            })?
        } else {
            checker.check()
        };
        Ok((result, None))
    }
}

/// Run portfolio racing mode: parallel BFS + symbolic strategies (Part of #3717).
///
/// Spawns multiple verification lanes in parallel via [`run_portfolio`] and
/// terminates when the first one reaches a definitive result.
pub(super) fn run_portfolio_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    strategy_names: &[String],
    output_format: OutputFormat,
) -> Result<()> {
    use tla_check::{run_portfolio, PortfolioWinner};

    if matches!(output_format, OutputFormat::Human) {
        if strategy_names.is_empty() {
            println!("Portfolio mode: racing all available strategies");
        } else {
            println!(
                "Portfolio mode: racing strategies: {}",
                strategy_names.join(", ")
            );
        }
        if !strategy_names.is_empty() {
            let unsupported: Vec<_> = strategy_names
                .iter()
                .filter(|s| !matches!(s.as_str(), "bfs" | "random" | "bmc" | "pdr" | "kinduction"))
                .collect();
            if !unsupported.is_empty() {
                eprintln!(
                    "Warning: unknown strategies ignored: {}",
                    unsupported
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
        println!();
    }

    let start = Instant::now();
    let result = run_portfolio(module, checker_modules, config, strategy_names);
    let elapsed = start.elapsed();

    let winner_str = match result.winner {
        PortfolioWinner::Bfs => "BFS (explicit-state)",
        PortfolioWinner::Pdr => "PDR (symbolic safety proving)",
        PortfolioWinner::Bmc => "BMC (symbolic bug finding)",
        PortfolioWinner::KInduction => "k-Induction (symbolic proving)",
        PortfolioWinner::Random => "Random walk",
    };

    match &result.bfs_result {
        tla_check::CheckResult::Success(stats) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("Model checking complete. No error has been found.");
                println!("  {} states found.", stats.states_found);
                println!("  Resolved by: {winner_str}");
                println!();
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "mode": "portfolio",
                    "result": "success",
                    "winner": format!("{:?}", result.winner),
                    "states_found": stats.states_found,
                    "time_secs": elapsed.as_secs_f64(),
                });
                println!("{value}");
            }
            Ok(())
        }
        tla_check::CheckResult::InvariantViolation { invariant, .. } => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("Error: Invariant {invariant} is violated.");
                eprintln!("  Resolved by: {winner_str}");
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "mode": "portfolio",
                    "result": "invariant_violation",
                    "winner": format!("{:?}", result.winner),
                    "invariant": invariant,
                    "time_secs": elapsed.as_secs_f64(),
                });
                println!("{value}");
            }
            std::process::exit(1);
        }
        other => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("Portfolio result: {other:?}");
                eprintln!("  Resolved by: {winner_str}");
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                let value = serde_json::json!({
                    "mode": "portfolio",
                    "result": format!("{other:?}"),
                    "winner": format!("{:?}", result.winner),
                    "time_secs": elapsed.as_secs_f64(),
                });
                println!("{value}");
            }
            bail!("Portfolio mode produced unexpected result: {other:?}");
        }
    }
}

/// Run fused cooperative BFS+symbolic verification (Part of #3770, Epic #3762).
///
/// Spawns BFS, BMC, and PDR lanes cooperatively via `FusedOrchestrator`.
/// BFS frontier states seed BMC; PDR proofs skip BFS invariant checks.
pub(super) fn run_fused_mode(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    output_format: OutputFormat,
    spec_file: &Path,
    config_file: Option<&Path>,
    workers: usize,
    completeness: SearchCompleteness,
) -> Result<()> {
    use tla_check::{run_fused_check, FusedWinner};

    if matches!(output_format, OutputFormat::Human) {
        println!("Fused mode: cooperative BFS + symbolic verification (CDEMC)");
        println!();
    }

    let start = Instant::now();
    let result = run_fused_check(module, checker_modules, config);
    let elapsed = start.elapsed();

    let winner_str = match result.winner {
        FusedWinner::Bfs => "BFS (explicit-state)",
        FusedWinner::Bmc => "BMC (symbolic bug finding)",
        FusedWinner::Pdr => "PDR (symbolic safety proving)",
        FusedWinner::KInduction => "k-Induction (inductive safety)",
    };

    // Report graceful degradation when symbolic lanes fail (Part of #3837).
    let degradation_summary = result.degradation.summary();
    let symbolic_coverage = result.symbolic_coverage;
    let lane_coverage = result.degradation.symbolic_coverage();

    // Part of #3837: Build a single-line user-friendly degradation info message.
    // Shows per-action symbolic coverage and lists unsupported action names.
    let degradation_info: Option<String> = if result.degradation.any_degraded()
        || !result.degradation.unsupported_action_names.is_empty()
    {
        let pct = (symbolic_coverage * 100.0) as u32;
        let compat = result.degradation.actions_smt_compatible;
        let total = result.degradation.actions_total;
        let unsupported = &result.degradation.unsupported_action_names;
        if unsupported.is_empty() {
            Some(format!(
                "Symbolic coverage: {pct}% ({compat}/{total} actions translatable)"
            ))
        } else {
            Some(format!(
                "Symbolic coverage: {pct}% ({compat}/{total} actions translatable, unsupported: {})",
                unsupported.join(", ")
            ))
        }
    } else {
        None
    };

    // Part of #3805: For JSON output, use the standard JsonOutput format so that
    // `tla2 diagnose` can parse the output. Previously the fused-mode raw JSON blob
    // was printed to stdout, breaking the diagnostic parser which expects a single
    // JSON object in SubprocessOutput format (result.status, statistics.states_found).
    // For Human output, the inline debug info is preserved unchanged.
    match &result.bfs_result {
        tla_check::CheckResult::Success(stats) => {
            if matches!(output_format, OutputFormat::Human) {
                println!("Model checking complete. No error has been found.");
                println!("  {} states found.", stats.states_found);
                if let Some(ref summary) = result.symbolic_summary {
                    println!("  {summary}");
                }
                if let Some(ref info) = degradation_info {
                    println!("  {info}");
                }
                println!("  Resolved by: {winner_str}");
                println!();
                println!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                // Emit fused metadata to stderr for debugging.
                eprintln!(
                    "[fused] winner={winner_str}, coverage={symbolic_coverage:.0}%, lane={lane_coverage:.2}"
                );
                if let Some(ref deg) = degradation_summary {
                    eprintln!("[fused] degradation: {deg}");
                }
                // Emit standard JsonOutput to stdout.
                let module_name = &module.name.node;
                let json_output = JsonOutput::new(spec_file, config_file, module_name, workers)
                    .with_completeness(completeness)
                    .with_check_result(&result.bfs_result, elapsed);
                let json_str = if matches!(output_format, OutputFormat::Jsonl) {
                    json_output.to_json_compact()
                } else {
                    json_output.to_json()
                };
                match json_str {
                    Ok(s) => println!("{s}"),
                    Err(e) => eprintln!("error: failed to serialize JSON output: {e}"),
                }
            }
            Ok(())
        }
        tla_check::CheckResult::InvariantViolation { invariant, .. } => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("Error: Invariant {invariant} is violated.");
                if let Some(ref info) = degradation_info {
                    eprintln!("  {info}");
                }
                eprintln!("  Resolved by: {winner_str}");
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                eprintln!("[fused] winner={winner_str}, invariant={invariant}");
                // Emit standard JsonOutput to stdout.
                let module_name = &module.name.node;
                let json_output = JsonOutput::new(spec_file, config_file, module_name, workers)
                    .with_completeness(completeness)
                    .with_check_result(&result.bfs_result, elapsed);
                let json_str = if matches!(output_format, OutputFormat::Jsonl) {
                    json_output.to_json_compact()
                } else {
                    json_output.to_json()
                };
                match json_str {
                    Ok(s) => println!("{s}"),
                    Err(e) => eprintln!("error: failed to serialize JSON output: {e}"),
                }
            }
            std::process::exit(1);
        }
        other => {
            if matches!(output_format, OutputFormat::Human) {
                eprintln!("Fused result: {other:?}");
                if let Some(ref info) = degradation_info {
                    eprintln!("  {info}");
                }
                eprintln!("  Resolved by: {winner_str}");
                eprintln!();
                eprintln!("Time: {:.3}s", elapsed.as_secs_f64());
            } else {
                // Emit standard JsonOutput to stdout. The caller's error handler
                // (emit_check_cli_error) would produce a generic error, but we have
                // the actual CheckResult with state counts here, so emit it properly.
                let module_name = &module.name.node;
                let json_output = JsonOutput::new(spec_file, config_file, module_name, workers)
                    .with_completeness(completeness)
                    .with_check_result(other, elapsed);
                let json_str = if matches!(output_format, OutputFormat::Jsonl) {
                    json_output.to_json_compact()
                } else {
                    json_output.to_json()
                };
                match json_str {
                    Ok(s) => println!("{s}"),
                    Err(e) => eprintln!("error: failed to serialize JSON output: {e}"),
                }
                // Exit directly — do NOT bail, which would cause the caller's error
                // handler to emit a second JSON object to stdout.
                std::process::exit(2);
            }
            bail!("Fused mode produced unexpected result: {other:?}");
        }
    }
}

/// Run multi-phase verification pipeline (Part of #3723).
///
/// Executes phases in order: RandomWalk(5s) -> BMC(30s) -> PDR(60s) -> BFS(300s).
/// Early-exits when all properties are resolved. BMC and PDR phases are only
/// available when the `z4` feature is enabled; otherwise they are silently skipped.
/// Run the multi-phase verification pipeline with a named strategy.
///
/// The strategy selects the phase configuration:
/// - Quick: RandomWalk(2s) + BMC(10s). Fast feedback for development.
/// - Full: RandomWalk(5s) + BFS(600s). TLC-equivalent completeness.
/// - Auto: walk -> BMC -> k-induction -> PDR -> BFS (adaptive early exit).
///
/// Part of #3723.
pub(super) fn run_pipeline_mode_with_strategy(
    module: &tla_core::ast::Module,
    checker_modules: &[&tla_core::ast::Module],
    config: &tla_check::Config,
    strategy: tla_check::VerificationStrategy,
    output_format: OutputFormat,
) -> Result<()> {
    use rustc_hash::FxHashMap as HashMap;
    use tla_check::{
        BfsRunner, PhaseRunner, PropertyVerdict, RandomWalkConfig, RandomWalkRunner,
        VerificationPhase,
    };

    let pipeline = strategy.into_pipeline();

    if matches!(output_format, OutputFormat::Human) {
        eprintln!("Pipeline mode: strategy={strategy}");
        let phase_names: Vec<String> = pipeline
            .phases()
            .iter()
            .filter(|p| p.enabled)
            .map(|p| format!("{}({}s)", p.phase, p.time_budget.as_secs()))
            .collect();
        eprintln!("  Phases: {}", phase_names.join(" -> "));
        eprintln!();
    }

    // Collect invariant names as property IDs.
    let properties: Vec<String> = config.invariants.clone();
    if properties.is_empty() {
        if matches!(output_format, OutputFormat::Human) {
            eprintln!("Pipeline: no invariants configured, nothing to verify.");
        }
        return Ok(());
    }

    let runtime_config = config.runtime_model_config();

    // Build runners for each phase.
    let mut runners: HashMap<VerificationPhase, Box<dyn PhaseRunner>> = HashMap::default();

    // RandomWalk runner
    let walk_checker =
        tla_check::ModelChecker::new_with_extends(module, checker_modules, &runtime_config);
    let walk_config = RandomWalkConfig {
        num_walks: 100,
        max_depth: 10_000,
        seed: None,
    };
    runners.insert(
        VerificationPhase::RandomWalk,
        Box::new(RandomWalkRunner::new(walk_checker, walk_config)),
    );

    // BMC/PDR/KInduction runners (z4 feature gate)
    #[cfg(feature = "z4")]
    {
        let mut ctx = tla_check::EvalCtx::new();
        ctx.load_module(module);
        for m in checker_modules {
            ctx.load_module(m);
        }
        if let Err(e) = tla_check::bind_constants_from_config(&mut ctx, config) {
            eprintln!("Pipeline: failed to bind constants for BMC/PDR: {e}");
        } else {
            // Leak the EvalCtx to get a 'static reference that can be stored
            // in Box<dyn PhaseRunner>. This is acceptable because pipeline mode
            // runs once per invocation and the process exits afterward.
            let ctx: &'static tla_check::EvalCtx = Box::leak(Box::new(ctx));

            runners.insert(
                VerificationPhase::Bmc,
                Box::new(tla_check::BmcRunner::new(module, config, ctx, 20)),
            );
            runners.insert(
                VerificationPhase::Pdr,
                Box::new(tla_check::PdrRunner::new(module, config, ctx)),
            );
            runners.insert(
                VerificationPhase::KInduction,
                Box::new(tla_check::KInductionRunner::new(module, config, ctx, 20)),
            );
        }
    }

    // BFS runner (always available)
    runners.insert(
        VerificationPhase::Bfs,
        Box::new(BfsRunner::new(module, checker_modules, config)),
    );

    let start = Instant::now();
    let result = pipeline.run(&properties, &mut runners);
    let elapsed = start.elapsed();

    // Report results.
    if matches!(output_format, OutputFormat::Human) {
        eprintln!();
        eprintln!(
            "Pipeline ({strategy}) complete in {:.3}s",
            elapsed.as_secs_f64()
        );
        for record in &result.phases_run {
            eprintln!(
                "  {}: {:.3}s, {} properties resolved",
                record.phase,
                record.elapsed.as_secs_f64(),
                record.properties_resolved,
            );
        }
        eprintln!();
        let mut any_violated = false;
        for (prop, verdict) in &result.verdicts {
            let label = match verdict {
                PropertyVerdict::Satisfied => "SATISFIED",
                PropertyVerdict::Violated => {
                    any_violated = true;
                    "VIOLATED"
                }
                PropertyVerdict::Unknown => "UNKNOWN",
            };
            eprintln!("  {prop}: {label}");
        }
        if any_violated {
            bail!("Pipeline found invariant violation(s)");
        }
    } else {
        // JSON output
        let verdicts_json: serde_json::Value = result
            .verdicts
            .iter()
            .map(|(k, v)| {
                let label = match v {
                    PropertyVerdict::Satisfied => "satisfied",
                    PropertyVerdict::Violated => "violated",
                    PropertyVerdict::Unknown => "unknown",
                };
                (k.clone(), serde_json::Value::String(label.to_string()))
            })
            .collect::<serde_json::Map<String, serde_json::Value>>()
            .into();

        let json = serde_json::json!({
            "mode": "pipeline",
            "strategy": strategy.to_string(),
            "time_secs": elapsed.as_secs_f64(),
            "phases_run": result.phases_run.len(),
            "verdicts": verdicts_json,
        });
        println!("{json}");

        if result
            .verdicts
            .values()
            .any(|v| *v == PropertyVerdict::Violated)
        {
            std::process::exit(1);
        }
    }

    Ok(())
}
