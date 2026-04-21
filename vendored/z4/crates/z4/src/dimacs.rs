// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! DIMACS CNF solver entry points.
//!
//! Extracted from `main.rs` as part of code-health module split.
//! Contains format detection, solver setup, and result output for SAT competition format.

use super::{
    exit_if_timed_out, global_elapsed, is_timed_out, stats_output, ProofConfig, ProofFormat,
    INTERRUPT_HANDLE,
};
use std::env;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use z4_sat::{
    adjust_features_for_instance, parse_dimacs, should_disable_reorder, Extension, InstanceClass,
    ProofOutput, SatFeatures, SatResult, Solver as SatSolver, SolverVariant, TlaTraceable,
    Variable, VariantInput,
};

/// SAT TLA trace module name matching specs/cdcl_test.tla.
const SAT_TRACE_MODULE: &str = "cdcl_test";
/// SAT TLA trace variables matching specs/cdcl_test.tla.
const SAT_TRACE_VARIABLES: [&str; 5] = [
    "assignment",
    "trail",
    "state",
    "decisionLevel",
    "learnedClauses",
];

pub(crate) fn is_dimacs_format(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Comment lines in DIMACS start with 'c'
        if trimmed.starts_with('c') {
            continue;
        }
        // Problem line starts with 'p cnf'
        if trimmed.starts_with("p cnf") {
            return true;
        }
        // If we hit a non-comment, non-empty, non-"p cnf" line, it's not DIMACS
        return false;
    }
    false
}

/// Check if file has .cnf extension
pub(crate) fn has_cnf_extension(path: &str) -> bool {
    path.to_lowercase().ends_with(".cnf")
}

fn should_enable_xor_extension(consumed: usize, remaining: usize, xor_count: usize) -> bool {
    z4_xor::should_enable_gauss_elimination(consumed, remaining, xor_count)
}

fn selected_sat_variant() -> SolverVariant {
    match env::var("Z4_SAT_VARIANT") {
        Ok(value) if value.trim().is_empty() => SolverVariant::Default,
        Ok(value) => match SolverVariant::parse(value.trim()) {
            Some(variant) => variant,
            None => {
                safe_eprintln!(
                    "Error: unknown Z4_SAT_VARIANT '{}'; expected one of: default, aggressive, minimal, probe",
                    value
                );
                std::process::exit(2);
            }
        },
        Err(_) => SolverVariant::Default,
    }
}

pub(crate) fn run_dimacs_from_content(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    let sat_variant = selected_sat_variant();

    // Fast path: large formulas use streaming byte-level parser (no intermediate
    // Vec<Vec<Literal>> allocation). On shuffling-2 (98MB, 4.7M clauses) this
    // reduces parse+load from >15s to ~2s. Skip when proof output is requested
    // since the streaming path doesn't wire proof writers.
    if let Some((_, nc)) = scan_dimacs_header(content) {
        if nc > STREAMING_CLAUSE_THRESHOLD {
            if proof_config.is_some() {
                safe_eprintln!(
                    "c Warning: proof output disables streaming parser for large formula ({nc} clauses). \
                     Parsing may be slower."
                );
            } else {
                run_streaming(content, stats_cfg, sat_variant);
                return;
            }
        }
    }

    match parse_dimacs(content) {
        Ok(formula) => {
            if let Some(proof) = proof_config {
                let num_original_clauses = formula.clauses.len() as u64;
                let file = match File::create(&proof.path) {
                    Ok(file) => file,
                    Err(error) => {
                        safe_eprintln!(
                            "Error: failed to create proof file {}: {error}",
                            proof.path
                        );
                        std::process::exit(1);
                    }
                };
                let writer = BufWriter::new(file);
                let mut variant_config = sat_variant.config(VariantInput::new(
                    formula.num_vars,
                    formula.num_clauses,
                    true,
                    matches!(proof.format, ProofFormat::Lrat),
                ));
                // Feature-driven adaptive adjustments.
                let features =
                    SatFeatures::extract(formula.num_vars, &formula.clauses);
                let class = InstanceClass::classify(&features);
                let _ = adjust_features_for_instance(&features, &class, &mut variant_config.features);

                let output = match (proof.format, proof.binary) {
                    (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
                    (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
                    (ProofFormat::Lrat, false) => {
                        ProofOutput::lrat_text(writer, num_original_clauses)
                    }
                    (ProofFormat::Lrat, true) => {
                        ProofOutput::lrat_binary(writer, num_original_clauses)
                    }
                    (ProofFormat::Alethe, _) => {
                        safe_eprintln!(
                            "Error: proof file '{}' uses Alethe format, but DIMACS SAT supports DRAT/LRAT only",
                            proof.path
                        );
                        std::process::exit(1);
                    }
                };
                let mut solver = SatSolver::with_proof_output(formula.num_vars, output);
                variant_config.apply_to_solver(&mut solver);
                if should_disable_reorder(&features, &class) {
                    solver.set_reorder_enabled(false);
                }
                for clause in formula.clauses {
                    solver.add_clause(clause);
                }
                run_dimacs_solver(&mut solver, stats_cfg);
            } else {
                let (remaining, xor_ext, xor_stats) =
                    z4_xor::preprocess_clauses_with_stats(&formula.clauses);
                let use_xor = xor_ext.as_ref().is_some_and(|_| {
                    should_enable_xor_extension(
                        xor_stats.clauses_consumed,
                        remaining.len(),
                        xor_stats.xors_detected,
                    )
                });

                if use_xor {
                    // Feature-driven adaptive adjustments (computed on original
                    // clauses before XOR preprocessing consumes them).
                    let features =
                        SatFeatures::extract(formula.num_vars, &formula.clauses);
                    let class = InstanceClass::classify(&features);

                    safe_eprintln!(
                        "c XOR: detected {} constraints, {} clauses consumed, {} remaining",
                        xor_stats.xors_detected,
                        xor_stats.clauses_consumed,
                        remaining.len()
                    );

                    let mut solver = SatSolver::new(formula.num_vars);
                    let mut xor_config = sat_variant.config(VariantInput::new(
                        formula.num_vars,
                        formula.num_clauses,
                        false,
                        false,
                    ));
                    let _ = adjust_features_for_instance(&features, &class, &mut xor_config.features);
                    xor_config.apply_to_solver(&mut solver);
                    if should_disable_reorder(&features, &class) {
                        solver.set_reorder_enabled(false);
                    }
                    if let Ok(path) = env::var("Z4_TRACE_FILE") {
                        if !path.trim().is_empty() {
                            solver.enable_tla_trace(&path, SAT_TRACE_MODULE, &SAT_TRACE_VARIABLES);
                        }
                    }
                    for clause in remaining {
                        solver.add_clause(clause);
                    }
                    let mut ext = xor_ext.expect("use_xor implies xor extension is present");
                    // Freeze XOR variables to prevent BVE from eliminating
                    // them, which would cause check() to see unassigned
                    // values and produce wrong SAT on UNSAT instances.
                    {
                        let mut seen = std::collections::HashSet::new();
                        for constraint in ext.constraints() {
                            for &var_id in &constraint.vars {
                                if seen.insert(var_id) {
                                    solver.freeze(Variable::new(var_id));
                                }
                            }
                        }
                    }
                    run_dimacs_solver_with_extension(&mut solver, &mut ext, stats_cfg);
                } else {
                    let mut solver = formula.into_solver_with_variant(sat_variant);
                    // TLA trace only available on non-proof solver.
                    if let Ok(path) = env::var("Z4_TRACE_FILE") {
                        if !path.trim().is_empty() {
                            solver.enable_tla_trace(&path, SAT_TRACE_MODULE, &SAT_TRACE_VARIABLES);
                        }
                    }
                    run_dimacs_solver(&mut solver, stats_cfg);
                }
            }
        }
        Err(e) => {
            safe_eprintln!("c Parse error: {}", e);
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
}

fn run_dimacs_solver(solver: &mut SatSolver, stats_cfg: stats_output::StatsConfig) {
    configure_dimacs_solver(solver);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve(solver, result, stats_cfg);
}

fn run_dimacs_solver_with_extension(
    solver: &mut SatSolver,
    ext: &mut dyn Extension,
    stats_cfg: stats_output::StatsConfig,
) {
    configure_dimacs_solver(solver);
    let result = solver
        .solve_interruptible_with_extension(ext, is_timed_out)
        .into_inner();
    finish_dimacs_solve(solver, result, stats_cfg);
}

fn configure_dimacs_solver(solver: &mut SatSolver) {
    // Wire interrupt flag so the solver checks the watchdog directly (#3638).
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        solver.set_interrupt(handle.clone());
    }
    // Enable periodic progress reporting if --progress was set.
    if super::PROGRESS_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        solver.set_progress_enabled(true);
    }
    // Allow disabling preprocessing for testing (e.g., TLA trace tests
    // that need CDCL conflict-driven behavior).
    if env::var("Z4_NO_PREPROCESS").is_ok() {
        solver.set_preprocess_enabled(false);
    }
    // Bisection flags: disable individual inprocessing techniques for soundness debugging.
    if env::var("Z4_NO_BVE").is_ok() {
        solver.set_bve_enabled(false);
    }
    if env::var("Z4_NO_PROBE").is_ok() {
        solver.set_probe_enabled(false);
    }
    if env::var("Z4_NO_CONGRUENCE").is_ok() {
        solver.set_congruence_enabled(false);
    }
    if env::var("Z4_NO_DECOMPOSE").is_ok() {
        solver.set_decompose_enabled(false);
    }
    if env::var("Z4_NO_SWEEP").is_ok() {
        solver.set_sweep_enabled(false);
    }
    if env::var("Z4_NO_CONDITION").is_ok() {
        solver.set_condition_enabled(false);
    }
    if env::var("Z4_NO_VIVIFY").is_ok() {
        solver.set_vivify_enabled(false);
    }
    if env::var("Z4_NO_SUBSUME").is_ok() {
        solver.set_subsume_enabled(false);
    }
    if env::var("Z4_NO_BCE").is_ok() {
        solver.set_bce_enabled(false);
    }
    if env::var("Z4_NO_TRANSRED").is_ok() {
        solver.set_transred_enabled(false);
    }
    if env::var("Z4_NO_HTR").is_ok() {
        solver.set_htr_enabled(false);
    }
    if env::var("Z4_NO_GATE").is_ok() {
        solver.set_gate_enabled(false);
    }
    if env::var("Z4_NO_FACTOR").is_ok() {
        solver.set_factor_enabled(false);
    }
    if env::var("Z4_NO_SHRINK").is_ok() {
        solver.set_shrink_enabled(false);
    }
    if env::var("Z4_NO_INPROCESS").is_ok() {
        solver.disable_all_inprocessing();
    }
    // TLA trace setup is done in run_dimacs_from_content for the non-proof solver path.
    solver.maybe_enable_diagnostic_trace_from_env();
    solver.maybe_enable_decision_trace_from_env();
    solver.maybe_enable_replay_trace_from_env();
    solver.maybe_load_solution_from_env();
}

fn finish_dimacs_solve(solver: &SatSolver, result: SatResult, stats_cfg: stats_output::StatsConfig) {
    if stats_cfg.any() {
        let props = solver.num_propagations();
        let confs = solver.num_conflicts();
        let decs = solver.num_decisions();
        let restarts = solver.num_restarts();
        let chrono = solver.num_chrono_backtracks();
        let random = solver.num_random_decisions();
        let fixed = solver.num_fixed();
        let orig = solver.num_original_clauses();
        let learned = solver.num_learned_clauses();

        if stats_cfg.human {
            let props_per_conf = if confs > 0 {
                props as f64 / confs as f64
            } else {
                0.0
            };
            let props_per_dec = if decs > 0 {
                props as f64 / decs as f64
            } else {
                0.0
            };
            safe_eprintln!("c");
            safe_eprintln!("c --- Z4 statistics ---");
            safe_eprintln!("c propagations:    {props:>12}");
            safe_eprintln!("c conflicts:       {confs:>12}");
            safe_eprintln!("c decisions:       {decs:>12}");
            safe_eprintln!("c restarts:        {restarts:>12}");
            safe_eprintln!("c chrono_bt:       {chrono:>12}");
            safe_eprintln!("c random_decs:     {random:>12}");
            safe_eprintln!("c fixed_vars:      {fixed:>12}");
            safe_eprintln!("c original_cls:    {orig:>12}");
            safe_eprintln!("c learned_cls:     {learned:>12}");
            safe_eprintln!("c props/conflict:  {props_per_conf:>12.1}");
            safe_eprintln!("c props/decision:  {props_per_dec:>12.1}");
            // Phase timing breakdown
            let preprocess_ns = solver.preprocess_time_ns();
            let search_ns = solver.search_time_ns();
            let lucky_ns = solver.lucky_time_ns();
            let walk_ns = solver.walk_time_ns();
            let search_secs = search_ns as f64 / 1_000_000_000.0;
            let total_ns = preprocess_ns + search_ns + lucky_ns + walk_ns;
            safe_eprintln!("c --- phase timing ---");
            safe_eprintln!("c preprocess_ms:   {:>12}", preprocess_ns / 1_000_000);
            safe_eprintln!("c lucky_ms:        {:>12}", lucky_ns / 1_000_000);
            safe_eprintln!("c walk_ms:         {:>12}", walk_ns / 1_000_000);
            safe_eprintln!("c search_ms:       {:>12}", search_ns / 1_000_000);
            if total_ns > 0 {
                safe_eprintln!(
                    "c preprocess%:     {:>11.1}%",
                    preprocess_ns as f64 / total_ns as f64 * 100.0
                );
                safe_eprintln!(
                    "c search%:         {:>11.1}%",
                    search_ns as f64 / total_ns as f64 * 100.0
                );
                let inproc_ns: u64 = solver
                    .inprocessing_pass_times_ns()
                    .iter()
                    .map(|&(_, v)| v)
                    .sum();
                safe_eprintln!(
                    "c inprocessing%:   {:>11.1}%",
                    inproc_ns as f64 / total_ns as f64 * 100.0
                );
            }
            // Rate metrics (based on search time)
            safe_eprintln!("c --- rates ---");
            if search_secs > 0.0 {
                safe_eprintln!(
                    "c props/sec:       {:>12.0}",
                    props as f64 / search_secs
                );
                safe_eprintln!(
                    "c conflicts/sec:   {:>12.0}",
                    confs as f64 / search_secs
                );
            }
            let decs_per_conf = if confs > 0 {
                decs as f64 / confs as f64
            } else {
                0.0
            };
            safe_eprintln!("c decs/conflict:   {decs_per_conf:>12.2}");
            // Average learned clause LBD
            let (lbd_sum, lbd_count) = solver.lbd_sum_count();
            if lbd_count > 0 {
                safe_eprintln!(
                    "c avg_lbd:         {:>12.2}",
                    lbd_sum as f64 / lbd_count as f64
                );
            }
            let (ema_checks, ema_fires) = solver.focused_ema_stats();
            let reluctant_fires = solver.stable_reluctant_fires();
            let mode_switches = solver.mode_switch_count();
            let ema_blocked = solver.focused_ema_blocked_by_conflict_gate();
            safe_eprintln!("c mode_switches:   {mode_switches:>12}");
            safe_eprintln!("c focused_fires:   {ema_fires:>12}");
            safe_eprintln!("c focused_checks:  {ema_checks:>12}");
            safe_eprintln!("c focused_blocked: {ema_blocked:>12}");
            safe_eprintln!("c reluctant_fires: {reluctant_fires:>12}");
            let bs = solver.bve_stats();
            let gs = solver.gate_stats();
            let ps = solver.probe_stats();
            safe_eprintln!("c --- preprocessing ---");
            safe_eprintln!("c bve_eliminated:  {val:>12}", val = bs.vars_eliminated);
            safe_eprintln!("c bve_cls_removed: {val:>12}", val = bs.clauses_removed);
            safe_eprintln!("c bve_resolvents:  {val:>12}", val = bs.resolvents_added);
            safe_eprintln!("c bve_tautologies: {val:>12}", val = bs.tautologies_skipped);
            safe_eprintln!("c bve_single_otfs: {val:>12}", val = bs.single_otfs);
            safe_eprintln!("c bve_double_otfs: {val:>12}", val = bs.double_otfs);
            safe_eprintln!(
                "c bve_root_pruned: {val:>12}",
                val = bs.root_literals_pruned
            );
            safe_eprintln!(
                "c bve_root_sat:    {val:>12}",
                val = bs.root_satisfied_parents
            );
            safe_eprintln!("c bve_max_res_len: {val:>12}", val = bs.max_resolvent_len);
            safe_eprintln!("c bve_nonunit_res: {val:>12}", val = bs.non_unit_resolvents);
            if bs.non_unit_resolvents > 0 {
                safe_eprintln!(
                    "c bve_avg_res_len: {val:>12.1}",
                    val = bs.total_resolvent_literals as f64 / bs.non_unit_resolvents as f64
                );
            }
            // Net clause count change: positive = formula grew
            let net = bs.resolvents_added as i64 - bs.clauses_removed as i64;
            safe_eprintln!("c bve_net_clauses: {net:>12}");
            safe_eprintln!("c gate_and:        {val:>12}", val = gs.and_gates);
            safe_eprintln!("c gate_xor:        {val:>12}", val = gs.xor_gates);
            safe_eprintln!("c gate_equiv:      {val:>12}", val = gs.equivalences);
            safe_eprintln!("c gate_ite:        {val:>12}", val = gs.ite_gates);
            safe_eprintln!("c probe_failed:    {val:>12}", val = ps.failed);
            let cs = solver.congruence_stats();
            let ss = solver.sweep_stats();
            let ds = solver.decompose_stats();
            let ts = solver.transred_stats();
            let fs = solver.factor_stats();
            safe_eprintln!("c --- simplification ---");
            safe_eprintln!("c cong_rounds:     {val:>12}", val = cs.rounds);
            safe_eprintln!("c cong_gates:      {val:>12}", val = cs.gates_analyzed);
            safe_eprintln!("c cong_equivs:     {val:>12}", val = cs.equivalences_found);
            safe_eprintln!("c cong_lits_rwt:   {val:>12}", val = cs.literals_rewritten);
            safe_eprintln!("c sweep_rounds:    {val:>12}", val = ss.rounds);
            safe_eprintln!("c sweep_lits_rwt:  {val:>12}", val = ss.literals_rewritten);
            safe_eprintln!("c decomp_rounds:   {val:>12}", val = ds.rounds);
            safe_eprintln!("c decomp_subst:    {val:>12}", val = ds.substituted);
            safe_eprintln!("c transred_rounds: {val:>12}", val = ts.rounds);
            safe_eprintln!("c transred_cls_rm: {val:>12}", val = ts.clauses_removed);
            safe_eprintln!("c factor_rounds:   {val:>12}", val = fs.rounds);
            safe_eprintln!("c factor_count:    {val:>12}", val = fs.factored_count);
            let vs = solver.vivify_stats();
            let sbs = solver.subsume_stats();
            safe_eprintln!("c --- inprocessing ---");
            safe_eprintln!("c vivify_examined: {val:>12}", val = vs.clauses_examined);
            safe_eprintln!(
                "c vivify_strength: {val:>12}",
                val = vs.clauses_strengthened
            );
            safe_eprintln!("c vivify_lits_rm:  {val:>12}", val = vs.literals_removed);
            safe_eprintln!("c vivify_sat:      {val:>12}", val = vs.clauses_satisfied);
            safe_eprintln!("c subsumed:        {val:>12}", val = sbs.forward_subsumed);
            safe_eprintln!(
                "c strengthened:    {val:>12}",
                val = sbs.strengthened_clauses
            );
            safe_eprintln!(
                "c strength_lits:   {val:>12}",
                val = sbs.strengthened_literals
            );
            for (label, value) in solver.inprocessing_pass_times_ms() {
                safe_eprintln!("c {label:<16} {value:>12}");
            }
            let flushes = solver.num_flushes();
            let reductions = solver.num_reductions();
            let inprobe_phases = solver.inprobe_phases();
            safe_eprintln!("c --- clause db ---");
            safe_eprintln!("c flushes:         {flushes:>12}");
            safe_eprintln!("c reductions:      {reductions:>12}");
            safe_eprintln!("c inprobe_phases:  {inprobe_phases:>12}");
            safe_eprintln!("c");
        }

        // Canonical envelope (used for both human and JSON output)
        let result_str = match &result {
            SatResult::Sat(_) => "sat",
            SatResult::Unsat => "unsat",
            SatResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        let mut run_stats = stats_output::RunStatistics::new(
            stats_output::SolveMode::DimacsSat,
            result_str,
            global_elapsed(),
        );
        run_stats.insert("conflicts", confs);
        run_stats.insert("decisions", decs);
        run_stats.insert("propagations", props);
        run_stats.insert("restarts", restarts);
        run_stats.insert("sat.chrono_bt", chrono);
        run_stats.insert("sat.random_decisions", random);
        run_stats.insert("sat.fixed_vars", fixed as u64);
        run_stats.insert("sat.original_clauses", orig as u64);
        run_stats.insert("sat.learned_clauses", learned);
        run_stats.insert("sat.preprocess_ms", solver.preprocess_time_ns() / 1_000_000);
        run_stats.insert("sat.search_ms", solver.search_time_ns() / 1_000_000);
        run_stats.insert("sat.lucky_ms", solver.lucky_time_ns() / 1_000_000);
        run_stats.insert("sat.walk_ms", solver.walk_time_ns() / 1_000_000);
        let (lbd_sum_j, lbd_count_j) = solver.lbd_sum_count();
        if lbd_count_j > 0 {
            run_stats.insert("sat.avg_lbd_x100", (lbd_sum_j * 100) / lbd_count_j);
        }
        for (label, value) in solver.inprocessing_pass_times_ms() {
            run_stats.insert(&format!("sat.{label}"), value);
        }
        run_stats.emit(stats_cfg);
    }
    match result {
        SatResult::Sat(model) => {
            safe_println!("s SATISFIABLE");
            // Print model in DIMACS format: v lit1 lit2 ... 0
            // Variables are 1-indexed in DIMACS
            safe_print!("v ");
            for (i, &val) in model.iter().enumerate() {
                let var = (i + 1) as i32;
                let lit = if val { var } else { -var };
                safe_print!("{} ", lit);
            }
            safe_println!("0");
            // SAT Competition exit code 10 = SATISFIABLE.
            // Flush before process::exit which skips destructors (#3088).
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(10);
        }
        SatResult::Unsat => {
            safe_println!("s UNSATISFIABLE");
            // SAT Competition exit code 20 = UNSATISFIABLE.
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(20);
        }
        SatResult::Unknown => {
            // Check timeout before printing -- if timed out, print
            // "timeout" to stderr and exit 124 instead of "s UNKNOWN".
            exit_if_timed_out();
            safe_eprintln!("c reason: incomplete (SAT solver could not determine satisfiability)");
            safe_println!("s UNKNOWN");
            // Exit 0 for unknown (no definitive result)
        }
        #[allow(unreachable_patterns)]
        _ => {
            safe_eprintln!("c reason: unknown");
            safe_println!("s UNKNOWN");
        }
    }
}

// ---------------------------------------------------------------------------
// Streaming DIMACS parser for large formulas
// ---------------------------------------------------------------------------

/// Clause count threshold for streaming parser activation.
const STREAMING_CLAUSE_THRESHOLD: usize = 500_000;

/// Quick header scan to get (num_vars, num_clauses) without full parsing.
fn scan_dimacs_header(content: &str) -> Option<(usize, usize)> {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("p cnf") {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() >= 4 {
                if let (Ok(v), Ok(c)) = (parts[2].parse::<usize>(), parts[3].parse::<usize>()) {
                    return Some((v, c));
                }
            }
        }
        if !trimmed.is_empty() && !trimmed.starts_with('c') && !trimmed.starts_with("p ") {
            break;
        }
    }
    None
}

/// Fast streaming DIMACS parser path for large formulas.
///
/// Parses DIMACS bytes directly into `solver.add_clause()`, skipping all
/// intermediate data structures. On shuffling-2 (98MB, 4.7M clauses),
/// this reduces parse+load from >15s to ~2s.
fn run_streaming(content: &str, stats_cfg: stats_output::StatsConfig, variant: SolverVariant) {
    use z4_sat::Literal;

    let bytes = content.as_bytes();
    let len = bytes.len();
    let mut pos = 0;
    let mut num_vars = 0usize;
    let mut num_clauses_declared = 0usize;
    let mut header_found = false;

    while pos < len && !header_found {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        match bytes[pos] {
            b'c' => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
            b'%' => break,
            b'p' => {
                let line_start = pos;
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
                let line = &bytes[line_start..pos];
                let mut lpos = 0;
                while lpos < line.len() && line[lpos].is_ascii_alphabetic() {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos].is_ascii_alphabetic() {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                let mut val = 0usize;
                while lpos < line.len() && line[lpos].is_ascii_digit() {
                    val = val * 10 + (line[lpos] - b'0') as usize;
                    lpos += 1;
                }
                num_vars = val;
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                let mut val2 = 0usize;
                while lpos < line.len() && line[lpos].is_ascii_digit() {
                    val2 = val2 * 10 + (line[lpos] - b'0') as usize;
                    lpos += 1;
                }
                num_clauses_declared = val2;
                header_found = true;
            }
            _ => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
        }
    }

    if !header_found || num_vars == 0 {
        safe_eprintln!("c Parse error: no valid DIMACS header found, expected \"p cnf <num_vars> <num_clauses>\"");
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }

    let mut solver = SatSolver::new(num_vars);
    let mut streaming_config = variant.config(VariantInput::new(
        num_vars,
        num_clauses_declared,
        false,
        false,
    ));

    // Streaming path: apply header-level adaptive adjustments.
    // Full feature extraction is unavailable (clauses are not buffered),
    // but we can gate on clause/var ratio and variable count.
    let ratio = num_clauses_declared as f64 / num_vars.max(1) as f64;
    if ratio > 100.0 {
        streaming_config.features.condition = false;
    }
    streaming_config.apply_to_solver(&mut solver);
    // Streaming formulas are >500K clauses, almost certainly large/industrial.
    if num_vars > 50_000 {
        solver.set_reorder_enabled(false);
    }

    let mut clause_buf: Vec<Literal> = Vec::with_capacity(32);
    let mut clauses_loaded = 0usize;

    // Counters for adaptive Rules 2 and 4 (computed during streaming parse).
    let mut ternary_count = 0usize;
    let mut horn_count = 0usize;
    let mut positive_in_clause = 0u32;

    while pos < len {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        let ch = bytes[pos];
        if ch == b'%' {
            break;
        }
        if ch == b'c' {
            while pos < len && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if ch.is_ascii_alphabetic() {
            while pos < len && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }

        let negative = ch == b'-';
        if negative {
            pos += 1;
        }
        if pos >= len || !bytes[pos].is_ascii_digit() {
            pos += 1;
            continue;
        }
        let mut val = 0u32;
        while pos < len && bytes[pos].is_ascii_digit() {
            val = val * 10 + u32::from(bytes[pos] - b'0');
            pos += 1;
        }
        if val == 0 {
            // Clause complete: classify before adding to solver.
            if clause_buf.len() == 3 {
                ternary_count += 1;
            }
            if positive_in_clause <= 1 {
                horn_count += 1;
            }
            positive_in_clause = 0;
            solver.add_clause(std::mem::take(&mut clause_buf));
            clauses_loaded += 1;
        } else {
            if !negative {
                positive_in_clause += 1;
            }
            let variable = Variable::new(val - 1);
            let lit = if negative {
                Literal::negative(variable)
            } else {
                Literal::positive(variable)
            };
            clause_buf.push(lit);
        }
    }

    if !clause_buf.is_empty() {
        // Final unterminated clause: classify it too.
        if clause_buf.len() == 3 {
            ternary_count += 1;
        }
        if positive_in_clause <= 1 {
            horn_count += 1;
        }
        solver.add_clause(clause_buf);
        clauses_loaded += 1;
    }

    // Post-parse adaptive adjustment: Rule 2.
    // Supplements the header-level Rules 1 and 3 applied above.
    let total = clauses_loaded.max(1) as f64;
    let frac_ternary = ternary_count as f64 / total;
    let frac_horn = horn_count as f64 / total;
    let clause_var_ratio = clauses_loaded as f64 / num_vars.max(1) as f64;

    // Rule 2: Random 3-SAT has no exploitable symmetry.
    if frac_ternary > 0.8 && clause_var_ratio > 3.5 && frac_horn < 0.5 {
        solver.set_symmetry_enabled(false);
    }

    // Rule 4 removed (#8132): force-enabling BCE caused 4x battleship regression.

    safe_eprintln!("c streaming parse: {clauses_loaded} clauses loaded ({num_vars} vars)");

    configure_dimacs_solver(&mut solver);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve(&solver, result, stats_cfg);
}

#[cfg(test)]
mod tests {
    use super::should_enable_xor_extension;

    #[test]
    fn test_should_enable_xor_extension_zero() {
        // No XOR detected at all.
        assert!(!should_enable_xor_extension(0, 0, 0));
    }

    #[test]
    fn test_should_enable_xor_extension_requires_density_not_just_detection() {
        // A tiny pure-XOR formula still qualifies.
        assert!(should_enable_xor_extension(2, 0, 1));
        // A single accidental XOR in a large formula should stay disabled.
        assert!(!should_enable_xor_extension(2, 9_998, 1));
    }

    #[test]
    fn test_should_enable_xor_extension_pure_xor() {
        // Pure XOR formula, no remaining clauses.
        assert!(should_enable_xor_extension(100, 0, 10));
        assert!(should_enable_xor_extension(8, 0, 4));
    }

    #[test]
    fn test_should_enable_xor_extension_high_density() {
        // High XOR density (80-90%): historically always enabled.
        assert!(should_enable_xor_extension(1732, 307, 100));
        assert!(should_enable_xor_extension(4000, 600, 200));
        // Previously rejected at 84% threshold -- now accepted at 5%.
        assert!(should_enable_xor_extension(7232, 1664, 300));
        assert!(should_enable_xor_extension(4000, 1000, 200));
    }

    #[test]
    fn test_should_enable_xor_extension_crypto_benchmarks() {
        // Large crypto benchmark: 1M clauses, 30% XOR-derived (asconhash-like).
        assert!(should_enable_xor_extension(300_000, 700_000, 5_000));
        // Moderate crypto: 100k clauses, 10% XOR.
        assert!(should_enable_xor_extension(10_000, 90_000, 500));
        // Borderline: exactly at 5% density.
        assert!(should_enable_xor_extension(500, 9_500, 50));
    }

    #[test]
    fn test_should_enable_xor_extension_below_density() {
        // Below 5% density: accidental XOR matches, not worth GE overhead.
        assert!(!should_enable_xor_extension(100, 9_900, 10));
        assert!(!should_enable_xor_extension(40, 9_960, 5));
    }
}
