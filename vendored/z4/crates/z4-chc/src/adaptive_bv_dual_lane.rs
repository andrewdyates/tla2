// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quad-lane BV solving: race BvToBool, BvToInt, BV-native PDR, and relaxed
//! BvToInt in parallel.
//!
//! Companion to `adaptive_bv_strategy.rs`: contains the `solve_bv_dual_lane`
//! method which spawns up to 4 threads for the parallel BV solving architecture.

use crate::kind::{KindConfig, KindResult, KindSolver};
use crate::pdr::{PdrConfig, PdrSolver};
use crate::portfolio::{PortfolioResult, PortfolioSolver, PreprocessSummary};
use crate::ChcSort;
use std::time::{Duration, Instant};
use z4_sat::TlaTraceable;

use crate::adaptive::{AdaptivePortfolio, ADAPTIVE_SOLVER_STACK_SIZE};

impl AdaptivePortfolio {
    /// Quad-lane BV solving: race BvToBool, BvToInt, BV-native PDR, and relaxed
    /// BvToInt in parallel.
    ///
    /// Lane A (BvToBool): Bit-blasts BV(<=64) to individual Bool args (#7975). Good
    /// for UNSAT instances needing bit-level invariants. Runs PDKIND + PDR + BMC.
    ///
    /// Lane B (BvToInt): Converts BV to exact integer arithmetic. Good for
    /// arithmetic invariants while preserving BV overflow semantics. Runs
    /// relaxed KIND (Phase 1), exact KIND (Phase 2), then full portfolio (Phase 3).
    ///
    /// Lane C (BV-native): Runs PDR + BMC on the original BV problem with no BV
    /// transforms. Matches Z3 Spacer's default behavior (xform.bit_blast = false).
    /// Good for SAT-finding (backward reachability) where the BvToBool state-space
    /// explosion is harmful. PDR operates on ~5-10 BV variables instead of 160+
    /// Bool variables (#5877 Wave 3).
    ///
    /// Lane D (Relaxed BvToInt): Only for BV64+ problems (#4198). Maps BV
    /// arithmetic to unbounded integers (no mod/div wrapping), producing much
    /// simpler LIA constraints. Safe results validated against original BV problem.
    /// Runs independently of Lane B's Phase 1 with a longer budget and deeper k.
    ///
    /// All lanes run in separate threads with the full budget. First definitive
    /// result (Safe/Unsafe) wins.
    pub(super) fn solve_bv_dual_lane(&self, budget: Duration) -> PortfolioResult {
        use std::sync::mpsc;

        let problem = self.problem.clone();
        let verbose = self.config.verbose;

        // Lane A: BvToBool → Boolean portfolio (existing path)
        //
        // #5877: BvToBool expands each BV(w) state variable to w Bool variables.
        // For problems with many BV32 variables (e.g., bist_cell: 37 × 32 = 1184),
        // the expansion produces an intractable problem that hangs BvToBoolBitBlaster
        // indefinitely (no cancellation check inside the transform). The thread
        // consumes GBs of memory and prevents process exit even after the timeout.
        // Skip Lane A when the expanded state would exceed 200 Bool variables.
        let bv_bit_groups = crate::adaptive_validation::compute_bv_bit_groups(&problem);
        // #7006/#7019/#7975: BvToBool now selectively bit-blasts BV args with
        // width <= 64, leaving BV128+ as-is for BvToInt. The expanded count
        // only includes args that will actually be expanded.
        let expanded_bool_count: usize = self
            .problem
            .predicates()
            .iter()
            .map(|p| {
                p.arg_sorts
                    .iter()
                    .map(|s| match s {
                        ChcSort::BitVec(w) if *w <= 64 => *w as usize,
                        ChcSort::BitVec(_) => 1, // BV128+ not expanded
                        ChcSort::Array(_, v) => match v.as_ref() {
                            ChcSort::BitVec(w) if *w <= 64 => *w as usize,
                            _ => 1,
                        },
                        _ => 1,
                    })
                    .sum::<usize>()
            })
            .max()
            .unwrap_or(0);
        let skip_lane_a = expanded_bool_count > 200;
        if skip_lane_a && verbose {
            safe_eprintln!(
                "Adaptive: Skipping BvToBool lane (expanded state would be {} Bool vars, threshold 200)",
                expanded_bool_count
            );
        }
        let problem_a = if skip_lane_a {
            None
        } else {
            Some(problem.clone())
        };
        let bool_config = self.boolean_simple_loop_portfolio_config(budget, &bv_bit_groups);

        // Lane B: BvToInt-only → LIA portfolio (exact integer encoding)
        let problem_b = problem.clone();
        let mut int_config = self.simple_loop_portfolio_config(budget);
        int_config.enable_preprocessing = false; // We preprocess manually via build_int_only

        // Lane C: BV-native → PDR + BMC on original BV problem (#5877 Wave 3)
        // No BV transforms — PDR operates on BV-sorted predicates directly,
        // delegating BV satisfiability to the SMT solver's BV theory.
        let problem_c = problem.clone();
        let bv_native_config = self.bv_native_portfolio_config(budget);

        // Lane D: Relaxed BvToInt + KIND + validation (#4198).
        // Maps BV arithmetic to unbounded integers (no mod/div wrapping).
        // Produces much simpler LIA constraints for BV64 problems.
        // Safe results validated against original BV problem for soundness.
        let has_bv64 = problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::BitVec(w) if *w > 32))
        });
        let skip_lane_d = !has_bv64;
        let problem_d = if has_bv64 { Some(problem) } else { None };

        let (tx, rx) = mpsc::channel();
        let tx_a = tx.clone();
        let tx_b = tx.clone();
        let tx_c = tx.clone();
        let tx_d = tx;

        // Spawn Lane A: BvToBool + Boolean portfolio (skip if expanded state too large)
        let handle_a = if let Some(problem_a) = problem_a {
            std::thread::Builder::new()
                .name("bv-bool-lane".to_string())
                .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn(move || {
                    let summary = PreprocessSummary::build(problem_a, verbose);
                    let result = PortfolioSolver::from_summary(summary, bool_config).solve();
                    let _ = tx_a.send(("BvToBool", result));
                })
        } else {
            // Lane A skipped — send Unknown immediately so the recv loop counts it
            let _ = tx_a.send(("BvToBool", PortfolioResult::Unknown));
            Err(std::io::Error::other("Lane A skipped"))
        };

        // Spawn Lane B: BvToInt + LIA portfolio
        //
        // Phase 1: Try RELAXED BvToInt + KIND. Relaxed mode maps BV arithmetic
        // to unbounded integers (no mod/div), producing simpler LIA problems
        // that are tractable even for BV64. If KIND finds a Safe invariant,
        // validate it on the ORIGINAL BV problem — the validation step catches
        // cases where overflow semantics matter (#6848, #4198).
        //
        // Phase 2: If relaxed fails, fall through to EXACT BvToInt + KIND.
        //
        // Phase 3: Full portfolio on exact BvToInt problem.
        let handle_b = std::thread::Builder::new()
            .name("bv-int-lane".to_string())
            .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
            .spawn(move || {
                let lane_start = Instant::now();

                // Phase 1: Relaxed BvToInt + KIND (fast path for BV64, #4198)
                let relaxed_budget = budget.min(Duration::from_secs(5));
                let relaxed_summary =
                    PreprocessSummary::build_int_relaxed(problem_b.clone(), verbose);
                let kind_config_relaxed = KindConfig::with_engine_config(
                    5,
                    Duration::from_secs(2),
                    relaxed_budget,
                    verbose,
                    None,
                );
                if verbose {
                    safe_eprintln!(
                        "Adaptive: BV Lane B Phase 1 — relaxed BvToInt + KIND ({} preds, {} clauses)",
                        relaxed_summary.transformed_problem.predicates().len(),
                        relaxed_summary.transformed_problem.clauses().len(),
                    );
                }
                let mut kind_solver_relaxed =
                    KindSolver::new(relaxed_summary.transformed_problem.clone(), kind_config_relaxed);
                kind_solver_relaxed.maybe_enable_tla_trace_from_env();
                let relaxed_result = kind_solver_relaxed.solve();

                if verbose {
                    safe_eprintln!(
                        "Adaptive: BV Lane B Phase 1 relaxed KIND: {} ({:?})",
                        match &relaxed_result {
                            KindResult::Safe(_) => "Safe",
                            KindResult::Unsafe(_) => "Unsafe",
                            KindResult::Unknown => "Unknown",
                            KindResult::NotApplicable => "NotApplicable",
                        },
                        lane_start.elapsed()
                    );
                }

                if let KindResult::Safe(model) = relaxed_result {
                    let translated = relaxed_summary.back_translator.translate_validity(model);
                    let config = PdrConfig {
                        verbose,
                        ..PdrConfig::default()
                    };
                    let mut verifier =
                        PdrSolver::new(relaxed_summary.original_problem.clone(), config);
                    if verifier.verify_model_per_rule(&translated, Duration::from_secs(3)) {
                        if verbose {
                            safe_eprintln!(
                                "Adaptive: BV Lane B Phase 1 — relaxed invariant VALIDATED ({:?})",
                                lane_start.elapsed()
                            );
                        }
                        let _ = tx_b.send(("BvToInt-relaxed", PortfolioResult::Safe(translated)));
                        return;
                    }
                    if verbose {
                        safe_eprintln!(
                            "Adaptive: BV Lane B Phase 1 — relaxed invariant failed BV validation"
                        );
                    }
                }

                let elapsed = lane_start.elapsed();
                if elapsed >= budget {
                    let _ = tx_b.send(("BvToInt", PortfolioResult::Unknown));
                    return;
                }

                // Phase 2: Exact BvToInt + KIND
                let summary = PreprocessSummary::build_int_only(problem_b, verbose);
                let remaining = budget.saturating_sub(elapsed);
                let kind_budget = remaining.min(Duration::from_secs(2));
                let kind_config = KindConfig::with_engine_config(
                    3,
                    kind_budget.min(Duration::from_secs(1)),
                    kind_budget,
                    verbose,
                    None,
                );
                if verbose {
                    safe_eprintln!(
                        "Adaptive: BV Lane B Phase 2 — exact BvToInt + KIND ({} preds, {} clauses, has_bv={})",
                        summary.transformed_problem.predicates().len(),
                        summary.transformed_problem.clauses().len(),
                        summary.transformed_problem.has_bv_sorts(),
                    );
                }
                let mut kind_solver =
                    KindSolver::new(summary.transformed_problem.clone(), kind_config);
                kind_solver.maybe_enable_tla_trace_from_env();
                let kind_result = kind_solver.solve();

                if verbose {
                    safe_eprintln!(
                        "Adaptive: BV Lane B Phase 2 exact KIND: {}",
                        match &kind_result {
                            KindResult::Safe(_) => "Safe".to_string(),
                            KindResult::Unsafe(_) => "Unsafe".to_string(),
                            KindResult::Unknown => "Unknown".to_string(),
                            KindResult::NotApplicable => "NotApplicable".to_string(),
                        }
                    );
                }

                if let KindResult::Safe(model) = kind_result {
                    let translated = summary.back_translator.translate_validity(model);
                    let config = PdrConfig {
                        verbose,
                        ..PdrConfig::default()
                    };
                    let mut verifier = PdrSolver::new(summary.original_problem.clone(), config);
                    if verifier.verify_model_per_rule(&translated, Duration::from_secs(2)) {
                        let _ = tx_b.send(("BvToInt", PortfolioResult::Safe(translated)));
                        return;
                    }
                    if verbose {
                        safe_eprintln!(
                            "Adaptive: BV Lane B Phase 2 — exact invariant failed validation"
                        );
                    }
                }

                // Phase 3: Full portfolio on exact BvToInt problem.
                let result = PortfolioSolver::from_summary(summary, int_config).solve();
                let _ = tx_b.send(("BvToInt", result));
            });

        // Spawn Lane C: BV-native PDR + BMC (no BV transforms)
        let handle_c = std::thread::Builder::new()
            .name("bv-native-lane".to_string())
            .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
            .spawn(move || {
                if verbose {
                    safe_eprintln!("Adaptive: BV-native lane (Lane C) thread started");
                }
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let _t_preproc = Instant::now();
                    let summary = PreprocessSummary::build_bv_native(problem_c, verbose);
                    if verbose {
                        safe_eprintln!(
                            "Adaptive: BV-native preprocessing took {:?}",
                            _t_preproc.elapsed()
                        );
                    }
                    PortfolioSolver::from_summary(summary, bv_native_config).solve()
                }));
                let result = match result {
                    Ok(r) => r,
                    Err(payload) => {
                        let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                            s.to_string()
                        } else if let Some(s) = payload.downcast_ref::<String>() {
                            s.clone()
                        } else {
                            "unknown panic".to_string()
                        };
                        safe_eprintln!("Adaptive: BV-native lane (Lane C) panicked: {}", msg);
                        PortfolioResult::Unknown
                    }
                };
                let _ = tx_c.send(("BvNative", result));
            });

        // Spawn Lane D: Relaxed BvToInt + KIND (dedicated BV64 lane, #4198)
        // Runs independently of Lane B's Phase 1 with a longer budget and deeper k.
        // Only for problems with BV64+ arguments where exact BvToInt is intractable.
        let handle_d = if let Some(problem_d) = problem_d {
            std::thread::Builder::new()
                .name("bv-relaxed-lane".to_string())
                .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn(move || {
                    let lane_start = Instant::now();
                    let relaxed_budget = budget.min(Duration::from_secs(15));
                    let summary = PreprocessSummary::build_int_relaxed(problem_d, verbose);
                    if verbose {
                        safe_eprintln!(
                            "Adaptive: BV Lane D — relaxed BvToInt + KIND ({} preds, {} clauses)",
                            summary.transformed_problem.predicates().len(),
                            summary.transformed_problem.clauses().len(),
                        );
                    }
                    let kind_config = KindConfig::with_engine_config(
                        10,
                        Duration::from_secs(3),
                        relaxed_budget,
                        verbose,
                        None,
                    );
                    let mut kind_solver =
                        KindSolver::new(summary.transformed_problem.clone(), kind_config);
                    kind_solver.maybe_enable_tla_trace_from_env();
                    let kind_result = kind_solver.solve();

                    if verbose {
                        safe_eprintln!(
                            "Adaptive: BV Lane D relaxed KIND: {} ({:?})",
                            match &kind_result {
                                KindResult::Safe(_) => "Safe",
                                KindResult::Unsafe(_) => "Unsafe",
                                KindResult::Unknown => "Unknown",
                                KindResult::NotApplicable => "NotApplicable",
                            },
                            lane_start.elapsed()
                        );
                    }

                    if let KindResult::Safe(model) = kind_result {
                        let translated = summary.back_translator.translate_validity(model);
                        let config = PdrConfig {
                            verbose,
                            ..PdrConfig::default()
                        };
                        let mut verifier = PdrSolver::new(summary.original_problem.clone(), config);
                        if verifier.verify_model_per_rule(&translated, Duration::from_secs(5)) {
                            if verbose {
                                safe_eprintln!(
                                    "Adaptive: BV Lane D — relaxed invariant VALIDATED ({:?})",
                                    lane_start.elapsed()
                                );
                            }
                            let _ = tx_d.send(("BvRelaxed", PortfolioResult::Safe(translated)));
                            return;
                        }
                        if verbose {
                            safe_eprintln!(
                                "Adaptive: BV Lane D — relaxed invariant failed BV validation"
                            );
                        }
                    }

                    let _ = tx_d.send(("BvRelaxed", PortfolioResult::Unknown));
                })
        } else {
            let _ = tx_d.send(("BvRelaxed", PortfolioResult::Unknown));
            Err(std::io::Error::other("Lane D skipped"))
        };

        let lane_a_status = if skip_lane_a {
            "skipped"
        } else if handle_a.is_ok() {
            "ok"
        } else {
            "FAILED"
        };
        let lane_d_status = if skip_lane_d {
            "skipped"
        } else if handle_d.is_ok() {
            "ok"
        } else {
            "FAILED"
        };
        let spawned = [&handle_b, &handle_c].iter().filter(|h| h.is_ok()).count()
            + if handle_a.is_ok() { 1 } else { 0 }
            + if handle_d.is_ok() { 1 } else { 0 };
        // expected includes skip-Lane-A and skip-Lane-D Unknown messages on the channel
        let expected_messages =
            spawned + if skip_lane_a { 1 } else { 0 } + if skip_lane_d { 1 } else { 0 };
        if verbose {
            safe_eprintln!(
                "Adaptive: BV quad-lane spawned {}/4 threads (A={}, B={}, C={}, D={})",
                spawned,
                lane_a_status,
                if handle_b.is_ok() { "ok" } else { "FAILED" },
                if handle_c.is_ok() { "ok" } else { "FAILED" },
                lane_d_status,
            );
        }
        if spawned == 0 {
            return PortfolioResult::Unknown;
        }

        // Collect results: first definitive answer wins
        let deadline = Instant::now() + budget;
        let mut best = PortfolioResult::Unknown;
        let mut received = 0u32;
        let expected = expected_messages as u32;

        while received < expected {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                break;
            }
            match rx.recv_timeout(remaining) {
                Ok((lane_name, result)) => {
                    received += 1;
                    match &result {
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => {
                            if verbose {
                                safe_eprintln!(
                                    "Adaptive: BV quad-lane — {} lane produced definitive result",
                                    lane_name
                                );
                            }
                            best = result;
                            break; // First definitive result wins
                        }
                        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
                            if verbose {
                                safe_eprintln!(
                                    "Adaptive: BV quad-lane — {} lane returned Unknown",
                                    lane_name
                                );
                            }
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => break,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        }

        // Join remaining threads to reclaim their 128 MiB stacks + solver state.
        // Each lane's portfolio has its own `parallel_timeout` budget enforcement,
        // so they should finish within ~budget. Use a short grace period after
        // the deadline to avoid blocking indefinitely on a stuck thread.
        let join_deadline = Instant::now() + Duration::from_secs(2);
        for h in [handle_a, handle_b, handle_c, handle_d]
            .into_iter()
            .flatten()
        {
            let remaining = join_deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                drop(h); // Detach — thread will clean up on its own timeout
            } else {
                let _ = h.join();
            }
        }

        best
    }
}
