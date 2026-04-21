// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Memory statistics and efficiency tests.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;
use std::mem::size_of;

fn packed_bool_vec_bytes(capacity: usize) -> usize {
    capacity.div_ceil(8)
}

// ========================================================================
// Memory Benchmark Tests
// ========================================================================

/// Test memory statistics for a small formula
#[test]
fn test_memory_stats_basic() {
    let mut solver = Solver::new(100);

    // Add 200 3-SAT clauses
    for i in 0..200 {
        let v1 = (i * 3) % 100;
        let v2 = (i * 3 + 1) % 100;
        let v3 = (i * 3 + 2) % 100;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();
    assert_eq!(stats.num_vars, 100);
    assert_eq!(stats.num_clauses, 200);
    assert_eq!(stats.total_literals, 600); // 200 clauses * 3 literals

    assert_eq!(stats.solver_shell, size_of::<Solver>());

    // Per-var should be in a reasonable range for the current arena-based core
    // plus the remaining cold inprocessing/proof scaffolding.
    // After #8069 (Phase 2a), unit_proof_id, level0_proof_id, and clause_ids
    // are always allocated (+16 bytes/var for proof IDs, plus clause_ids
    // pre-allocated at 4*num_vars capacity = +32 bytes/var).
    assert!(stats.per_var() > 20.0, "Per-var should be > 20 bytes");
    assert!(stats.per_var() < 300.0, "Per-var should be < 300 bytes");

    // Total should be positive and reasonable
    assert!(stats.total() > 0);
    assert!(stats.total() < 1_000_000, "Small formula should use < 1MB");
}

/// Test memory efficiency - bytes per literal should be reasonable
#[test]
fn test_memory_efficiency_per_literal() {
    let mut solver = Solver::new(1000);

    // Add 4000 3-SAT clauses (12000 literals)
    for i in 0..4000 {
        let v1 = (i * 7) % 1000;
        let v2 = (i * 7 + 3) % 1000;
        let v3 = (i * 7 + 5) % 1000;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();

    // Bytes per literal in the inline clause arena.
    // Ideal payload is 4 bytes per literal, with additional amortized header
    // and capacity slack from the packed arena representation.
    let per_lit = stats.per_literal();
    assert!(
        per_lit >= 4.0,
        "Per literal should be >= 4 bytes, got {per_lit}"
    );
    assert!(
        per_lit < 50.0,
        "Per literal should be < 50 bytes, got {per_lit}"
    );

    // Compare clause_db to theoretical minimum
    // Minimum: num_clauses * (3 lits * 4 bytes) = 4000 * 12 = 48KB
    let min_clause_bytes = 4000 * 3 * 4;
    assert!(
        stats.arena >= min_clause_bytes,
        "Clause DB {} should be >= minimum {}",
        stats.arena,
        min_clause_bytes
    );

    // Should be within 10x of minimum (allowing for Vec overhead)
    assert!(
        stats.arena < min_clause_bytes * 10,
        "Clause DB {} should be < 10x minimum {}",
        stats.arena,
        min_clause_bytes * 10
    );
}

/// Benchmark memory usage after solving (with learned clauses)
#[test]
fn test_memory_after_solving() {
    let mut solver = Solver::new(50);

    // Add a satisfiable random 3-SAT instance
    for i in 0..200 {
        let v1 = (i * 3) % 50;
        let v2 = (i * 3 + 1) % 50;
        let v3 = (i * 3 + 2) % 50;
        solver.add_clause(vec![
            if i % 2 == 0 {
                Literal::positive(Variable(v1 as u32))
            } else {
                Literal::negative(Variable(v1 as u32))
            },
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats_before = solver.memory_stats();

    // Solve
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    let stats_after = solver.memory_stats();

    // After solving, we may have learned clauses
    // Memory should not explode (allow up to 5x growth for learned clauses)
    assert!(
        stats_after.total() < stats_before.total() * 5,
        "Memory should not grow more than 5x after solving"
    );
}

/// Test memory stats display formatting
#[test]
fn test_memory_stats_display() {
    let mut solver = Solver::new(100);
    for i in 0..100 {
        solver.add_clause(vec![Literal::positive(Variable(i as u32))]);
    }

    let stats = solver.memory_stats();
    let display = format!("{stats}");

    // Should contain key information
    assert!(display.contains("Variables: 100"));
    assert!(display.contains("Clauses: 100"));
    assert!(display.contains("Solver shell:"));
    assert!(display.contains("Original clause ledger:"));
    assert!(display.contains("Total:"));
    assert!(display.contains("bytes"));
}

#[test]
fn test_memory_stats_var_data_matches_live_layout() {
    let solver = Solver::new(64);
    let stats = solver.memory_stats();

    let expected = solver.vals.capacity() * size_of::<i8>()
        + solver.var_data.capacity() * size_of::<VarData>()
        + solver.phase.capacity() * size_of::<i8>()
        + solver.target_phase.capacity() * size_of::<i8>()
        + solver.best_phase.capacity() * size_of::<i8>();

    assert_eq!(
        stats.var_data, expected,
        "memory_stats var_data must match the live VarData + phase-array layout"
    );
}

#[test]
fn test_memory_stats_conflict_counts_minimization_buffers() {
    let solver = Solver::new(32);
    let stats = solver.memory_stats();

    let minimize_bytes = solver.min.minimize_flags.capacity() * size_of::<u8>()
        + solver.min.minimize_to_clear.capacity() * size_of::<usize>()
        + solver.min.level_seen_count.capacity() * size_of::<u32>()
        + solver.min.level_seen_trail.capacity() * size_of::<usize>()
        + solver.min.level_seen_to_clear.capacity() * size_of::<u32>()
        + solver.min.lrat_to_clear.capacity() * size_of::<usize>()
        + solver.min.minimize_level_count.capacity() * size_of::<u32>()
        + solver.min.minimize_level_trail.capacity() * size_of::<usize>()
        + solver.min.minimize_levels_to_clear.capacity() * size_of::<u32>();

    assert!(
        stats.conflict >= minimize_bytes,
        "conflict bucket must include the minimization arrays"
    );
}

#[test]
fn test_memory_stats_watches_use_outer_capacity_after_var_growth() {
    let mut solver = Solver::new(0);
    while solver.watches.outer_capacity() == solver.num_vars * 2 {
        solver.new_var();
        if solver.num_vars >= 64 {
            break;
        }
    }

    assert!(
        solver.watches.outer_capacity() > solver.num_vars * 2,
        "expected incremental growth to leave spare capacity in the outer watch table"
    );

    let stats = solver.memory_stats();
    let expected = solver.watches.heap_bytes()
        + solver.deferred_watch_list.capacity() * size_of::<u64>()
        + solver.deferred_replacement_watches.capacity() * size_of::<(Literal, Watcher)>();

    assert_eq!(
        stats.watches, expected,
        "memory_stats watches must use the live outer watch-table capacity, not just num_vars * 2"
    );
}

#[test]
fn test_memory_stats_support_counts_mapping_and_walk_buffers() {
    let mut solver = Solver::new(8);
    solver.ensure_num_vars(17);

    let stats = solver.memory_stats();
    let expected = solver.cold.e2i.capacity() * size_of::<u32>()
        + solver.cold.i2e.capacity() * size_of::<u32>()
        + solver.var_lifecycle.heap_bytes()
        + packed_bool_vec_bytes(solver.phase_init.walk_prev_phase.capacity())
        + solver
            .cold
            .solution_witness
            .as_ref()
            .map_or(0, |witness| witness.capacity() * size_of::<Option<bool>>());

    assert_eq!(
        stats.support, expected,
        "memory_stats support bucket must match live mapping/lifecycle/walk buffers"
    );
}

#[test]
fn test_memory_stats_original_ledger_matches_live_layout() {
    let mut solver = Solver::new(16);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
        Literal::negative(Variable(5)),
    ]);
    solver.add_clause(vec![Literal::positive(Variable(6))]);

    let stats = solver.memory_stats();
    let expected = solver.cold.original_ledger.heap_bytes();

    assert_eq!(
        stats.original_ledger, expected,
        "memory_stats must include the immutable original-clause ledger kept beside the arena"
    );
}

// ========================================================================
// Progress Reporting Tests
// ========================================================================

/// Test that `format_progress_line` produces the expected DIMACS comment format.
#[test]
fn test_format_progress_line_dimacs_format() {
    let solver = Solver::new(10);
    let line = solver.format_progress_line(5.0);
    assert!(line.starts_with("c ["), "Progress line must start with 'c [', got: {line}");
    assert!(line.contains("conflicts="), "Progress line must contain conflicts=");
    assert!(line.contains("decisions="), "Progress line must contain decisions=");
    assert!(line.contains("props="), "Progress line must contain props=");
    assert!(line.contains("restarts="), "Progress line must contain restarts=");
    assert!(line.contains("learned="), "Progress line must contain learned=");
    assert!(line.contains("mode="), "Progress line must contain mode=");
}

/// Test that `format_progress_line` reflects actual solver counters after solving.
#[test]
fn test_format_progress_line_reflects_counters() {
    let mut solver = Solver::new(50);
    // Add a satisfiable random 3-SAT instance that requires some search.
    for i in 0..200 {
        let v1 = (i * 3) % 50;
        let v2 = (i * 3 + 1) % 50;
        let v3 = (i * 3 + 2) % 50;
        solver.add_clause(vec![
            if i % 2 == 0 {
                Literal::positive(Variable(v1 as u32))
            } else {
                Literal::negative(Variable(v1 as u32))
            },
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }
    let _ = solver.solve();
    let line = solver.format_progress_line(1.0);
    // After solving, at least some propagations and decisions must have occurred.
    assert!(line.contains("props="), "progress line after solve must contain props=");
    // The line should reflect non-zero counters.
    assert!(!line.contains("props=0 "), "after solving, propagation count should be > 0");
}

/// Test that `set_progress_enabled` toggles the flag and `maybe_emit_progress` is safe to call.
#[test]
fn test_set_progress_enabled_toggle() {
    let mut solver = Solver::new(10);
    // Default: disabled.
    solver.maybe_emit_progress();
    // Enable.
    solver.set_progress_enabled(true);
    // Call without a solve start time — should not panic.
    solver.maybe_emit_progress();
}

/// Memory benchmark comparing to theoretical CaDiCaL efficiency
///
/// CaDiCaL uses ~8 bytes per literal (compact arena allocation).
/// Z4 uses an inline clause arena, so the dominant remaining overhead is
/// original-clause storage plus solver-side per-variable state and cold
/// inprocessing scaffolding.
///
/// Optimization opportunities to reach 1.5x target:
/// 1. Finish `#5090` hot/cold separation for proof/incremental state
/// 2. Lazy initialization of inprocessing engines
/// 3. Compact clause headers (pack lbd, learned, used into single u32)
/// 4. Use SmallVec for short clauses where arena access is not required
#[test]
fn test_memory_vs_cadical_efficiency() {
    let num_vars = 10_000;
    let num_clauses = 40_000; // 4:1 clause-to-var ratio typical for 3-SAT

    let mut solver = Solver::new(num_vars);

    // Add random 3-SAT clauses
    for i in 0..num_clauses {
        let v1 = (i * 7) % num_vars;
        let v2 = (i * 7 + 3) % num_vars;
        let v3 = (i * 7 + 5) % num_vars;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();

    // CaDiCaL baseline (estimated):
    // - Per variable: ~80 bytes (activities, levels, reasons, etc.)
    // - Per literal: ~8 bytes (arena-allocated with compact headers)
    // - Watches: ~4 bytes per watch entry
    let cadical_per_var = 80;
    let cadical_per_lit = 8;
    let cadical_estimate = num_vars * cadical_per_var + stats.total_literals * cadical_per_lit;

    // Z4 should be within 1.5x of CaDiCaL estimate (per Priority 2.1 requirement)
    let ratio = stats.total() as f64 / cadical_estimate as f64;

    // Print results for visibility in test output
    safe_eprintln!("Memory Benchmark Results:");
    safe_eprintln!("  Variables: {}", num_vars);
    safe_eprintln!("  Clauses: {}", num_clauses);
    safe_eprintln!("  Literals: {}", stats.total_literals);
    safe_eprintln!();
    safe_eprintln!("Breakdown:");
    safe_eprintln!(
        "  solver_shell: {} bytes ({:.1}%)",
        stats.solver_shell,
        100.0 * stats.solver_shell as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  var_data: {} bytes ({:.1}%)",
        stats.var_data,
        100.0 * stats.var_data as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  vsids: {} bytes ({:.1}%)",
        stats.vsids,
        100.0 * stats.vsids as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  conflict: {} bytes ({:.1}%)",
        stats.conflict,
        100.0 * stats.conflict as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  arena: {} bytes ({:.1}%)",
        stats.arena,
        100.0 * stats.arena as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  watches: {} bytes ({:.1}%)",
        stats.watches,
        100.0 * stats.watches as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  trail: {} bytes ({:.1}%)",
        stats.trail,
        100.0 * stats.trail as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  support: {} bytes ({:.1}%)",
        stats.support,
        100.0 * stats.support as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  clause_ids: {} bytes ({:.1}%)",
        stats.clause_ids,
        100.0 * stats.clause_ids as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  original_ledger: {} bytes ({:.1}%)",
        stats.original_ledger,
        100.0 * stats.original_ledger as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  inprocessing: {} bytes ({:.1}%)",
        stats.inprocessing,
        100.0 * stats.inprocessing as f64 / stats.total() as f64
    );
    safe_eprintln!();
    safe_eprintln!(
        "  Z4 total: {} bytes ({:.2} MB)",
        stats.total(),
        stats.total() as f64 / 1_048_576.0
    );
    safe_eprintln!(
        "  CaDiCaL estimate: {} bytes ({:.2} MB)",
        cadical_estimate,
        cadical_estimate as f64 / 1_048_576.0
    );
    safe_eprintln!("  Ratio (Z4/CaDiCaL): {:.2}x", ratio);
    safe_eprintln!();
    safe_eprintln!("  Z4 per variable: {:.2} bytes", stats.per_var());
    safe_eprintln!("  Z4 per literal: {:.2} bytes", stats.per_literal());

    // Requirement: within 1.5x of CaDiCaL (Priority 2.1)
    // Current baseline is ~3.4x, target is 1.5x
    // For now, assert we're under 4x to track regressions
    assert!(
        ratio < 4.0,
        "Z4 memory ({} bytes) should be within 4x of CaDiCaL estimate ({} bytes), ratio: {:.2}x",
        stats.total(),
        cadical_estimate,
        ratio
    );
}
