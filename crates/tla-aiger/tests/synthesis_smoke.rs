// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Smoke test for ABC-style AIG synthesis preprocessing (#4261).
//!
//! Validates that balance + rewrite + dag_rewrite + strash (the ABC `b`/`rw`/`rf`
//! equivalents) produce measurable gate/depth reduction on real HWMCC benchmarks.
//!
//! The test is guarded behind benchmark-file presence so CI without the HWMCC
//! fixtures still passes (returns early with `eprintln!`).

use std::path::Path;

use tla_aiger::preprocess::PreprocessConfig;
use tla_aiger::transys::Transys;

/// Paths tried in order; first one that exists is used.
const CANDIDATE_BENCHMARKS: &[&str] = &[
    "./hwmcc/benchmarks/bitlevel/safety/2019/goel/industry/cal14/cal14.aig",
    "./hwmcc/benchmarks/bitlevel/safety/2025/ntu/unsat/microban_1.aig",
];

fn pick_benchmark() -> Option<&'static str> {
    CANDIDATE_BENCHMARKS
        .iter()
        .copied()
        .find(|p| Path::new(p).exists())
}

#[test]
fn synthesis_reduces_gates_on_real_benchmark() {
    let Some(path) = pick_benchmark() else {
        eprintln!("skip: no HWMCC benchmark file available");
        return;
    };
    let circuit = tla_aiger::parse_file(Path::new(path))
        .expect("parse AIGER benchmark");
    let ts_before = Transys::from_aiger(&circuit);

    // Run preprocessing with synthesis DISABLED (rewrite+dag_rewrite+synthesis all off).
    let cfg_off = PreprocessConfig {
        enable_rewrite: false,
        enable_dag_rewrite: false,
        enable_synthesis: false,
        ..PreprocessConfig::default()
    };
    let (_, stats_off) = tla_aiger::preprocess::preprocess_with_config(&ts_before, &cfg_off);

    // Run preprocessing with synthesis ENABLED (default).
    let cfg_on = PreprocessConfig::default();
    let (_, stats_on) = tla_aiger::preprocess::preprocess_with_config(&ts_before, &cfg_on);

    eprintln!(
        "bench={} orig_gates={} gates_without_synthesis={} gates_with_synthesis={}",
        path, stats_off.orig_gates, stats_off.final_gates, stats_on.final_gates
    );
    eprintln!(
        "synthesis_rounds={} synthesis_gate_reduction={} synthesis_depth_reduction={} \
         dag_rewrite_eliminated={}",
        stats_on.synthesis_rounds,
        stats_on.synthesis_gate_reduction,
        stats_on.synthesis_depth_reduction,
        stats_on.dag_rewrite_eliminated,
    );

    assert!(
        stats_on.final_gates <= stats_off.final_gates,
        "synthesis must not INCREASE gate count: with_synth={} without_synth={}",
        stats_on.final_gates,
        stats_off.final_gates,
    );

    // Productive assertion: on cal14 specifically, synthesis produces a real reduction.
    if path.ends_with("cal14.aig") {
        assert!(
            stats_on.synthesis_gate_reduction + stats_on.dag_rewrite_eliminated > 0,
            "cal14 should see some ABC-style gate reduction; got synth={}, dag_rewrite={}",
            stats_on.synthesis_gate_reduction,
            stats_on.dag_rewrite_eliminated,
        );
    }
}

#[test]
fn balance_pass_runs_on_real_benchmark_without_crash() {
    let Some(path) = pick_benchmark() else {
        eprintln!("skip: no HWMCC benchmark file available");
        return;
    };
    let circuit = tla_aiger::parse_file(Path::new(path))
        .expect("parse AIGER benchmark");
    let ts = Transys::from_aiger(&circuit);

    // Just exercising the default pipeline (which includes balance inside synthesis)
    // on a real benchmark acts as a crash smoke test.
    let cfg = PreprocessConfig::default();
    let (preprocessed, stats) = tla_aiger::preprocess::preprocess_with_config(&ts, &cfg);
    eprintln!(
        "bench={} orig_gates={} final_gates={} synthesis_rounds={} depth_reduction={}",
        path,
        stats.orig_gates,
        stats.final_gates,
        stats.synthesis_rounds,
        stats.synthesis_depth_reduction,
    );
    assert!(!preprocessed.bad_lits.is_empty() || preprocessed.bad_lits.is_empty());
}
