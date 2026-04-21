// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::process::Command;

fn run_z4_hwbench(file_name: &str) -> String {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let benchmark_path = format!(
        "{}/../../benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/{file_name}",
        env!("CARGO_MANIFEST_DIR")
    );

    let output = Command::new(z4_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn z4");

    assert!(
        output.status.success(),
        "z4 exited with {:?} for {}\nstderr: {}",
        output.status,
        file_name,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout)
        .trim()
        .lines()
        .next()
        .unwrap_or("")
        .to_string()
}

/// #4610 regression: these UNSAT hwbench cases must never return SAT.
#[test]
#[timeout(60_000)]
fn test_hwbench_unsat_instances_never_return_sat() {
    const CASES: &[&str] = &[
        "QF_UF_cache_coherence_three_ab_reg_max.smt2",
        "QF_UF_h_Arbiter_ab_reg_max.smt2",
        "QF_UF_h_BufAl_ab_fp_max.smt2",
        "QF_UF_h_Rrobin_ab_cti_max.smt2",
        "QF_UF_h_TicTacToe_ab_reg_max.smt2",
        "QF_UF_h_Vlunc_ab_cti_max.smt2",
        "QF_UF_h_b04_ab_cti_max.smt2",
        "QF_UF_h_b04_ab_reg_max.smt2",
        "QF_UF_itc99_b13_ab_cti_max.smt2",
    ];

    for case in CASES {
        let result = run_z4_hwbench(case);
        // Keep the broad guard at "not sat": one current hwbench case still
        // returns `unknown`, while #6869's exact cache_coherence benchmark gets
        // a stricter exact-UNSAT assertion below.
        assert!(
            matches!(result.as_str(), "unsat" | "unknown"),
            "{case} should not return sat (expected unsat/unknown), got: {result}"
        );
    }
}

/// #6869 regression: the original cache_coherence benchmark must return UNSAT,
/// not merely avoid the wrong-answer `sat`.
#[test]
#[timeout(60_000)]
fn test_cache_coherence_three_ab_reg_max_returns_unsat_6869() {
    let result = run_z4_hwbench("QF_UF_cache_coherence_three_ab_reg_max.smt2");
    assert_eq!(
        result, "unsat",
        "#6869: cache_coherence benchmark must return unsat"
    );
}
