// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Feature-gated HWMCC `/unsafe/` soundness canary suite (#4311, R22 design).
//!
//! Each benchmark in `CANARY_BENCHMARKS` lives under `~/hwmcc/benchmarks/
//! bitlevel/safety/.../unsafe/` and has a KNOWN `SAT` (unsafe) verdict per
//! the HWMCC ground truth. If tla-aiger ever returns `Unsat` for one of
//! these inputs, that is a SOUNDNESS REGRESSION (false UNSAT), and the
//! test MUST fail loudly — that is the entire purpose of this canary.
//!
//! `Unknown` is also treated as failure: the benchmarks are tiny (all
//! 5–50 KB) and the per-benchmark timeout (60 s) is generous. A correct
//! SAT-based portfolio on this hardware should return `Sat` within seconds.
//!
//! The suite is gated behind the `hwmcc_canary` cargo feature and additionally
//! skipped at runtime when the benchmark files are not present on disk, so
//! machines without HWMCC fixtures do NOT fail the build — they simply skip
//! with an `eprintln!` diagnostic.
//!
//! Run:
//!   cargo test -p tla-aiger --features hwmcc_canary -- unsafe_canary

#![cfg(feature = "hwmcc_canary")]

use std::path::Path;
use std::time::Duration;

use tla_aiger::{check_aiger_sat, parse_file, AigerCheckResult};

/// Per-benchmark timeout. A10's audit (`reports/2026-04-20-a10-tl54-r22-
/// wave29-audit.md`) estimates these should all solve in <5 s on a
/// competent SAT backend; 60 s gives ~12x headroom before we treat
/// a slow/stuck solver as a regression.
const CANARY_TIMEOUT_SECS: u64 = 60;

/// Smallest `/unsafe/` HWMCC safety benchmarks on disk, ground-truth SAT.
/// Ordered by file size (ascending) so the cheapest one runs first.
///
/// Sizes verified against `~/hwmcc/benchmarks/bitlevel/safety/` on
/// 2026-04-20 — all seven benchmarks under 50 KB.
const CANARY_BENCHMARKS: &[&str] = &[
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/circular_pointer_top_w8_d16_e0.aig", // 11.5 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/shift_register_top_w16_d16_e0.aig",  // 18.9 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/circular_pointer_top_w8_d32_e0.aig", // 21.0 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/arbitrated_top_n3_w8_d16_e0.aig",    // 35.9 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/circular_pointer_top_w32_d16_e0.aig",// 42.5 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/arbitrated_top_n2_w8_d32_e0.aig",    // 45.5 KB
    "./hwmcc/benchmarks/bitlevel/safety/2019/mann/data-integrity/unsafe/arbitrated_top_n4_w16_d8_e0.aig",    // 47.3 KB
];

fn assert_sat_or_panic(path: &str) {
    if !Path::new(path).exists() {
        // Only the path-not-exist case is allowed to skip per R22's design.
        // Everything else is a hard failure.
        eprintln!(
            "skip: HWMCC benchmark not available at {} (R22 canary suite \
             requires ~/hwmcc/benchmarks/bitlevel/safety/ fixtures)",
            path
        );
        return;
    }

    let circuit = parse_file(Path::new(path))
        .unwrap_or_else(|e| panic!("R22 canary parse failed for {}: {:?}", path, e));

    let results = check_aiger_sat(&circuit, Some(Duration::from_secs(CANARY_TIMEOUT_SECS)));

    // `/unsafe/` benchmarks all have exactly one bad property (safety
    // output) and that property must be SAT (reachable).
    assert!(
        !results.is_empty(),
        "R22 canary {} returned no results (expected exactly one SAT verdict)",
        path
    );

    match &results[0] {
        AigerCheckResult::Sat { trace } => {
            eprintln!(
                "R22 canary OK: {} -> Sat (trace len={})",
                path,
                trace.len()
            );
        }
        AigerCheckResult::Unsat => {
            panic!(
                "R22 CANARY SOUNDNESS REGRESSION: {} returned Unsat, \
                 but ground truth is Sat (unsafe). This is a false UNSAT — \
                 see #4311 and A10's audit \
                 reports/2026-04-20-a10-tl54-r22-wave29-audit.md",
                path
            );
        }
        AigerCheckResult::Unknown { reason } => {
            panic!(
                "R22 CANARY REGRESSION: {} returned Unknown ({}), but ground \
                 truth is Sat (unsafe) and per-benchmark timeout was {}s — \
                 either the SAT backend is stuck or has regressed. See #4311.",
                path, reason, CANARY_TIMEOUT_SECS
            );
        }
    }
}

#[test]
fn unsafe_canary_circular_pointer_w8_d16() {
    assert_sat_or_panic(CANARY_BENCHMARKS[0]);
}

#[test]
fn unsafe_canary_shift_register_w16_d16() {
    assert_sat_or_panic(CANARY_BENCHMARKS[1]);
}

#[test]
fn unsafe_canary_circular_pointer_w8_d32() {
    assert_sat_or_panic(CANARY_BENCHMARKS[2]);
}

#[test]
fn unsafe_canary_arbitrated_n3_w8_d16() {
    assert_sat_or_panic(CANARY_BENCHMARKS[3]);
}

#[test]
fn unsafe_canary_circular_pointer_w32_d16() {
    assert_sat_or_panic(CANARY_BENCHMARKS[4]);
}

#[test]
fn unsafe_canary_arbitrated_n2_w8_d32() {
    assert_sat_or_panic(CANARY_BENCHMARKS[5]);
}

#[test]
fn unsafe_canary_arbitrated_n4_w16_d8() {
    assert_sat_or_panic(CANARY_BENCHMARKS[6]);
}
