// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// AIGER format parser, IR, and CHC translation for bit-level hardware model checking.
//
// Supports both ASCII (.aag) and binary (.aig) formats, including the
// extended HWMCC header (M I L O A B C J F) for safety and liveness properties.
//
// Reference: "The AIGER And-Inverter Graph (AIG) Format Version 20071012"
// by Armin Biere, Johannes Kepler University, 2006-2007.

pub mod bmc;
pub mod check_result;
pub mod cnf;
pub mod coi;
pub mod error;
pub mod ic3;
pub(crate) mod inn_proper;
pub mod kind;
pub mod parser;
pub mod portfolio;
pub mod preprocess;
pub mod sat_types;
pub mod ternary;
pub mod to_chc;
pub mod transys;
pub mod types;

pub use bmc::{check_bmc, check_bmc_dynamic, check_kind, check_kind_simple_path, BmcResult};
pub use check_result::CheckResult;
pub use error::AigerError;
pub use parser::{parse_aag, parse_aig, parse_file};
pub use portfolio::{
    cegar_ic3_conservative, cegar_ic3_ctp_inf, competition_portfolio, default_preset_pool,
    full_ic3_portfolio, ic3_abs_all, ic3_abs_cst, portfolio_check, portfolio_check_adaptive,
    portfolio_check_detailed, ric3_portfolio, AdaptivePortfolioConfig, AdaptiveScheduler,
    EngineConfig, PortfolioConfig, PortfolioResult,
};
pub use to_chc::{check_aiger, translate_to_chc, AigerCheckResult, AigerTranslation};
pub use types::{AigerAnd, AigerCircuit, AigerJustice, AigerLatch, AigerSymbol, Literal};

use std::time::Duration;

/// Check all safety properties of an AIGER circuit using the SAT-based portfolio
/// (BMC + k-induction). This is the preferred entry point for HWMCC benchmarks.
pub fn check_aiger_sat(
    circuit: &AigerCircuit,
    timeout: Option<Duration>,
) -> Vec<AigerCheckResult> {
    let config = portfolio::PortfolioConfig {
        timeout: timeout.unwrap_or_else(|| Duration::from_secs(3600)),
        ..portfolio::default_portfolio()
    };

    let result = portfolio::portfolio_check(circuit, config);

    // Map the SAT-based CheckResult to the existing AigerCheckResult type
    let n = if !circuit.bad.is_empty() {
        circuit.bad.len()
    } else {
        circuit.outputs.len()
    };

    if n == 0 {
        return vec![];
    }

    match result {
        CheckResult::Safe => (0..n).map(|_| AigerCheckResult::Unsat).collect(),
        CheckResult::Unsafe { trace, .. } => {
            // Convert bool trace to i64 trace for compatibility
            let i64_trace: Vec<rustc_hash::FxHashMap<String, i64>> = trace
                .iter()
                .map(|step| {
                    step.iter()
                        .map(|(k, &v)| (k.clone(), if v { 1 } else { 0 }))
                        .collect()
                })
                .collect();

            if n == 1 {
                vec![AigerCheckResult::Sat { trace: i64_trace }]
            } else {
                // Portfolio finds one violation; mark others as unknown
                let mut results = Vec::with_capacity(n);
                results.push(AigerCheckResult::Sat { trace: i64_trace });
                for _ in 1..n {
                    results.push(AigerCheckResult::Unknown {
                        reason: "other property not checked".into(),
                    });
                }
                results
            }
        }
        CheckResult::Unknown { reason } => (0..n)
            .map(|_| AigerCheckResult::Unknown {
                reason: reason.clone(),
            })
            .collect(),
    }
}
