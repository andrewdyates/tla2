// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile-time feature reporting for z4.
//!
//! Zero runtime overhead: all feature detection uses `cfg!()` which evaluates
//! at compile time. The report is a structured key=value format for LLM and
//! machine consumption.

/// Feature status as a structured entry.
pub(crate) struct Feature {
    pub name: &'static str,
    pub enabled: bool,
    /// Human-readable description. Used by `feature_summary()` and available
    /// for diagnostic tooling; not included in the JSON `--features` output.
    #[allow(dead_code)]
    pub description: &'static str,
}

/// Returns all z4 feature flags and their compile-time status.
///
/// This is a const-evaluable function with zero runtime overhead.
/// Each entry reports whether the feature was enabled at compile time.
pub(crate) fn all_features() -> &'static [Feature] {
    &[
        // SAT engine features
        Feature {
            name: "unsafe-bcp",
            enabled: z4_sat::feature_flags::UNSAFE_BCP,
            description: "CaDiCaL-exact raw pointer BCP (~2x throughput)",
        },
        Feature {
            name: "sat-jit",
            enabled: z4_sat::feature_flags::JIT,
            description: "Cranelift JIT-compiled BCP for static clauses",
        },
        Feature {
            name: "sat-gpu",
            enabled: z4_sat::feature_flags::GPU,
            description: "GPU compute infrastructure (wgpu/Metal)",
        },
        // DPLL(T) features
        Feature {
            name: "proof-checker",
            enabled: z4_dpll::feature_flags::PROOF_CHECKER,
            description: "Internal Alethe proof checker",
        },
    ]
}

/// Names of enabled feature flags.
pub(crate) fn enabled_feature_names() -> Vec<&'static str> {
    all_features()
        .iter()
        .filter(|f| f.enabled)
        .map(|f| f.name)
        .collect()
}

/// Supported SMT-LIB logics.
///
/// This is the authoritative list of logics z4 accepts via `(set-logic ...)`.
/// Kept in SMT-LIB alphabetical order. HORN is listed last as a non-standard
/// extension for CHC solving.
pub(crate) const SUPPORTED_LOGICS: &[&str] = &[
    "ALL",
    "AUFDT",
    "AUFDTLIA",
    "AUFDTLIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFLRA",
    "LIA",
    "LIRA",
    "LRA",
    "NIA",
    "NIRA",
    "NRA",
    "QF_ABV",
    "QF_AUFBV",
    "QF_AUFLIA",
    "QF_AUFLIRA",
    "QF_AUFLRA",
    "QF_AX",
    "QF_BV",
    "QF_BVFP",
    "QF_DT",
    "QF_FP",
    "QF_LIA",
    "QF_LIRA",
    "QF_LRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_S",
    "QF_SEQ",
    "QF_SLIA",
    "QF_SNIA",
    "QF_UF",
    "QF_UFBV",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNIA",
    "QF_UFNIRA",
    "QF_UFNRA",
    "UF",
    "UFDT",
    "UFDTLIA",
    "UFDTLIRA",
    "UFDTLRA",
    "UFDTNIA",
    "UFDTNIRA",
    "UFDTNRA",
    "UFLIA",
    "UFLRA",
    "UFNIA",
    "UFNIRA",
    "UFNRA",
    "HORN",
];

/// Supported proof output formats.
pub(crate) const PROOF_FORMATS: &[&str] = &["DRAT", "LRAT", "Alethe"];

/// Print a JSON feature report to stdout (`--features`).
///
/// Output is a single JSON object for machine consumption.
/// Uses serde_json for correct escaping and valid JSON output.
pub(crate) fn print_feature_report() {
    let version = env!("CARGO_PKG_VERSION");
    let commit = env!("Z4_GIT_HASH");
    let build_date = env!("Z4_BUILD_DATE");
    let profile = env!("Z4_BUILD_PROFILE");

    let enabled: Vec<&str> = enabled_feature_names();

    let obj = serde_json::json!({
        "version": version,
        "commit": commit,
        "build_date": build_date,
        "features": enabled,
        "supported_logics": SUPPORTED_LOGICS,
        "proof_formats": PROOF_FORMATS,
        "build_profile": profile,
    });
    safe_println!("{}", serde_json::to_string_pretty(&obj).unwrap_or_else(|_| "{}".to_string()));
}

/// One-line feature summary for `--version` output.
///
/// Example: `+unsafe-bcp -sat-jit -sat-gpu +proof-checker`
pub(crate) fn feature_summary() -> String {
    all_features()
        .iter()
        .map(|f| {
            let prefix = if f.enabled { "+" } else { "-" };
            format!("{prefix}{}", f.name)
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// One-line version string for `--version`.
///
/// Format: `z4 VERSION (HASH DATE) [LOGICS...] [FEATURES]`
pub(crate) fn version_line() -> String {
    let logics = SUPPORTED_LOGICS.join(" ");
    format!(
        "z4 {} ({} {}) [{}] [{}]",
        env!("CARGO_PKG_VERSION"),
        env!("Z4_GIT_HASH"),
        env!("Z4_BUILD_DATE"),
        logics,
        feature_summary(),
    )
}

/// Interactive mode banner printed when z4 is run on a TTY without arguments.
pub(crate) fn interactive_banner() -> String {
    // Show a compact subset of commonly used logics in the banner.
    let common_logics = [
        "QF_LIA", "QF_LRA", "QF_BV", "QF_ABV", "QF_UF", "QF_UFLIA", "QF_UFLRA", "QF_FP",
        "HORN", "ALL",
    ];
    let logics_str = common_logics.join(" ");
    format!(
        "z4 {} ({}) -- High-performance SMT solver\n\
         Type SMT-LIB 2.6 commands. Ctrl-D to exit.\n\
         Supported: {}",
        env!("CARGO_PKG_VERSION"),
        env!("Z4_GIT_HASH"),
        logics_str,
    )
}

