// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Data types for the `diagnose` subcommand: baseline schema, results, JSON output.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

// ── Baseline schema (v3) ────────────────────────────────────────────────────

#[derive(Deserialize)]
pub(super) struct Baseline {
    pub(super) inputs: BaselineInputs,
    pub(super) specs: BTreeMap<String, BaselineSpec>,
}

#[derive(Deserialize)]
pub(super) struct BaselineInputs {
    pub(super) examples_dir: String,
}

#[derive(Deserialize, Serialize, Clone)]
pub(super) struct BaselineSpec {
    pub(super) tlc: BaselineTlc,
    pub(super) tla2: BaselineTla2,
    pub(super) verified_match: bool,
    pub(super) category: String,
    pub(super) source: Option<BaselineSource>,
    #[serde(default)]
    pub(super) expected_mismatch: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(super) expected_mismatch_reason: Option<String>,
    /// TLA2-specific expected state count. When present, `diagnose` compares
    /// TLA2 output against this field instead of `tlc.states`. This handles
    /// specs where PRNG differences produce deterministic-but-different state
    /// counts (e.g., SpanTreeRandom uses RandomElement which yields different
    /// graphs per implementation).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(super) tla2_expected_states: Option<u64>,
    /// Per-spec timeout override in seconds. When present, `diagnose` uses
    /// `max(cli_timeout, diagnose_timeout_seconds)` as the effective budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(super) diagnose_timeout_seconds: Option<u64>,
    /// Per-spec continue-on-error override. When `false`, the spec is checked
    /// at first-error (no `--continue-on-error` flag), matching TLC baselines
    /// that were collected without `-continue`. Defaults to `true` (current
    /// behavior) so existing specs are unaffected.
    #[serde(
        default = "default_continue_on_error",
        skip_serializing_if = "is_default_continue_on_error"
    )]
    pub(super) continue_on_error: bool,
}

fn default_continue_on_error() -> bool {
    true
}

fn is_default_continue_on_error(v: &bool) -> bool {
    *v
}

impl BaselineSpec {
    /// Returns the effective continue-on-error mode for this spec.
    ///
    /// TLC stops at invariant and assume violations by default; the baseline
    /// state counts reflect that first-error behavior. Continuing past these
    /// violations in TLA2 explores states TLC never saw, causing state count
    /// mismatches and timeouts (see #833).
    ///
    /// Returns `false` when:
    /// - The per-spec override explicitly sets `continue_on_error: false`, OR
    /// - The TLC baseline has `error_type` of "invariant" or "assume_violation"
    pub(super) fn effective_continue_on_error(&self) -> bool {
        if !self.continue_on_error {
            return false;
        }
        !matches!(
            self.tlc.error_type.as_deref(),
            Some("invariant" | "assume_violation")
        )
    }
}

#[derive(Deserialize, Serialize, Clone)]
pub(super) struct BaselineTlc {
    pub(super) status: String,
    pub(super) states: Option<u64>,
    pub(super) error_type: Option<String>,
}

#[derive(Deserialize, Serialize, Clone)]
pub(super) struct BaselineTla2 {
    pub(super) status: String,
    pub(super) states: Option<u64>,
    pub(super) error_type: Option<String>,
    pub(super) last_run: Option<String>,
    pub(super) git_commit: Option<String>,
}

#[derive(Deserialize, Serialize, Clone)]
pub(super) struct BaselineSource {
    pub(super) tla_path: String,
    pub(super) cfg_path: String,
    /// Optional execution mode: "check" (default), "simulate", or "generate".
    /// Specs requiring simulation mode (e.g., SimKnuthYao, SimTokenRing) use "simulate".
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(super) mode: Option<String>,
}

// ── Subprocess JSON output (subset of tla_check::JsonOutput) ────────────────

#[derive(Deserialize)]
pub(super) struct SubprocessOutput {
    pub(super) result: SubprocessResult,
    pub(super) statistics: SubprocessStats,
}

#[derive(Deserialize)]
pub(super) struct SubprocessResult {
    pub(super) status: String,
    pub(super) error_type: Option<String>,
    pub(super) error_message: Option<String>,
}

#[derive(Deserialize)]
pub(super) struct SubprocessStats {
    pub(super) states_found: u64,
}

// ── Result types ────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SpecVerdict {
    Pass,
    ExpectedMismatch,
    StateMismatch,
    FalsePositive,
    FalseNegative,
    Crash,
    OomKilled,
    Timeout,
    FlakyTimeout,
    Skip,
    BothFail,
}

impl SpecVerdict {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Pass => "pass",
            Self::ExpectedMismatch => "expected_mismatch",
            Self::StateMismatch => "state_mismatch",
            Self::FalsePositive => "false_positive",
            Self::FalseNegative => "false_negative",
            Self::Crash => "crash",
            Self::OomKilled => "oom_killed",
            Self::Timeout => "timeout",
            Self::FlakyTimeout => "flaky_timeout",
            Self::Skip => "skip",
            Self::BothFail => "both_fail",
        }
    }
}

pub(super) struct SpecResult {
    pub(super) name: String,
    pub(super) verdict: SpecVerdict,
    pub(super) tla2_status: Option<String>,
    pub(super) tla2_states: Option<u64>,
    pub(super) tlc_status: String,
    pub(super) tlc_states: Option<u64>,
    pub(super) tlc_error_type: Option<String>,
    pub(super) error_details: Option<String>,
    pub(super) expected_mismatch_reason: Option<String>,
    pub(super) time_seconds: f64,
    /// Effective timeout applied for this spec.
    pub(super) timeout_seconds: u64,
    /// Whether the timeout came from the CLI cap or a baseline override.
    pub(super) timeout_source: TimeoutSource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub(super) enum TimeoutSource {
    #[serde(rename = "cli")]
    Cli,
    #[serde(rename = "baseline")]
    Baseline,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DiagnoseCheckPolicy {
    BaselineParity,
    CheckerWorkers(usize),
}

impl DiagnoseCheckPolicy {
    pub(super) fn from_checker_workers(checker_workers: Option<usize>) -> Self {
        match checker_workers {
            Some(workers) => Self::CheckerWorkers(workers),
            None => Self::BaselineParity,
        }
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::BaselineParity => "baseline_parity",
            Self::CheckerWorkers(_) => "checker_workers",
        }
    }

    pub(super) fn checker_workers(self) -> Option<usize> {
        match self {
            Self::BaselineParity => None,
            Self::CheckerWorkers(workers) => Some(workers),
        }
    }

    pub(super) fn effective_workers(self) -> usize {
        match self {
            // Use auto (0) for baseline parity — parallel is the default user
            // experience for `tla2 check`, and state counts are deterministic
            // regardless of worker count. Single-worker mode caused memory
            // blowup on large specs (bosco: 56GB/1-worker vs 10GB/8-worker)
            // and missed the CAS FPSet code path.
            Self::BaselineParity => 0,
            Self::CheckerWorkers(workers) => workers,
        }
    }

    /// Append `--workers N` and optionally `--continue-on-error` to a
    /// `tla2 check` subprocess command. The `continue_on_error` parameter
    /// is a per-spec override from the baseline; when `false`, the spec is
    /// checked at first-error to match a TLC baseline collected without
    /// `-continue`.
    pub(super) fn append_check_args(
        self,
        cmd: &mut std::process::Command,
        continue_on_error: bool,
    ) {
        cmd.arg("--workers")
            .arg(self.effective_workers().to_string());
        if continue_on_error {
            cmd.arg("--continue-on-error");
        }
    }

    pub(super) fn human_description(self) -> String {
        match self {
            Self::BaselineParity => {
                "baseline_parity (--workers 0 auto-sequential; --continue-on-error unless per-spec override)"
                    .to_string()
            }
            Self::CheckerWorkers(0) => {
                "checker_workers=0 (adaptive; --continue-on-error unless per-spec override)"
                    .to_string()
            }
            Self::CheckerWorkers(workers) => {
                format!("checker_workers={workers} (--continue-on-error unless per-spec override)")
            }
        }
    }
}

// ── JSON output schema (metrics/spec_coverage.json compatible) ──────────────

#[derive(Serialize)]
pub(super) struct JsonReport {
    pub(super) schema_version: u32,
    pub(super) generated_at: String,
    pub(super) binary_info: BinaryInfo,
    pub(super) run_conditions: RunConditions,
    pub(super) summary: JsonSummary,
    pub(super) specs: BTreeMap<String, JsonSpecResult>,
}

#[derive(Serialize)]
pub(super) struct BinaryInfo {
    pub(super) path: String,
    pub(super) git_commit: String,
    pub(super) build_timestamp: Option<String>,
}

#[derive(Clone, Serialize)]
pub(super) struct RunConditions {
    pub(super) cpu_count: usize,
    pub(super) load_avg_1m: f64,
    pub(super) load_avg_5m: f64,
    pub(super) load_avg_15m: f64,
    /// CLI timeout cap in seconds. No spec runs longer than this value.
    /// Part of #3455: changed from floor to cap semantics.
    pub(super) timeout_floor_seconds: u64,
    /// Compatibility alias for `timeout_floor_seconds`. Serialized
    /// with the same value so consumers reading
    /// `run_conditions.timeout_seconds` continue to work.
    pub(super) timeout_seconds: u64,
    pub(super) retries: u32,
    pub(super) checker_policy: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) checker_workers: Option<usize>,
}

#[derive(Serialize)]
pub(super) struct JsonSummary {
    pub(super) total_specs: usize,
    pub(super) specs_ran: usize,
    pub(super) pass: usize,
    pub(super) coverage: f64,
    pub(super) expected_mismatch: usize,
    pub(super) state_mismatch: usize,
    pub(super) false_positive: usize,
    pub(super) false_negative: usize,
    pub(super) crash: usize,
    pub(super) oom_killed: usize,
    pub(super) timeout: usize,
    pub(super) flaky_timeout: usize,
    pub(super) skip: usize,
    pub(super) both_fail: usize,
}

#[derive(Serialize)]
pub(super) struct JsonSpecResult {
    pub(super) status: String,
    pub(super) tla2_states: Option<u64>,
    pub(super) tlc_states: Option<u64>,
    pub(super) tla2_error: Option<String>,
    pub(super) tlc_error_type: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) error_details: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) expected_mismatch_reason: Option<String>,
    pub(super) time_seconds: f64,
    pub(super) timeout_seconds: u64,
    pub(super) timeout_source: TimeoutSource,
}

// ── Tally helper ────────────────────────────────────────────────────────────

pub(super) struct Tally {
    pub(super) pass: usize,
    pub(super) expected_mismatch: usize,
    pub(super) mismatch: usize,
    pub(super) false_pos: usize,
    pub(super) false_neg: usize,
    pub(super) crash: usize,
    pub(super) oom_killed: usize,
    pub(super) timeout: usize,
    pub(super) flaky_timeout: usize,
    pub(super) skip: usize,
    pub(super) both_fail: usize,
    pub(super) coverage: f64,
}

impl Tally {
    pub(super) fn from_results(results: &[SpecResult], total_baseline: usize) -> Self {
        let count = |v: SpecVerdict| results.iter().filter(|r| r.verdict == v).count();
        let pass = count(SpecVerdict::Pass);
        let flaky = count(SpecVerdict::FlakyTimeout);
        Self {
            pass,
            expected_mismatch: count(SpecVerdict::ExpectedMismatch),
            mismatch: count(SpecVerdict::StateMismatch),
            false_pos: count(SpecVerdict::FalsePositive),
            false_neg: count(SpecVerdict::FalseNegative),
            crash: count(SpecVerdict::Crash),
            oom_killed: count(SpecVerdict::OomKilled),
            timeout: count(SpecVerdict::Timeout),
            flaky_timeout: flaky,
            skip: count(SpecVerdict::Skip),
            both_fail: count(SpecVerdict::BothFail),
            coverage: if total_baseline > 0 {
                // FlakyTimeout specs count as passing for coverage —
                // they produce correct results, just not deterministic timing.
                (pass + flaky) as f64 / total_baseline as f64
            } else {
                0.0
            },
        }
    }
}

#[cfg(test)]
#[path = "types_tests.rs"]
mod tests;
