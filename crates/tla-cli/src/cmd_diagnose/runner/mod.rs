// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-spec execution: subprocess spawning, timeout handling, result classification.

mod classify;
mod subprocess;

#[cfg(test)]
mod tests;

use std::path::Path;
use std::time::{Duration, Instant};

use super::types::{BaselineSpec, DiagnoseCheckPolicy, SpecResult, SpecVerdict};
use classify::{crash_result, parse_and_classify, skip_result, timeout_result};
pub(super) use subprocess::Semaphore;
use subprocess::{spawn_tla2, wait_with_timeout, WaitResult};

/// Run `tla2 check` on a single spec and classify the result against TLC baseline.
///
/// If `retries > 0` and the spec times out, retry up to `retries` times. A spec
/// that times out initially but passes on a retry is classified as `FlakyTimeout`
/// rather than `Timeout`, distinguishing CPU-contention flakiness from real failures.
pub(super) fn run_one_spec(
    name: &str,
    spec: &BaselineSpec,
    exe: &Path,
    examples_dir: &Path,
    timeout: Duration,
    retries: u32,
    checker_policy: DiagnoseCheckPolicy,
) -> SpecResult {
    let source = match &spec.source {
        Some(s) => s,
        None => return skip_result(name, spec, "no source paths in baseline"),
    };
    let tla_path = examples_dir.join(&source.tla_path);
    let cfg_path = examples_dir.join(&source.cfg_path);

    if !tla_path.is_file() || !cfg_path.is_file() {
        let detail = format!(
            "missing: tla={} cfg={}",
            tla_path.exists(),
            cfg_path.exists()
        );
        return skip_result(name, spec, &detail);
    }

    // Part of #3076: detect simulation mode from baseline source metadata.
    let mode = source.mode.as_deref().unwrap_or("check");

    let result = run_once(
        name,
        spec,
        exe,
        &tla_path,
        &cfg_path,
        timeout,
        mode,
        checker_policy,
    );

    if result.verdict != SpecVerdict::Timeout || retries == 0 {
        return result;
    }

    // Retry timed-out specs — CPU contention can push borderline specs past the limit.
    for attempt in 1..=retries {
        let retry = run_once(
            name,
            spec,
            exe,
            &tla_path,
            &cfg_path,
            timeout,
            mode,
            checker_policy,
        );
        match retry.verdict {
            SpecVerdict::Timeout => continue,
            SpecVerdict::Pass => {
                // Passed on retry — mark as flaky, not a real timeout.
                return SpecResult {
                    verdict: SpecVerdict::FlakyTimeout,
                    error_details: Some(format!(
                        "passed on retry {attempt}/{retries} ({:.1}s); initial attempt timed out",
                        retry.time_seconds
                    )),
                    ..retry
                };
            }
            _ => {
                // Non-timeout, non-pass result (crash, mismatch, etc.) —
                // the initial timeout was masking a real failure. Return as-is.
                return retry;
            }
        }
    }
    // Still timing out after all retries — genuine timeout.
    SpecResult {
        error_details: Some(format!(
            "timeout after {:.0}s ({} retries exhausted)",
            timeout.as_secs_f64(),
            retries
        )),
        ..result
    }
}

fn run_once(
    name: &str,
    spec: &BaselineSpec,
    exe: &Path,
    tla_path: &Path,
    cfg_path: &Path,
    timeout: Duration,
    mode: &str,
    checker_policy: DiagnoseCheckPolicy,
) -> SpecResult {
    let start = Instant::now();
    let child = spawn_tla2(
        exe,
        tla_path,
        cfg_path,
        mode,
        checker_policy,
        spec.effective_continue_on_error(),
    );

    let child = match child {
        Ok(c) => c,
        Err(e) => return crash_result(name, spec, &format!("spawn failed: {e}"), &start),
    };

    let output = wait_with_timeout(child, timeout);
    let elapsed = start.elapsed().as_secs_f64();

    match output {
        WaitResult::Completed(o) => parse_and_classify(name, spec, &o, elapsed),
        WaitResult::Timeout => timeout_result(name, spec, timeout, elapsed),
        WaitResult::Error(e) => crash_result(name, spec, &format!("wait error: {e}"), &start),
    }
}
