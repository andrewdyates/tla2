// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rust policy verdict evaluator for `tla2 supremacy gate`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::Serialize;
use serde_json::Value;

use super::policy::{PlannedGate, SelftestRequirement, TelemetryRequirement};
use super::PreparedSupremacy;

const VERDICT_SCHEMA: &str = "tla2.single_thread_supremacy.policy_verdict.v1";
const FLAT_PRIMARY_REBUILD_MARKER: &str =
    "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: reason=flat_state_primary layout promotion";

#[derive(Debug, Serialize)]
pub(super) struct PolicyVerdict {
    schema: &'static str,
    verdict: &'static str,
    gate_mode: Option<String>,
    expected_run_count: Option<usize>,
    errors: Vec<String>,
    policy_file: PathBuf,
    raw_benchmark_summary: SummaryReference,
    policy_fields: BTreeMap<&'static str, &'static str>,
    required_llvm2_env: BTreeMap<String, String>,
    generated_state_count_sources: BTreeMap<&'static str, &'static str>,
    planned_gate: Option<PlannedGate>,
}

#[derive(Debug, Serialize)]
struct SummaryReference {
    path: PathBuf,
}

impl PolicyVerdict {
    fn passed(&self) -> bool {
        self.errors.is_empty()
    }
}

pub(super) fn evaluate_and_write(
    prepared: &PreparedSupremacy,
    summary_path: &Path,
) -> Result<bool> {
    let verdict = evaluate(prepared, summary_path)?;
    let verdict_path = prepared.output_dir.join("policy_verdict.json");
    fs::write(
        &verdict_path,
        serde_json::to_string_pretty(&verdict).context("serialize policy verdict")? + "\n",
    )
    .with_context(|| format!("write {}", verdict_path.display()))?;

    let markdown_path = prepared.output_dir.join("policy_verdict.md");
    fs::write(&markdown_path, render_markdown(&verdict))
        .with_context(|| format!("write {}", markdown_path.display()))?;

    Ok(verdict.passed())
}

fn evaluate(prepared: &PreparedSupremacy, summary_path: &Path) -> Result<PolicyVerdict> {
    let text = fs::read_to_string(summary_path)
        .with_context(|| format!("read benchmark summary {}", summary_path.display()))?;
    let summary: Value = serde_json::from_str(&text)
        .with_context(|| format!("parse benchmark summary {}", summary_path.display()))?;
    let mut errors = Vec::new();
    let gate_plan = prepared.gate_plan.as_ref();

    require_gate_flags(&summary, gate_plan, &mut errors);

    let rows_by_spec = rows_by_spec(&summary, &mut errors);
    for spec in &prepared.policy.specs {
        let Some(row) = rows_by_spec.get(spec.as_str()) else {
            errors.push(format!("{spec}: summary row missing"));
            continue;
        };
        evaluate_row(prepared, summary_path, gate_plan, spec, row, &mut errors);
    }

    let required_llvm2_env = gate_plan
        .map(PlannedGate::enforce_required_env)
        .unwrap_or_default();
    Ok(PolicyVerdict {
        schema: VERDICT_SCHEMA,
        verdict: if errors.is_empty() { "pass" } else { "fail" },
        gate_mode: gate_plan.map(|plan| plan.gate_mode.clone()),
        expected_run_count: prepared.runs,
        errors,
        policy_file: prepared.policy_path.clone(),
        raw_benchmark_summary: SummaryReference {
            path: summary_path.to_path_buf(),
        },
        policy_fields: BTreeMap::from([
            ("generated_state_counts", "expected_generated_state_counts"),
            ("llvm2_env", "gate_modes.*.required_llvm2_env"),
        ]),
        required_llvm2_env,
        generated_state_count_sources: BTreeMap::from([
            ("tlc", "runs[].states_generated"),
            ("interp", "runs[].transitions"),
            ("llvm2", "runs[].transitions"),
        ]),
        planned_gate: gate_plan.cloned(),
    })
}

fn require_gate_flags(summary: &Value, gate_plan: Option<&PlannedGate>, errors: &mut Vec<String>) {
    let Some(gate_plan) = gate_plan else {
        return;
    };
    let Some(flags) = summary.get("gate_flags").and_then(Value::as_object) else {
        errors.push("summary.gate_flags missing or not an object".to_string());
        return;
    };
    for flag in &gate_plan.benchmark_flags {
        if flags.get(flag).and_then(Value::as_bool) != Some(true) {
            errors.push(format!("required benchmark flag was not enabled: {flag}"));
        }
    }
    for flag in &gate_plan.forbidden_benchmark_flags {
        if flags.get(flag).and_then(Value::as_bool) != Some(false) {
            errors.push(format!("forbidden benchmark flag was not disabled: {flag}"));
        }
    }
}

fn rows_by_spec<'a>(summary: &'a Value, errors: &mut Vec<String>) -> BTreeMap<&'a str, &'a Value> {
    let mut rows = BTreeMap::new();
    let Some(items) = summary.get("rows").and_then(Value::as_array) else {
        errors.push("summary.rows missing or not an array".to_string());
        return rows;
    };
    for row in items {
        let Some(spec) = row.get("spec").and_then(Value::as_str) else {
            errors.push("summary row missing string spec".to_string());
            continue;
        };
        if rows.insert(spec, row).is_some() {
            errors.push(format!("{spec}: duplicate summary row"));
        }
    }
    rows
}

fn evaluate_row(
    prepared: &PreparedSupremacy,
    summary_path: &Path,
    gate_plan: Option<&PlannedGate>,
    spec: &str,
    row: &Value,
    errors: &mut Vec<String>,
) {
    let expected_states = prepared.policy.expected_state_counts.get(spec).copied();
    let expected_generated = prepared
        .policy
        .expected_generated_state_counts
        .get(spec)
        .copied();

    let tlc = evaluate_mode(
        spec,
        "tlc",
        row.get("tlc"),
        prepared.runs,
        expected_states,
        expected_generated,
        "states_generated",
        errors,
    );
    let interp = evaluate_mode(
        spec,
        "interp",
        row.get("interp"),
        prepared.runs,
        expected_states,
        expected_generated,
        "transitions",
        errors,
    );
    let llvm2 = evaluate_mode(
        spec,
        "llvm2",
        row.get("llvm2"),
        prepared.runs,
        expected_states,
        expected_generated,
        "transitions",
        errors,
    );

    if let Some(plan) = gate_plan {
        require_state_parity_flags(spec, row, errors);
        require_generated_parity(spec, plan, &tlc, &interp, &llvm2, errors);
        require_llvm2_runs(prepared, summary_path, plan, spec, row, errors);
    }

    if let Some(thresholds) = prepared.policy.thresholds.get(spec) {
        if let (Some(tlc_median), Some(interp_median)) = (tlc.median, interp.median) {
            if let Some(min) = thresholds.min_speedup_interp_vs_tlc {
                let speedup = tlc_median / interp_median;
                if speedup <= min {
                    errors.push(format!(
                        "{spec}: speedup_interp_vs_tlc was {speedup:.6}, expected > {min:.6}"
                    ));
                }
            }
        }
        if let (Some(tlc_median), Some(llvm2_median)) = (tlc.median, llvm2.median) {
            if let Some(min) = thresholds.min_speedup_llvm2_vs_tlc {
                let speedup = tlc_median / llvm2_median;
                require_advertised_speedup(spec, row, "speedup_llvm2_vs_tlc", speedup, errors);
                if speedup <= min {
                    errors.push(format!(
                        "{spec}: speedup_llvm2_vs_tlc was {speedup:.6}, expected > {min:.6}"
                    ));
                }
            }
        }
        if let (Some(interp_median), Some(llvm2_median)) = (interp.median, llvm2.median) {
            if let Some(min) = thresholds.min_llvm2_vs_interp_ratio {
                let ratio = interp_median / llvm2_median;
                if ratio <= min {
                    errors.push(format!(
                        "{spec}: llvm2_vs_interp_ratio was {ratio:.6}, expected > {min:.6}"
                    ));
                }
            }
        }
    }
}

fn require_state_parity_flags(spec: &str, row: &Value, errors: &mut Vec<String>) {
    if row.get("parity_interp_vs_tlc").and_then(Value::as_bool) != Some(true) {
        errors.push(format!("{spec}: interp parity drift vs TLC"));
    }
    if row.get("parity_llvm2_vs_tlc").and_then(Value::as_bool) != Some(true) {
        errors.push(format!("{spec}: llvm2 parity drift vs TLC"));
    }
}

#[derive(Default)]
struct ModeFacts {
    median: Option<f64>,
    generated_by_run: BTreeMap<u64, u64>,
}

fn evaluate_mode(
    spec: &str,
    mode_name: &str,
    mode: Option<&Value>,
    expected_run_count: Option<usize>,
    expected_states: Option<u64>,
    expected_generated: Option<u64>,
    generated_field: &str,
    errors: &mut Vec<String>,
) -> ModeFacts {
    let mut facts = ModeFacts::default();
    let Some(mode) = mode else {
        errors.push(format!("{spec}: {mode_name} summary missing"));
        return facts;
    };
    if mode.get("all_ok").and_then(Value::as_bool) != Some(true) {
        errors.push(format!("{spec}: {mode_name} run failed"));
    }
    let Some(runs) = mode.get("runs").and_then(Value::as_array) else {
        errors.push(format!("{spec}: {mode_name}.runs missing or not an array"));
        return facts;
    };

    let mut elapsed = Vec::new();
    let mut indexes = Vec::new();
    let mut seen_indexes = BTreeSet::new();
    for (position, run) in runs.iter().enumerate() {
        let label = run_label(run, position);
        let run_index = integer_field(run, "run_index");
        if let Some(index) = run_index {
            if !seen_indexes.insert(index) {
                errors.push(format!(
                    "{spec}: {mode_name} run_index {index} was duplicated"
                ));
            }
            indexes.push(index);
        } else {
            errors.push(format!(
                "{spec}: {mode_name} successful run at position {}: run_index was {}, expected an integer",
                position + 1,
                display_value(run.get("run_index")),
            ));
        }

        require_integer_equals(spec, mode_name, &label, run, "returncode", 0, errors);
        require_integer_equals(spec, mode_name, &label, run, "workers", 1, errors);
        if !run.get("error").map(Value::is_null).unwrap_or(true) {
            errors.push(format!(
                "{spec}: {mode_name} {label}: error was {}, expected null/missing",
                display_value(run.get("error"))
            ));
        }
        if let Some(expected) = expected_states {
            require_integer_equals(
                spec,
                mode_name,
                &label,
                run,
                "states_found",
                expected,
                errors,
            );
        }
        if let Some(expected) = expected_generated {
            require_integer_equals(
                spec,
                mode_name,
                &label,
                run,
                generated_field,
                expected,
                errors,
            );
        }
        if let (Some(index), Some(generated)) = (
            run_index,
            integer_field(run, generated_field).map(|value| value as u64),
        ) {
            facts.generated_by_run.insert(index as u64, generated);
        }
        match finite_float_field(run, "elapsed_seconds") {
            Some(value) if value >= 0.0 => elapsed.push(value),
            _ => errors.push(format!(
                "{spec}: {mode_name} {label}: elapsed_seconds was {}, expected a non-negative finite number",
                display_value(run.get("elapsed_seconds"))
            )),
        }
    }

    if let Some(expected) = expected_run_count {
        let expected_indexes = (1..=expected as i64).collect::<Vec<_>>();
        if indexes != expected_indexes {
            errors.push(format!(
                "{spec}: {mode_name} successful run_index values were {indexes:?}, expected sequential {expected_indexes:?}"
            ));
        }
    }

    facts.median = median(&mut elapsed);
    if let Some(advertised) = mode.get("median_seconds") {
        match (facts.median, advertised.as_f64()) {
            (Some(actual), Some(value)) if close(actual, value) => {}
            (Some(actual), _) => errors.push(format!(
                "{spec}: {mode_name} advertised median_seconds {} did not match recomputed median {actual:?}",
                display_value(Some(advertised))
            )),
            (None, _) if advertised.is_null() => {}
            (None, _) => errors.push(format!(
                "{spec}: {mode_name} advertised median_seconds {} did not match recomputed median None",
                display_value(Some(advertised))
            )),
        }
    }
    facts
}

fn require_generated_parity(
    spec: &str,
    plan: &PlannedGate,
    tlc: &ModeFacts,
    interp: &ModeFacts,
    llvm2: &ModeFacts,
    errors: &mut Vec<String>,
) {
    if !plan.require_generated_state_parity_by_run_index {
        return;
    }
    for (run_index, tlc_generated) in &tlc.generated_by_run {
        let interp_generated = interp.generated_by_run.get(run_index);
        let llvm2_generated = llvm2.generated_by_run.get(run_index);
        if interp_generated != Some(tlc_generated) || llvm2_generated != Some(tlc_generated) {
            errors.push(format!(
                "{spec}: generated-state parity failed at run {run_index}: tlc={tlc_generated}, interp={interp_generated:?}, llvm2={llvm2_generated:?}"
            ));
        }
    }
}

fn require_llvm2_runs(
    prepared: &PreparedSupremacy,
    summary_path: &Path,
    plan: &PlannedGate,
    spec: &str,
    row: &Value,
    errors: &mut Vec<String>,
) {
    let Some(runs) = row
        .get("llvm2")
        .and_then(|mode| mode.get("runs"))
        .and_then(Value::as_array)
    else {
        return;
    };
    let mut execution_seconds = Vec::new();
    for (position, run) in runs.iter().enumerate() {
        let label = run_label(run, position);
        require_env(spec, &label, plan, run, errors);
        require_telemetry(spec, &label, plan, run, errors);
        if let Some(seconds) = compiled_bfs_execution_seconds(run.get("llvm2_telemetry")) {
            execution_seconds.push(seconds);
        }
        if let Some(requirement) = plan.required_llvm2_selftest_by_spec.get(spec) {
            require_selftest(summary_path, spec, &label, run, requirement, errors);
        }
    }

    let actual_execution_median = median(&mut execution_seconds);
    if let Some(advertised) = row
        .get("llvm2")
        .and_then(|mode| mode.get("execution_median_seconds"))
    {
        match (actual_execution_median, advertised.as_f64()) {
            (Some(actual), Some(value)) if close(actual, value) => {}
            (Some(actual), _) => errors.push(format!(
                "{spec}: llvm2 advertised execution_median_seconds {} did not match recomputed median {actual:?}",
                display_value(Some(advertised))
            )),
            (None, _) if advertised.is_null() => {}
            (None, _) => errors.push(format!(
                "{spec}: llvm2 advertised execution_median_seconds {} did not match recomputed median None",
                display_value(Some(advertised))
            )),
        }
    }

    if let (Some(tlc_median), Some(execution_median)) = (
        row.get("tlc")
            .and_then(|mode| mode.get("median_seconds"))
            .and_then(Value::as_f64),
        actual_execution_median,
    ) {
        if let Some(thresholds) = prepared.policy.thresholds.get(spec) {
            if let Some(min) = thresholds.min_speedup_llvm2_vs_tlc {
                let speedup = tlc_median / execution_median;
                if speedup <= min {
                    errors.push(format!(
                        "{spec}: speedup_llvm2_execution_vs_tlc was {speedup:.6}, expected > {min:.6}"
                    ));
                }
            }
        }
    }
}

fn require_env(spec: &str, label: &str, plan: &PlannedGate, run: &Value, errors: &mut Vec<String>) {
    let required = plan.enforce_required_env();
    let Some(env) = run.get("env_overrides").and_then(Value::as_object) else {
        errors.push(format!("{spec}: llvm2 {label}: env_overrides missing"));
        return;
    };
    for (key, expected) in required {
        if env.get(&key).and_then(Value::as_str) != Some(expected.as_str()) {
            errors.push(format!(
                "{spec}: llvm2 {label}: env_overrides[{key}] was {}, expected {expected:?}",
                display_value(env.get(&key))
            ));
        }
    }
}

fn require_telemetry(
    spec: &str,
    label: &str,
    plan: &PlannedGate,
    run: &Value,
    errors: &mut Vec<String>,
) {
    let Some(telemetry) = run.get("llvm2_telemetry").and_then(Value::as_object) else {
        errors.push(format!("{spec}: llvm2 {label}: llvm2_telemetry missing"));
        return;
    };
    if plan
        .benchmark_flags
        .iter()
        .any(|flag| flag == "require_no_llvm2_fallbacks")
        && !plan
            .benchmark_flags
            .iter()
            .any(|flag| flag == "allow_llvm2_invariant_rust_fallbacks")
    {
        require_no_fallback_markers(spec, label, telemetry, errors);
    }
    for name in &plan.required_llvm2_compilation_total_matches {
        let compiled = telemetry.get(&format!("llvm2_{name}_compiled"));
        let total = telemetry.get(&format!("llvm2_{name}_total"));
        if integer_value(compiled) != integer_value(total) {
            errors.push(format!(
                "{spec}: llvm2 {label}: llvm2_{name}_compiled {} did not match llvm2_{name}_total {}",
                display_value(compiled),
                display_value(total)
            ));
        }
    }
    let mut requirements = plan.required_llvm2_run_telemetry.clone();
    if let Some(per_spec) = plan.required_llvm2_run_telemetry_by_spec.get(spec) {
        requirements.extend(per_spec.clone());
    }
    for (field, requirement) in requirements {
        let value = telemetry.get(&field);
        match requirement {
            TelemetryRequirement::Bool(expected) => {
                if value.and_then(Value::as_bool) != Some(expected) {
                    errors.push(format!(
                        "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected {expected}",
                        display_value(value)
                    ));
                }
            }
            TelemetryRequirement::Integer(expected) => {
                if integer_value(value) != Some(expected) {
                    errors.push(format!(
                        "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected {expected}",
                        display_value(value)
                    ));
                }
            }
            TelemetryRequirement::Text(expected) => {
                require_text_telemetry(
                    spec, label, telemetry, &field, &expected, value, run, errors,
                );
            }
        }
    }
}

fn require_no_fallback_markers(
    spec: &str,
    label: &str,
    telemetry: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    match telemetry.get("fallback_reasons").and_then(Value::as_array) {
        Some(reasons) if reasons.is_empty() => {}
        Some(reasons) => errors.push(format!(
            "{spec}: llvm2 {label}: LLVM2 fallback reasons observed ({})",
            reasons.len()
        )),
        None => errors.push(format!(
            "{spec}: llvm2 {label}: fallback_reasons missing or not an array"
        )),
    }
}

fn require_text_telemetry(
    spec: &str,
    label: &str,
    telemetry: &serde_json::Map<String, Value>,
    field: &str,
    expected: &str,
    value: Option<&Value>,
    run: &Value,
    errors: &mut Vec<String>,
) {
    match expected {
        "positive" => {
            if !positive_integer(value) {
                errors.push(format!(
                    "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected positive integer",
                    display_value(value)
                ));
            }
        }
        "transitions" => {
            if integer_value(value) != integer_field(run, "transitions") {
                errors.push(format!(
                    "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected transitions {}",
                    display_value(value),
                    display_value(run.get("transitions"))
                ));
            }
        }
        "states_found" => {
            if integer_value(value) != integer_field(run, "states_found") {
                errors.push(format!(
                    "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected states_found {}",
                    display_value(value),
                    display_value(run.get("states_found"))
                ));
            }
        }
        "all" => {
            let total = telemetry.get("llvm2_invariants_total");
            if integer_value(value) != integer_value(total) {
                errors.push(format!(
                    "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected llvm2_invariants_total {}",
                    display_value(value),
                    display_value(total)
                ));
            }
        }
        exact => {
            if value.and_then(Value::as_str) != Some(exact) {
                errors.push(format!(
                    "{spec}: llvm2 {label}: telemetry[{field}] was {}, expected {exact:?}",
                    display_value(value)
                ));
            }
        }
    }
}

fn require_selftest(
    summary_path: &Path,
    spec: &str,
    label: &str,
    run: &Value,
    requirement: &SelftestRequirement,
    errors: &mut Vec<String>,
) {
    let Some(artifact_dir) = run.get("artifact_dir").and_then(Value::as_str) else {
        errors.push(format!("{spec}: llvm2 {label}: artifact_dir missing"));
        return;
    };
    let base = summary_path.parent().unwrap_or_else(|| Path::new("."));
    let artifact_dir = base.join(artifact_dir);
    let text = ["stdout.txt", "stderr.txt"]
        .into_iter()
        .filter_map(|name| fs::read_to_string(artifact_dir.join(name)).ok())
        .collect::<Vec<_>>()
        .join("\n");
    if text.is_empty() {
        errors.push(format!(
            "{spec}: llvm2 {label}: selftest artifacts missing under {}",
            artifact_dir.display()
        ));
        return;
    }
    let relevant = text
        .rfind(FLAT_PRIMARY_REBUILD_MARKER)
        .map(|index| &text[index + FLAT_PRIMARY_REBUILD_MARKER.len()..])
        .unwrap_or(text.as_str());
    let prepared = relevant.contains(&format!(
        "prepared native fused callout selftest: actions={}, state_constraints={}, invariants={}, missing_expected=0, fail_closed=true",
        requirement.actions, requirement.state_constraints, requirement.invariants
    ));
    let running = relevant.contains(&format!(
        "running native fused callout selftest on first real parent: state_len={}, actions={}, state_constraints={}, invariants={}, fail_closed=true",
        requirement.state_len, requirement.actions, requirement.state_constraints, requirement.invariants
    ));
    let complete = relevant.contains("native fused callout selftest complete");
    if !prepared || !running || !complete {
        errors.push(format!(
            "{spec}: llvm2 {label}: strict native fused selftest markers missing or mismatched"
        ));
    }
}

fn require_integer_equals(
    spec: &str,
    mode_name: &str,
    label: &str,
    run: &Value,
    field: &str,
    expected: u64,
    errors: &mut Vec<String>,
) {
    if integer_field(run, field).map(|value| value as u64) != Some(expected) {
        errors.push(format!(
            "{spec}: {mode_name} {label}: {field} was {}, expected {expected}",
            display_value(run.get(field))
        ));
    }
}

fn run_label(run: &Value, position: usize) -> String {
    integer_field(run, "run_index")
        .map(|index| format!("run {index}"))
        .unwrap_or_else(|| format!("run at position {}", position + 1))
}

fn integer_field(value: &Value, field: &str) -> Option<i64> {
    integer_value(value.get(field))
}

fn integer_value(value: Option<&Value>) -> Option<i64> {
    let value = value?;
    if value.is_boolean() {
        return None;
    }
    value.as_i64()
}

fn finite_float_field(value: &Value, field: &str) -> Option<f64> {
    let value = value.get(field)?;
    if value.is_boolean() {
        return None;
    }
    value.as_f64().filter(|number| number.is_finite())
}

fn positive_integer(value: Option<&Value>) -> bool {
    integer_value(value).is_some_and(|value| value > 0)
}

fn require_advertised_speedup(
    spec: &str,
    row: &Value,
    field: &str,
    recomputed: f64,
    errors: &mut Vec<String>,
) {
    match row.get(field).and_then(Value::as_f64) {
        Some(advertised) if close(advertised, recomputed) => {}
        Some(advertised) => errors.push(format!(
            "{spec}: advertised {field} {advertised:?} did not match recomputed speedup {recomputed:?}"
        )),
        None => errors.push(format!(
            "{spec}: advertised {field} was {}, expected recomputed speedup {recomputed:?}",
            display_value(row.get(field))
        )),
    }
}

fn compiled_bfs_execution_seconds(telemetry: Option<&Value>) -> Option<f64> {
    let telemetry = telemetry?;
    let nanos = telemetry.get("compiled_bfs_execution_nanos");
    if let Some(nanos) = integer_value(nanos).filter(|value| *value > 0) {
        return Some(nanos as f64 / 1_000_000_000.0);
    }
    telemetry
        .get("compiled_bfs_execution_seconds")
        .and_then(Value::as_f64)
        .filter(|value| value.is_finite() && *value > 0.0)
}

fn median(values: &mut [f64]) -> Option<f64> {
    if values.is_empty() {
        return None;
    }
    values.sort_by(f64::total_cmp);
    let mid = values.len() / 2;
    if values.len() % 2 == 1 {
        Some(values[mid])
    } else {
        Some((values[mid - 1] + values[mid]) / 2.0)
    }
}

fn close(left: f64, right: f64) -> bool {
    (left - right).abs() <= 1e-12 || (left - right).abs() <= 1e-9 * left.abs().max(right.abs())
}

fn display_value(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(value)) => format!("{value:?}"),
        Some(value) => value.to_string(),
        None => "missing".to_string(),
    }
}

fn render_markdown(verdict: &PolicyVerdict) -> String {
    let mut markdown = format!(
        "# TLA2 Supremacy Policy Verdict\n\nVerdict: **{}**\n\nSummary: `{}`\n",
        verdict.verdict,
        verdict.raw_benchmark_summary.path.display()
    );
    if let Some(gate_mode) = &verdict.gate_mode {
        markdown.push_str(&format!("\nGate mode: `{gate_mode}`\n"));
    }
    if !verdict.errors.is_empty() {
        markdown.push_str("\n## Errors\n");
        for error in &verdict.errors {
            markdown.push_str(&format!("- {error}\n"));
        }
    }
    markdown
}

#[cfg(test)]
mod focused_tests {
    use serde_json::{json, Value};

    use super::*;
    use crate::cli_schema::{
        SupremacyCommonArgs, SupremacyGateMode, SupremacyMode, SupremacyOutputFormat,
    };

    fn repo_policy_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("tests/tlc_comparison/single_thread_supremacy_gate.json")
    }

    fn prepared(output_dir: PathBuf) -> PreparedSupremacy {
        let common = SupremacyCommonArgs {
            policy: repo_policy_path(),
            output_dir: Some(output_dir),
            tla2_bin: None,
            timeout: 300,
            specs: Vec::new(),
            llvm2_env: Vec::new(),
            format: SupremacyOutputFormat::Human,
        };
        PreparedSupremacy::prepare(
            "gate",
            &common,
            Some(3),
            Some(SupremacyGateMode::FullNativeFused),
            Some(SupremacyMode::Enforce),
        )
        .unwrap()
    }

    fn expected_states(prepared: &PreparedSupremacy, spec: &str) -> u64 {
        *prepared.policy.expected_state_counts.get(spec).unwrap()
    }

    fn expected_generated(prepared: &PreparedSupremacy, spec: &str) -> u64 {
        *prepared
            .policy
            .expected_generated_state_counts
            .get(spec)
            .unwrap()
    }

    fn telemetry(prepared: &PreparedSupremacy, spec: &str) -> Value {
        let expected_states = expected_states(prepared, spec);
        let expected_generated = expected_generated(prepared, spec);
        let (actions, invariants, mode, state_len, state_constraints) = match spec {
            "CoffeeCan1000BeansSafety" => (4, 1, "invariant_checking", 2, 0),
            "EWD998Small" => (15, 3, "state_constraint_checking", 15, 1),
            "MCLamportMutex" => (27, 3, "state_constraint_checking", 89, 1),
            other => panic!("unexpected spec {other}"),
        };
        let mut telemetry = json!({
            "llvm2_actions_compiled": actions,
            "llvm2_actions_total": actions,
            "llvm2_invariants_compiled": invariants,
            "llvm2_invariants_total": invariants,
            "compiled_bfs_level_loop_started": true,
            "compiled_bfs_level_loop_fused": true,
            "compiled_bfs_level_loop_initial_states": 1,
            "compiled_bfs_levels_completed": 1,
            "compiled_bfs_parents_processed": 1,
            "compiled_bfs_successors_generated": expected_generated,
            "compiled_bfs_successors_new": expected_states.saturating_sub(1).max(1),
            "compiled_bfs_execution_nanos": 1_000_000_000u64,
            "compiled_bfs_execution_seconds": 1.0,
            "compiled_bfs_total_states": expected_states,
            "llvm2_native_fused_level_built": true,
            "llvm2_native_fused_level_active": true,
            "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
            "transitions": expected_generated,
            "llvm2_native_fused_regular_invariants_checked": true,
            "llvm2_native_fused_invariant_count": invariants,
            "llvm2_native_fused_mode": mode,
            "llvm2_native_fused_state_len": state_len,
            "llvm2_native_fused_state_constraint_count": state_constraints,
            "llvm2_native_fused_local_dedup": false,
            "flat_state_primary": true,
            "flat_bfs_frontier_active": true,
            "flat_bfs_frontier_fallbacks": 0,
            "fallback_reasons": [],
        });
        if state_constraints > 0 {
            telemetry["llvm2_state_constraints_compiled"] = json!(state_constraints);
            telemetry["llvm2_state_constraints_total"] = json!(state_constraints);
        }
        telemetry
    }

    fn runs(prepared: &PreparedSupremacy, spec: &str, mode: &str) -> Vec<Value> {
        let expected_states = expected_states(prepared, spec);
        let expected_generated = expected_generated(prepared, spec);
        let env = prepared.gate_plan.as_ref().unwrap().enforce_required_env();
        (1..=3)
            .map(|run_index| {
                let mut run = json!({
                    "run_index": run_index,
                    "states_found": expected_states,
                    "elapsed_seconds": if mode == "tlc" { 3.0 } else { 2.0 },
                    "returncode": 0,
                    "error": null,
                    "workers": 1,
                    "artifact_dir": format!("artifacts/{spec}/{mode}-{run_index}"),
                });
                if mode == "tlc" {
                    run["states_generated"] = json!(expected_generated);
                } else {
                    run["transitions"] = json!(expected_generated);
                }
                if mode == "llvm2" {
                    run["env_overrides"] = json!(env);
                    run["llvm2_telemetry"] = telemetry(prepared, spec);
                }
                run
            })
            .collect()
    }

    fn row(prepared: &PreparedSupremacy, spec: &str) -> Value {
        let expected_states = expected_states(prepared, spec);
        json!({
            "spec": spec,
            "tlc": {
                "all_ok": true,
                "median_seconds": 3.0,
                "expected_states": expected_states,
                "runs": runs(prepared, spec, "tlc"),
            },
            "interp": {
                "all_ok": true,
                "median_seconds": 2.0,
                "expected_states": expected_states,
                "runs": runs(prepared, spec, "interp"),
            },
            "llvm2": {
                "all_ok": true,
                "median_seconds": 2.0,
                "execution_median_seconds": 1.0,
                "expected_states": expected_states,
                "runs": runs(prepared, spec, "llvm2"),
            },
            "parity_interp_vs_tlc": true,
            "parity_llvm2_vs_tlc": true,
            "llvm2_gate_failures": [],
            "speedup_interp_vs_tlc": 1.5,
            "speedup_llvm2_vs_tlc": 1.5,
            "speedup_llvm2_execution_vs_tlc": 3.0,
        })
    }

    fn summary(prepared: &PreparedSupremacy) -> Value {
        let plan = prepared.gate_plan.as_ref().unwrap();
        let mut flags = serde_json::Map::new();
        for flag in &plan.benchmark_flags {
            flags.insert(flag.clone(), Value::Bool(true));
        }
        for flag in &plan.forbidden_benchmark_flags {
            flags.insert(flag.clone(), Value::Bool(false));
        }
        json!({
            "gate_flags": flags,
            "rows": prepared
                .policy
                .specs
                .iter()
                .map(|spec| row(prepared, spec))
                .collect::<Vec<_>>(),
        })
    }

    fn write_selftest_artifacts(
        prepared: &PreparedSupremacy,
        summary_path: &Path,
        summary: &Value,
    ) {
        for row in summary["rows"].as_array().unwrap() {
            let spec = row["spec"].as_str().unwrap();
            let requirement = &prepared
                .gate_plan
                .as_ref()
                .unwrap()
                .required_llvm2_selftest_by_spec[spec];
            for run in row["llvm2"]["runs"].as_array().unwrap() {
                let artifact_dir = summary_path
                    .parent()
                    .unwrap()
                    .join(run["artifact_dir"].as_str().unwrap());
                fs::create_dir_all(&artifact_dir).unwrap();
                fs::write(
                    artifact_dir.join("stdout.txt"),
                    format!(
                        "{FLAT_PRIMARY_REBUILD_MARKER}\n\
                         [llvm2-selftest] prepared native fused callout selftest: actions={}, state_constraints={}, invariants={}, missing_expected=0, fail_closed=true\n\
                         [llvm2-selftest] running native fused callout selftest on first real parent: state_len={}, actions={}, state_constraints={}, invariants={}, fail_closed=true\n\
                         [llvm2-selftest] native fused callout selftest complete\n",
                        requirement.actions,
                        requirement.state_constraints,
                        requirement.invariants,
                        requirement.state_len,
                        requirement.actions,
                        requirement.state_constraints,
                        requirement.invariants,
                    ),
                )
                .unwrap();
                fs::write(artifact_dir.join("stderr.txt"), "").unwrap();
            }
        }
    }

    fn evaluate_summary(summary: &Value) -> PolicyVerdict {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path().join("out"));
        let summary_path = dir.path().join("summary.json");
        fs::write(&summary_path, serde_json::to_string(summary).unwrap()).unwrap();
        write_selftest_artifacts(&prepared, &summary_path, summary);
        evaluate(&prepared, &summary_path).unwrap()
    }

    #[test]
    fn final_gate_summary_policy_facts_pass() {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path().join("out"));
        let summary = summary(&prepared);
        let summary_path = dir.path().join("summary.json");
        fs::write(&summary_path, serde_json::to_string(&summary).unwrap()).unwrap();
        write_selftest_artifacts(&prepared, &summary_path, &summary);

        let verdict = evaluate(&prepared, &summary_path).unwrap();

        assert!(verdict.passed(), "{:?}", verdict.errors);
    }

    #[test]
    fn final_gate_rejects_worker_state_and_generated_drift() {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path().join("out"));
        let mut summary = summary(&prepared);
        summary["rows"][0]["tlc"]["runs"][0]["workers"] = json!(2);
        summary["rows"][0]["parity_llvm2_vs_tlc"] = json!(false);
        summary["rows"][0]["interp"]["runs"][1]["transitions"] = json!(42);
        let summary_path = dir.path().join("summary.json");
        fs::write(&summary_path, serde_json::to_string(&summary).unwrap()).unwrap();
        write_selftest_artifacts(&prepared, &summary_path, &summary);

        let verdict = evaluate(&prepared, &summary_path).unwrap();

        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("tlc run 1: workers was 2, expected 1")));
        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("llvm2 parity drift vs TLC")));
        assert!(verdict
            .errors
            .iter()
            .any(|error| { error.contains("interp run 2: transitions was 42") }));
    }

    #[test]
    fn final_gate_rejects_native_flat_fallback_and_speedup_drift() {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path().join("out"));
        let mut summary = summary(&prepared);
        let telemetry = &mut summary["rows"][0]["llvm2"]["runs"][0]["llvm2_telemetry"];
        telemetry["llvm2_native_fused_level_active"] = json!(false);
        telemetry["flat_state_primary"] = json!(false);
        telemetry["flat_bfs_frontier_fallbacks"] = json!(1);
        telemetry["fallback_reasons"] = json!(["[llvm2] requested interpreter fallback"]);
        summary["rows"][0]["llvm2"]["median_seconds"] = json!(4.0);
        for run in summary["rows"][0]["llvm2"]["runs"].as_array_mut().unwrap() {
            run["elapsed_seconds"] = json!(4.0);
        }
        summary["rows"][0]["speedup_llvm2_vs_tlc"] = json!(0.75);
        let summary_path = dir.path().join("summary.json");
        fs::write(&summary_path, serde_json::to_string(&summary).unwrap()).unwrap();
        write_selftest_artifacts(&prepared, &summary_path, &summary);

        let verdict = evaluate(&prepared, &summary_path).unwrap();

        assert!(verdict.errors.iter().any(|error| {
            error.contains("llvm2_native_fused_level_active] was false, expected true")
        }));
        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("flat_state_primary] was false, expected true")));
        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("flat_bfs_frontier_fallbacks] was 1, expected 0")));
        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("LLVM2 fallback reasons observed (1)")));
        assert!(verdict.errors.iter().any(|error| {
            error.contains("speedup_llvm2_vs_tlc was 0.750000, expected > 1.000000")
        }));
    }
}

#[cfg(test)]
mod verdict_write_tests {
    use std::collections::BTreeMap;

    use serde_json::{json, Value};

    use super::*;
    use crate::cli_schema::{SupremacyGateMode, SupremacyMode, SupremacyOutputFormat};

    fn repo_policy_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("tests/tlc_comparison/single_thread_supremacy_gate.json")
    }

    fn prepared(output_dir: &Path) -> PreparedSupremacy {
        let policy_path = repo_policy_path();
        let policy = super::super::policy::SupremacyPolicy::load(&policy_path).unwrap();
        let gate_plan = policy
            .resolve_gate_mode(
                SupremacyMode::Enforce,
                Some(SupremacyGateMode::FullNativeFused),
            )
            .map(super::super::policy::PlannedGate::from_resolved)
            .unwrap();
        PreparedSupremacy {
            command: "gate",
            policy_path,
            output_dir: output_dir.to_path_buf(),
            specs: policy.specs.clone(),
            env_overrides: BTreeMap::new(),
            format: SupremacyOutputFormat::Human,
            timeout_seconds: 300,
            tla2_bin: None,
            runs: Some(3),
            gate_mode: Some(SupremacyGateMode::FullNativeFused),
            policy,
            gate_plan: Some(gate_plan),
        }
    }

    fn required_env() -> BTreeMap<&'static str, &'static str> {
        BTreeMap::from([
            ("TLA2_LLVM2", "1"),
            ("TLA2_LLVM2_BFS", "1"),
            ("TLA2_LLVM2_EXISTS", "1"),
            ("TLA2_COMPILED_BFS", "1"),
            ("TLA2_FLAT_BFS", "1"),
            ("TLA2_BYTECODE_VM", "1"),
            ("TLA2_BYTECODE_VM_STATS", "1"),
            ("TLA2_AUTO_POR", "0"),
            ("TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST", "strict"),
            ("TLA2_LLVM2_NATIVE_FUSED_STRICT", "1"),
            ("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", "O3"),
            ("TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL", "O3"),
            ("TLA2_LLVM2_DISABLE_POST_RA_OPT", "0"),
            ("TLA2_DISABLE_ARTIFACT_CACHE", "1"),
            ("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP", "1"),
        ])
    }

    fn mode(kind: &str, states: u64, generated: u64, elapsed: f64) -> Value {
        let generated_field = if kind == "tlc" {
            "states_generated"
        } else {
            "transitions"
        };
        let runs = [1, 2, 3]
            .into_iter()
            .map(|index| {
                let mut run = json!({
                    "run_index": index,
                    "states_found": states,
                    "elapsed_seconds": elapsed,
                    "workers": 1,
                    "returncode": 0,
                });
                run[generated_field] = json!(generated);
                run
            })
            .collect::<Vec<_>>();
        json!({
            "all_ok": true,
            "median_seconds": elapsed,
            "expected_states": states,
            "expected_states_match": true,
            "runs": runs,
        })
    }

    fn valid_summary(output_dir: &Path) -> Value {
        let expected_states = BTreeMap::from([
            ("CoffeeCan1000BeansSafety", 501500_u64),
            ("EWD998Small", 1520618),
            ("MCLamportMutex", 724274),
        ]);
        let expected_generated = BTreeMap::from([
            ("CoffeeCan1000BeansSafety", 1498502_u64),
            ("EWD998Small", 9630813),
            ("MCLamportMutex", 2496350),
        ]);
        let per_spec = BTreeMap::from([
            (
                "CoffeeCan1000BeansSafety",
                json!({
                    "llvm2_native_fused_mode": "invariant_checking",
                    "llvm2_native_fused_state_len": 2,
                    "llvm2_native_fused_state_constraint_count": 0,
                }),
            ),
            (
                "EWD998Small",
                json!({
                    "llvm2_native_fused_mode": "state_constraint_checking",
                    "llvm2_native_fused_state_len": 15,
                    "llvm2_native_fused_state_constraint_count": 1,
                    "llvm2_state_constraints_compiled": 1,
                    "llvm2_state_constraints_total": 1,
                }),
            ),
            (
                "MCLamportMutex",
                json!({
                    "llvm2_native_fused_mode": "state_constraint_checking",
                    "llvm2_native_fused_state_len": 89,
                    "llvm2_native_fused_state_constraint_count": 1,
                    "llvm2_state_constraints_compiled": 1,
                    "llvm2_state_constraints_total": 1,
                }),
            ),
        ]);
        let selftest = BTreeMap::from([
            ("CoffeeCan1000BeansSafety", (4_u64, 0_u64, 1_u64, 2_u64)),
            ("EWD998Small", (15, 1, 3, 15)),
            ("MCLamportMutex", (27, 1, 3, 89)),
        ]);

        let mut rows = Vec::new();
        for spec in ["CoffeeCan1000BeansSafety", "EWD998Small", "MCLamportMutex"] {
            let states = expected_states[spec];
            let generated = expected_generated[spec];
            let mut telemetry = json!({
                "compiled_bfs_level_loop_started": true,
                "compiled_bfs_level_loop_fused": true,
                "compiled_bfs_level_loop_initial_states": 1,
                "compiled_bfs_levels_completed": 1,
                "compiled_bfs_parents_processed": 1,
                "compiled_bfs_successors_generated": generated,
                "compiled_bfs_successors_new": 1,
                "compiled_bfs_execution_nanos": 500000000,
                "compiled_bfs_total_states": states,
                "llvm2_native_fused_level_built": true,
                "llvm2_native_fused_level_active": true,
                "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
                "transitions": generated,
                "llvm2_native_fused_regular_invariants_checked": true,
                "llvm2_native_fused_invariant_count": 3,
                "llvm2_invariants_total": 3,
                "llvm2_invariants_compiled": 3,
                "llvm2_actions_total": 4,
                "llvm2_actions_compiled": 4,
                "llvm2_native_fused_local_dedup": false,
                "flat_state_primary": true,
                "flat_bfs_frontier_active": true,
                "flat_bfs_frontier_fallbacks": 0,
                "fallback_reasons": [],
            });
            telemetry.as_object_mut().unwrap().extend(
                per_spec[spec]
                    .as_object()
                    .unwrap()
                    .iter()
                    .map(|(key, value)| (key.clone(), value.clone())),
            );

            let artifact_dir = format!("artifacts/{spec}/llvm2-1");
            let artifact_path = output_dir.join(&artifact_dir);
            fs::create_dir_all(&artifact_path).unwrap();
            let (actions, state_constraints, invariants, state_len) = selftest[spec];
            fs::write(
                artifact_path.join("stdout.txt"),
                format!(
                    "{FLAT_PRIMARY_REBUILD_MARKER}\n[llvm2-selftest] prepared native fused callout selftest: actions={actions}, state_constraints={state_constraints}, invariants={invariants}, missing_expected=0, fail_closed=true\n[llvm2-selftest] running native fused callout selftest on first real parent: state_len={state_len}, actions={actions}, state_constraints={state_constraints}, invariants={invariants}, fail_closed=true\n[llvm2-selftest] native fused callout selftest complete\n"
                ),
            )
            .unwrap();
            fs::write(artifact_path.join("stderr.txt"), "").unwrap();

            rows.push(json!({
                "spec": spec,
                "tlc": mode("tlc", states, generated, 3.0),
                "interp": mode("interp", states, generated, 2.0),
                "llvm2": {
                    "all_ok": true,
                    "median_seconds": 2.0,
                    "execution_median_seconds": 0.5,
                    "expected_states": states,
                    "expected_states_match": true,
                    "runs": ([1, 2, 3].into_iter().map(|index| json!({
                        "run_index": index,
                        "states_found": states,
                        "elapsed_seconds": 2.0,
                        "workers": 1,
                        "returncode": 0,
                        "transitions": generated,
                        "artifact_dir": artifact_dir,
                        "llvm2_telemetry": telemetry.clone(),
                        "env_overrides": required_env(),
                    })).collect::<Vec<_>>()),
                },
                "parity_interp_vs_tlc": true,
                "parity_llvm2_vs_tlc": true,
                "llvm2_gate_failures": [],
                "speedup_interp_vs_tlc": 1.5,
                "speedup_llvm2_vs_tlc": 1.5,
                "speedup_llvm2_execution_vs_tlc": 6.0,
            }));
        }
        json!({
            "gate_flags": {
                "require_llvm2_compiled_actions": true,
                "require_llvm2_all_actions": true,
                "require_llvm2_compiled_invariants": true,
                "require_llvm2_compiled_bfs": true,
                "require_llvm2_fused_level": true,
                "require_llvm2_native_fused_level": true,
                "require_llvm2_successor_telemetry": true,
                "require_flat_state_primary": true,
                "require_flat_bfs_frontier": true,
                "require_no_llvm2_fallbacks": true,
                "require_llvm2_faster_than_tlc": true,
                "require_llvm2_execution_faster_than_tlc": true,
                "allow_llvm2_invariant_rust_fallbacks": false
            },
            "rows": rows,
        })
    }

    #[test]
    fn writes_passing_policy_verdict() {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path());
        let summary_path = dir.path().join("summary.json");
        fs::write(
            &summary_path,
            serde_json::to_string(&valid_summary(dir.path())).unwrap(),
        )
        .unwrap();

        let passed = evaluate_and_write(&prepared, &summary_path).unwrap();

        assert!(passed);
        let verdict: Value = serde_json::from_str(
            &fs::read_to_string(dir.path().join("policy_verdict.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(verdict["schema"], VERDICT_SCHEMA);
        assert_eq!(verdict["verdict"], "pass");
        assert_eq!(
            verdict["generated_state_count_sources"]["llvm2"],
            "runs[].transitions"
        );
    }

    #[test]
    fn rejects_wrong_fixed_state_count() {
        let dir = tempfile::tempdir().unwrap();
        let prepared = prepared(dir.path());
        let mut summary = valid_summary(dir.path());
        summary["rows"][0]["llvm2"]["runs"][0]["states_found"] = json!(501499);
        let summary_path = dir.path().join("summary.json");
        fs::write(&summary_path, serde_json::to_string(&summary).unwrap()).unwrap();

        let verdict = evaluate(&prepared, &summary_path).unwrap();

        assert!(!verdict.passed());
        assert!(verdict
            .errors
            .iter()
            .any(|error| error.contains("states_found was 501499, expected 501500")));
    }
}
