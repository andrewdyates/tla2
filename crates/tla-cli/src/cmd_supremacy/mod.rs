// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 supremacy` command family.
//!
//! This module owns the Rust entrypoint that will replace the Python
//! single-thread supremacy smoke, benchmark, and gate scripts. Smoke execution
//! is ported first because it is the bounded correctness gate. The gate can
//! also evaluate an existing benchmark `summary.json`; raw benchmark collection
//! still fails closed until the runner is ported.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde_json::json;

use crate::cli_schema::{
    SupremacyArgs, SupremacyBenchmarkArgs, SupremacyCommand, SupremacyCommonArgs,
    SupremacyGateArgs, SupremacyGateMode, SupremacyMode, SupremacyOutputFormat, SupremacySmokeArgs,
};

mod benchmark;
mod policy;
mod smoke;
mod verdict;

use policy::{cli_gate_mode_name, PlannedGate, SupremacyPolicy};

const DEFAULT_SPECS: &[&str] = &["CoffeeCan1000BeansSafety", "EWD998Small", "MCLamportMutex"];

pub(crate) fn cmd_supremacy(args: SupremacyArgs) -> Result<()> {
    match args.command {
        SupremacyCommand::Smoke(args) => cmd_smoke(args),
        SupremacyCommand::Benchmark(args) => cmd_benchmark(args),
        SupremacyCommand::Gate(args) => cmd_gate(args),
    }
}

fn cmd_smoke(args: SupremacySmokeArgs) -> Result<()> {
    let prepared = PreparedSupremacy::prepare("smoke", &args.common, None, None, None)?;
    smoke::run_smoke(prepared)
}

fn cmd_benchmark(args: SupremacyBenchmarkArgs) -> Result<()> {
    if args.runs == 0 {
        bail!("--runs must be >= 1");
    }
    let prepared =
        PreparedSupremacy::prepare("benchmark", &args.common, Some(args.runs), None, None)?;
    benchmark::run_benchmark(prepared)
}

fn cmd_gate(args: SupremacyGateArgs) -> Result<()> {
    if args.runs == 0 {
        bail!("--runs must be >= 1");
    }
    if args.mode == SupremacyMode::Enforce && args.runs < 3 {
        bail!("--runs must be at least 3 in enforce mode");
    }
    let mut prepared = PreparedSupremacy::prepare(
        "gate",
        &args.common,
        Some(args.runs),
        Some(args.gate_mode),
        Some(args.mode),
    )?;
    if args.mode == SupremacyMode::Enforce {
        prepared.validate_enforce_env_overrides()?;
    }
    if let Some(summary_json) = args.summary_json {
        if args.common.output_dir.is_none() {
            if let Some(parent) = summary_json.parent() {
                prepared.output_dir = parent.to_path_buf();
            }
        }
        let passed = verdict::evaluate_and_write(&prepared, &summary_json)?;
        match prepared.format {
            SupremacyOutputFormat::Human | SupremacyOutputFormat::Markdown => {
                let status = if passed { "PASS" } else { "FAIL" };
                eprintln!(
                    "[supremacy] {status}: policy verdict written to {}",
                    prepared.output_dir.join("policy_verdict.json").display()
                );
            }
            SupremacyOutputFormat::Json => {
                println!(
                    "{}",
                    json!({
                        "status": if passed { "pass" } else { "fail" },
                        "policy_verdict": prepared.output_dir.join("policy_verdict.json"),
                    })
                );
            }
        }
        if !passed && args.mode == SupremacyMode::Enforce {
            bail!("tla2 supremacy gate policy verdict failed")
        }
        return Ok(());
    }
    prepared.write_stub_reports("policy verdict runner not yet ported")?;
    prepared.print_stub_notice();
    if args.mode == SupremacyMode::Enforce {
        bail!("tla2 supremacy gate is a Rust CLI skeleton; enforce mode cannot pass until policy execution is implemented")
    }
    Ok(())
}

struct PreparedSupremacy {
    command: &'static str,
    policy_path: PathBuf,
    output_dir: PathBuf,
    specs: Vec<String>,
    env_overrides: BTreeMap<String, String>,
    format: SupremacyOutputFormat,
    timeout_seconds: u64,
    tla2_bin: Option<PathBuf>,
    runs: Option<usize>,
    gate_mode: Option<SupremacyGateMode>,
    policy: SupremacyPolicy,
    gate_plan: Option<PlannedGate>,
}

impl PreparedSupremacy {
    fn prepare(
        command: &'static str,
        common: &SupremacyCommonArgs,
        runs: Option<usize>,
        gate_mode: Option<SupremacyGateMode>,
        run_mode: Option<SupremacyMode>,
    ) -> Result<Self> {
        let policy_path = common.policy.clone();
        let policy = SupremacyPolicy::load(&policy_path)?;
        if gate_mode.is_some() {
            policy.validate_gate_ready()?;
        }
        let specs = if common.specs.is_empty() {
            if policy.specs.is_empty() {
                default_specs()
            } else {
                policy.specs.clone()
            }
        } else {
            common.specs.clone()
        };
        let env_overrides = parse_env_overrides(&common.llvm2_env)?;
        let gate_plan = gate_mode
            .map(|mode| {
                policy.resolve_gate_mode(run_mode.unwrap_or(SupremacyMode::Warn), Some(mode))
            })
            .transpose()?
            .map(PlannedGate::from_resolved);
        let output_dir = common
            .output_dir
            .clone()
            .unwrap_or_else(|| default_output_dir(command));
        fs::create_dir_all(&output_dir)
            .with_context(|| format!("create output dir {}", output_dir.display()))?;
        Ok(Self {
            command,
            policy_path,
            output_dir,
            specs,
            env_overrides,
            format: common.format,
            timeout_seconds: common.timeout,
            tla2_bin: common.tla2_bin.clone(),
            runs,
            gate_mode,
            policy,
            gate_plan,
        })
    }

    fn validate_enforce_env_overrides(&self) -> Result<()> {
        let Some(gate_plan) = &self.gate_plan else {
            return Ok(());
        };
        let required = gate_plan.enforce_required_env();
        for (key, value) in &self.env_overrides {
            let Some(expected) = required.get(key) else {
                continue;
            };
            if value != expected {
                bail!(
                    "enforce/{} requires {}={}; --llvm2-env supplied {}={}",
                    gate_plan.gate_mode,
                    key,
                    expected,
                    key,
                    value
                );
            }
        }
        Ok(())
    }

    fn write_stub_reports(&self, reason: &str) -> Result<()> {
        let summary = json!({
            "schema": "tla2.supremacy.summary.stub.v1",
            "status": "not_implemented",
            "command": self.command,
            "reason": reason,
            "policy_file": self.policy_path,
            "output_dir": self.output_dir,
            "specs": self.specs,
            "policy_specs": self.policy.specs,
            "runs": self.runs,
            "gate_mode": self.gate_plan.as_ref().map(|plan| plan.gate_mode.as_str()),
            "gate_mode_cli": self.gate_mode.map(cli_gate_mode_name),
            "planned_gate": self.gate_plan.as_ref(),
            "timeout_seconds": self.timeout_seconds,
            "tla2_bin": self.tla2_bin,
            "llvm2_env": self.env_overrides,
            "policy_loaded": true,
        });
        let summary_path = self.output_dir.join("summary.json");
        fs::write(
            &summary_path,
            serde_json::to_string_pretty(&summary).context("serialize supremacy summary")? + "\n",
        )
        .with_context(|| format!("write {}", summary_path.display()))?;

        let markdown = format!(
            "# TLA2 Supremacy {command}\n\nStatus: not implemented\n\nReason: {reason}\n\nPolicy: `{policy}`\n",
            command = self.command,
            reason = reason,
            policy = self.policy_path.display(),
        );
        fs::write(self.output_dir.join("summary.md"), markdown)
            .with_context(|| format!("write {}", self.output_dir.join("summary.md").display()))?;

        if self.command == "gate" {
            let verdict = json!({
                "schema": "tla2.single_thread_supremacy.policy_verdict.stub.v1",
                "verdict": "not_implemented",
                "gate_mode": self.gate_plan.as_ref().map(|plan| plan.gate_mode.as_str()),
                "expected_run_count": self.runs,
                "errors": [reason],
                "policy_file": self.policy_path,
                "summary_file": summary_path,
                "planned_gate": self.gate_plan.as_ref(),
            });
            let path = self.output_dir.join("policy_verdict.json");
            fs::write(
                &path,
                serde_json::to_string_pretty(&verdict).context("serialize policy verdict")? + "\n",
            )
            .with_context(|| format!("write {}", path.display()))?;
        }
        Ok(())
    }

    fn print_stub_notice(&self) {
        match self.format {
            SupremacyOutputFormat::Human | SupremacyOutputFormat::Markdown => {
                eprintln!(
                    "[supremacy] {} skeleton wrote stub artifacts to {}",
                    self.command,
                    self.output_dir.display()
                );
            }
            SupremacyOutputFormat::Json => {
                println!(
                    "{}",
                    json!({
                        "status": "not_implemented",
                        "command": self.command,
                        "output_dir": self.output_dir,
                    })
                );
            }
        }
    }
}

fn default_output_dir(command: &str) -> PathBuf {
    Path::new("reports").join("perf").join(format!(
        "{}-supremacy-{}",
        chrono::Utc::now().format("%Y%m%dT%H%M%SZ"),
        command
    ))
}

fn default_specs() -> Vec<String> {
    DEFAULT_SPECS
        .iter()
        .map(|spec| (*spec).to_string())
        .collect()
}

fn parse_env_overrides(items: &[String]) -> Result<BTreeMap<String, String>> {
    let mut env = BTreeMap::new();
    for item in items {
        let Some((key, value)) = item.split_once('=') else {
            bail!("--llvm2-env expects KEY=VALUE, got {item:?}");
        };
        if key.is_empty() {
            bail!("--llvm2-env key must not be empty");
        }
        env.insert(key.to_string(), value.to_string());
    }
    Ok(env)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_policy_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("tests/tlc_comparison/single_thread_supremacy_gate.json")
    }

    #[test]
    fn parses_env_overrides() {
        let parsed = parse_env_overrides(&["TLA2_LLVM2=1".to_string(), "A=".to_string()]).unwrap();

        assert_eq!(parsed.get("TLA2_LLVM2").map(String::as_str), Some("1"));
        assert_eq!(parsed.get("A").map(String::as_str), Some(""));
    }

    #[test]
    fn rejects_malformed_env_override() {
        let error = parse_env_overrides(&["TLA2_LLVM2".to_string()]).unwrap_err();

        assert!(error.to_string().contains("KEY=VALUE"));
    }

    #[test]
    fn reads_specs_from_policy() {
        let policy = SupremacyPolicy::load(&repo_policy_path()).unwrap();

        assert_eq!(
            policy.specs,
            vec![
                "CoffeeCan1000BeansSafety".to_string(),
                "EWD998Small".to_string(),
                "MCLamportMutex".to_string()
            ]
        );
    }

    #[test]
    fn enforce_rejects_protected_env_override() {
        let common = SupremacyCommonArgs {
            policy: repo_policy_path(),
            output_dir: None,
            tla2_bin: None,
            timeout: 300,
            specs: Vec::new(),
            llvm2_env: vec!["TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O1".to_string()],
            format: SupremacyOutputFormat::Human,
        };
        let prepared = PreparedSupremacy::prepare(
            "gate",
            &common,
            Some(3),
            Some(SupremacyGateMode::FullNativeFused),
            Some(SupremacyMode::Enforce),
        )
        .unwrap();

        let error = prepared.validate_enforce_env_overrides().unwrap_err();
        assert!(error
            .to_string()
            .contains("requires TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O3"));
    }
}
