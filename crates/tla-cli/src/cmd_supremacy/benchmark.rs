// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rust staging layer for `tla2 supremacy benchmark`.
//!
//! This module ports benchmark-local spec staging and planned subprocess
//! artifacts out of `scripts/benchmark_single_thread_backends_vs_tlc.py`.
//! Timing collection still fails closed until the TLC/TLA2 runner loop and
//! summary aggregation are fully ported.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::Serialize;
use serde_json::json;

use super::PreparedSupremacy;
use crate::cli_schema::SupremacyOutputFormat;

const BENCHMARK_STAGING_SCHEMA: &str = "tla2.single_thread_supremacy.benchmark.staging.v1";
const COFFEECAN_SAFETY_SPEC_NAME: &str = "CoffeeCan1000BeansSafety";
const COFFEECAN_SAFETY_BEANS: usize = 1000;
const DEFAULT_BINARY: &str = "target/user/release/tla2";
const DEFAULT_TLC_JAR: &str = "tlaplus/tla2tools.jar";

pub(super) fn run_benchmark(prepared: PreparedSupremacy) -> Result<()> {
    let repo_root = env::current_dir().context("resolve current working directory")?;
    let examples_dir = tlaplus_examples_dir()?;
    let tla2_binary = prepared
        .tla2_bin
        .clone()
        .unwrap_or_else(|| repo_root.join(DEFAULT_BINARY));
    let tlc_jar = default_tlc_jar()?;

    let mut staged_specs = Vec::new();
    let mut planned_runs = Vec::new();
    for spec_name in &prepared.specs {
        let spec = resolve_benchmark_spec(spec_name, &prepared.output_dir, &examples_dir)?;
        let spec_artifact_dir = prepared.output_dir.join(&spec.name);
        for run_index in 1..=prepared.runs.unwrap_or(1) {
            planned_runs.push(plan_tlc_run(
                &spec,
                run_index,
                &repo_root,
                &tlc_jar,
                &spec_artifact_dir,
            )?);
            planned_runs.push(plan_tla2_run(
                &spec,
                "interp",
                run_index,
                &repo_root,
                &tla2_binary,
                &prepared.env_overrides,
                &spec_artifact_dir,
            )?);
            planned_runs.push(plan_tla2_run(
                &spec,
                "llvm2",
                run_index,
                &repo_root,
                &tla2_binary,
                &prepared.env_overrides,
                &spec_artifact_dir,
            )?);
        }
        staged_specs.push(spec);
    }

    let summary = json!({
        "schema": BENCHMARK_STAGING_SCHEMA,
        "status": "staged",
        "command": prepared.command,
        "policy_file": prepared.policy_path,
        "output_dir": prepared.output_dir,
        "runs": prepared.runs,
        "timeout_seconds": prepared.timeout_seconds,
        "tla2_bin": tla2_binary,
        "tlc_jar": tlc_jar,
        "llvm2_env": prepared.env_overrides,
        "staged_specs": staged_specs,
        "planned_runs": planned_runs,
        "next_port_step": "execute planned TLC/interpreter/LLVM2 runs and aggregate summary rows",
    });
    let summary_json =
        serde_json::to_string_pretty(&summary).context("serialize benchmark staging summary")?;
    fs::write(
        prepared.output_dir.join("summary.json"),
        summary_json + "\n",
    )
    .with_context(|| {
        format!(
            "write {}",
            prepared.output_dir.join("summary.json").display()
        )
    })?;
    let markdown = render_markdown(&summary);
    fs::write(prepared.output_dir.join("summary.md"), &markdown)
        .with_context(|| format!("write {}", prepared.output_dir.join("summary.md").display()))?;

    match prepared.format {
        SupremacyOutputFormat::Human | SupremacyOutputFormat::Markdown => {
            eprintln!(
                "[supremacy] benchmark staged {} planned runs under {}",
                planned_runs.len(),
                prepared.output_dir.display()
            );
        }
        SupremacyOutputFormat::Json => println!("{}", summary),
    }

    bail!(
        "tla2 supremacy benchmark staged Rust artifacts but subprocess execution is not yet implemented"
    )
}

#[derive(Clone, Debug, Serialize)]
struct BenchmarkSpec {
    name: String,
    tla_path: PathBuf,
    cfg_path: PathBuf,
    category: String,
    expected_states: Option<u64>,
    expected_generated_states: Option<u64>,
    timeout_seconds: u64,
    notes: String,
}

#[derive(Clone, Debug, Serialize)]
struct PlannedRun {
    spec: String,
    mode: String,
    run_index: usize,
    artifact_dir: PathBuf,
    command: PlannedCommand,
}

#[derive(Clone, Debug, Serialize)]
struct PlannedCommand {
    argv: Vec<String>,
    cwd: PathBuf,
    env_overrides: BTreeMap<String, String>,
}

fn resolve_benchmark_spec(
    spec_name: &str,
    output_dir: &Path,
    examples_dir: &Path,
) -> Result<BenchmarkSpec> {
    match spec_name {
        COFFEECAN_SAFETY_SPEC_NAME => stage_coffecan_safety_spec(output_dir, examples_dir),
        "EWD998Small" => catalog_spec(
            "EWD998Small",
            "ewd998/EWD998.tla",
            "ewd998/EWD998Small.cfg",
            "ewd998",
            Some(1_520_618),
            Some(2_770_455),
            examples_dir,
        ),
        "MCLamportMutex" => catalog_spec(
            "MCLamportMutex",
            "lamport_mutex/MCLamportMutex.tla",
            "lamport_mutex/MCLamportMutex.cfg",
            "lamport_mutex",
            Some(724_274),
            Some(2_174_319),
            examples_dir,
        ),
        other => bail!(
            "unsupported Rust supremacy benchmark spec {other:?}; port its catalog metadata before running it here"
        ),
    }
}

fn catalog_spec(
    name: &str,
    tla_path: &str,
    cfg_path: &str,
    category: &str,
    expected_states: Option<u64>,
    expected_generated_states: Option<u64>,
    examples_dir: &Path,
) -> Result<BenchmarkSpec> {
    let tla_path = examples_dir.join(tla_path);
    let cfg_path = examples_dir.join(cfg_path);
    validate_spec_files(&tla_path, &cfg_path)?;
    Ok(BenchmarkSpec {
        name: name.to_string(),
        tla_path,
        cfg_path,
        category: category.to_string(),
        expected_states,
        expected_generated_states,
        timeout_seconds: 300,
        notes: String::new(),
    })
}

fn stage_coffecan_safety_spec(output_dir: &Path, examples_dir: &Path) -> Result<BenchmarkSpec> {
    let spec_dir = output_dir
        .join("generated-specs")
        .join("CoffeeCanSafety1000");
    fs::create_dir_all(&spec_dir).with_context(|| format!("create {}", spec_dir.display()))?;
    let source = examples_dir.join("CoffeeCan/CoffeeCan.tla");
    if !source.is_file() {
        bail!("CoffeeCan source not found: {}", source.display());
    }
    fs::copy(&source, spec_dir.join("CoffeeCan.tla"))
        .with_context(|| format!("copy {}", source.display()))?;

    let wrapper_tla = spec_dir.join("CoffeeCanSafetyBench.tla");
    let wrapper_cfg = spec_dir.join("CoffeeCanSafetyBench.cfg");
    fs::write(
        &wrapper_tla,
        format!(
            "---- MODULE CoffeeCanSafetyBench ----\n\
             VARIABLE can\n\n\
             INSTANCE CoffeeCan WITH MaxBeanCount <- {COFFEECAN_SAFETY_BEANS}\n\n\
             SafetyInit ==\n\
             \tcan \\in {{c \\in Can : c.black + c.white = {COFFEECAN_SAFETY_BEANS}}}\n\n\
             ====\n"
        ),
    )
    .with_context(|| format!("write {}", wrapper_tla.display()))?;
    fs::write(
        &wrapper_cfg,
        "INIT\n    SafetyInit\n\nNEXT\n    Next\n\nINVARIANTS\n    TypeInvariant\n",
    )
    .with_context(|| format!("write {}", wrapper_cfg.display()))?;

    Ok(BenchmarkSpec {
        name: COFFEECAN_SAFETY_SPEC_NAME.to_string(),
        tla_path: wrapper_tla,
        cfg_path: wrapper_cfg,
        category: "CoffeeCan".to_string(),
        expected_states: Some(501_500),
        expected_generated_states: Some(1_498_502),
        timeout_seconds: 300,
        notes: "Generated safety-only CoffeeCan1000 model: exact-1000-bean initial frontier, Next, TypeInvariant, no temporal properties or fairness.".to_string(),
    })
}

fn validate_spec_files(tla_path: &Path, cfg_path: &Path) -> Result<()> {
    if !tla_path.is_file() {
        bail!("TLA file not found: {}", tla_path.display());
    }
    if !cfg_path.is_file() {
        bail!("config file not found: {}", cfg_path.display());
    }
    Ok(())
}

fn plan_tlc_run(
    spec: &BenchmarkSpec,
    run_index: usize,
    repo_root: &Path,
    tlc_jar: &Path,
    spec_artifact_dir: &Path,
) -> Result<PlannedRun> {
    let artifact_dir = spec_artifact_dir.join(format!("tlc-run{run_index}"));
    let metadir = artifact_dir.join("tlc-metadir");
    let command = PlannedCommand {
        argv: vec![
            "java".to_string(),
            "-jar".to_string(),
            tlc_jar.display().to_string(),
            spec.tla_path.display().to_string(),
            "-config".to_string(),
            spec.cfg_path.display().to_string(),
            "-metadir".to_string(),
            metadir.display().to_string(),
            "-workers".to_string(),
            "1".to_string(),
        ],
        cwd: spec
            .tla_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf(),
        env_overrides: BTreeMap::new(),
    };
    write_planned_artifacts(repo_root, &artifact_dir, &command)?;
    Ok(PlannedRun {
        spec: spec.name.clone(),
        mode: "tlc".to_string(),
        run_index,
        artifact_dir,
        command,
    })
}

fn plan_tla2_run(
    spec: &BenchmarkSpec,
    mode: &str,
    run_index: usize,
    repo_root: &Path,
    tla2_binary: &Path,
    cli_overrides: &BTreeMap<String, String>,
    spec_artifact_dir: &Path,
) -> Result<PlannedRun> {
    let artifact_dir = spec_artifact_dir.join(format!("{mode}-run{run_index}"));
    let env_overrides = tla2_env(mode, cli_overrides)?;
    let command = PlannedCommand {
        argv: vec![
            tla2_binary.display().to_string(),
            "check".to_string(),
            spec.tla_path.display().to_string(),
            "--config".to_string(),
            spec.cfg_path.display().to_string(),
            "--workers".to_string(),
            "1".to_string(),
            "--force".to_string(),
            "--backend".to_string(),
            backend_name(mode)?.to_string(),
        ],
        cwd: repo_root.to_path_buf(),
        env_overrides,
    };
    write_planned_artifacts(repo_root, &artifact_dir, &command)?;
    Ok(PlannedRun {
        spec: spec.name.clone(),
        mode: mode.to_string(),
        run_index,
        artifact_dir,
        command,
    })
}

fn backend_name(mode: &str) -> Result<&'static str> {
    match mode {
        "interp" => Ok("interpreter"),
        "llvm2" => Ok("llvm2"),
        other => bail!("unsupported benchmark mode {other:?}"),
    }
}

fn tla2_env(
    mode: &str,
    cli_overrides: &BTreeMap<String, String>,
) -> Result<BTreeMap<String, String>> {
    let mut env = BTreeMap::from([
        ("TLA2_BYTECODE_VM".to_string(), "1".to_string()),
        ("TLA2_AUTO_POR".to_string(), "0".to_string()),
    ]);
    match mode {
        "interp" => {
            env.insert("TLA2_LLVM2".to_string(), "0".to_string());
            env.insert("TLA2_LLVM2_BFS".to_string(), "0".to_string());
        }
        "llvm2" => {
            env.insert("TLA2_LLVM2".to_string(), "1".to_string());
            env.insert("TLA2_LLVM2_BFS".to_string(), "1".to_string());
            env.insert("TLA2_LLVM2_EXISTS".to_string(), "1".to_string());
        }
        other => bail!("unsupported benchmark mode {other:?}"),
    }
    env.extend(cli_overrides.clone());
    Ok(env)
}

fn write_planned_artifacts(
    repo_root: &Path,
    artifact_dir: &Path,
    command: &PlannedCommand,
) -> Result<()> {
    fs::create_dir_all(artifact_dir)
        .with_context(|| format!("create {}", artifact_dir.display()))?;
    fs::write(artifact_dir.join("stdout.txt"), "")
        .with_context(|| format!("write {}", artifact_dir.join("stdout.txt").display()))?;
    fs::write(artifact_dir.join("stderr.txt"), "")
        .with_context(|| format!("write {}", artifact_dir.join("stderr.txt").display()))?;
    let report = json!({
        "schema": "tla2.supremacy.planned_command.v1",
        "argv": command.argv,
        "cwd": command.cwd,
        "repo_relative_artifact_dir": repo_relative(repo_root, artifact_dir),
        "env_overrides": command.env_overrides,
        "status": "planned",
    });
    fs::write(
        artifact_dir.join("command.json"),
        serde_json::to_string_pretty(&report).context("serialize planned command")? + "\n",
    )
    .with_context(|| format!("write {}", artifact_dir.join("command.json").display()))?;
    Ok(())
}

fn render_markdown(summary: &serde_json::Value) -> String {
    let mut lines = vec![
        "# Single-Thread Supremacy Benchmark Staging".to_string(),
        String::new(),
        format!(
            "Status: {}",
            summary["status"].as_str().unwrap_or("unknown")
        ),
        format!(
            "Planned runs: {}",
            summary["planned_runs"].as_array().map_or(0, Vec::len)
        ),
        String::new(),
        "| Spec | TLA | Config | Expected states | Expected generated |".to_string(),
        "| --- | --- | --- | ---: | ---: |".to_string(),
    ];
    if let Some(specs) = summary["staged_specs"].as_array() {
        for spec in specs {
            lines.push(format!(
                "| {} | `{}` | `{}` | {} | {} |",
                spec["name"].as_str().unwrap_or("unknown"),
                spec["tla_path"].as_str().unwrap_or(""),
                spec["cfg_path"].as_str().unwrap_or(""),
                fmt_optional_u64(spec.get("expected_states")),
                fmt_optional_u64(spec.get("expected_generated_states")),
            ));
        }
    }
    lines.push(String::new());
    lines.push(
        "Subprocess execution is intentionally still fail-closed in this Rust slice.".to_string(),
    );
    lines.push(String::new());
    lines.join("\n")
}

fn fmt_optional_u64(value: Option<&serde_json::Value>) -> String {
    value
        .and_then(serde_json::Value::as_u64)
        .map(|value| value.to_string())
        .unwrap_or_else(|| "-".to_string())
}

fn tlaplus_examples_dir() -> Result<PathBuf> {
    let home = env::var_os("HOME").context("HOME is not set")?;
    Ok(PathBuf::from(home).join("tlaplus-examples/specifications"))
}

fn default_tlc_jar() -> Result<PathBuf> {
    let home = env::var_os("HOME").context("HOME is not set")?;
    Ok(PathBuf::from(home).join(DEFAULT_TLC_JAR))
}

fn repo_relative(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root)
        .map(Path::display)
        .map(|display| display.to_string())
        .unwrap_or_else(|_| path.display().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stages_coffecan_safety_spec() {
        let dir = tempfile::tempdir().unwrap();
        let examples = dir.path().join("examples");
        let coffee_dir = examples.join("CoffeeCan");
        fs::create_dir_all(&coffee_dir).unwrap();
        fs::write(
            coffee_dir.join("CoffeeCan.tla"),
            "---- MODULE CoffeeCan ----\n====\n",
        )
        .unwrap();
        let output = dir.path().join("out");

        let spec = stage_coffecan_safety_spec(&output, &examples).unwrap();

        assert_eq!(spec.name, COFFEECAN_SAFETY_SPEC_NAME);
        assert_eq!(spec.expected_states, Some(501_500));
        assert_eq!(spec.expected_generated_states, Some(1_498_502));
        assert!(spec.tla_path.is_file());
        assert!(spec.cfg_path.is_file());
        assert!(spec.tla_path.with_file_name("CoffeeCan.tla").is_file());
        let wrapper = fs::read_to_string(&spec.tla_path).unwrap();
        assert!(wrapper.contains("INSTANCE CoffeeCan WITH MaxBeanCount <- 1000"));
        assert!(wrapper.contains("c.black + c.white = 1000"));
        let cfg = fs::read_to_string(&spec.cfg_path).unwrap();
        assert!(cfg.contains("INIT\n    SafetyInit"));
        assert!(cfg.contains("INVARIANTS\n    TypeInvariant"));
    }

    #[test]
    fn builds_mode_specific_tla2_env() {
        let overrides = BTreeMap::from([
            ("TLA2_DISABLE_ARTIFACT_CACHE".to_string(), "1".to_string()),
            ("TLA2_LLVM2_BFS".to_string(), "forced".to_string()),
        ]);

        let interp = tla2_env("interp", &overrides).unwrap();
        assert_eq!(interp.get("TLA2_LLVM2").map(String::as_str), Some("0"));
        assert_eq!(
            interp.get("TLA2_LLVM2_BFS").map(String::as_str),
            Some("forced")
        );

        let llvm2 = tla2_env("llvm2", &overrides).unwrap();
        assert_eq!(llvm2.get("TLA2_LLVM2").map(String::as_str), Some("1"));
        assert_eq!(
            llvm2.get("TLA2_LLVM2_EXISTS").map(String::as_str),
            Some("1")
        );
        assert_eq!(
            llvm2.get("TLA2_DISABLE_ARTIFACT_CACHE").map(String::as_str),
            Some("1")
        );
    }

    #[test]
    fn writes_planned_command_artifacts() {
        let dir = tempfile::tempdir().unwrap();
        let artifact_dir = dir.path().join("artifact");
        let command = PlannedCommand {
            argv: vec!["tla2".to_string(), "check".to_string()],
            cwd: dir.path().to_path_buf(),
            env_overrides: BTreeMap::from([("TLA2_LLVM2".to_string(), "1".to_string())]),
        };

        write_planned_artifacts(dir.path(), &artifact_dir, &command).unwrap();

        assert_eq!(
            fs::read_to_string(artifact_dir.join("stdout.txt")).unwrap(),
            ""
        );
        assert_eq!(
            fs::read_to_string(artifact_dir.join("stderr.txt")).unwrap(),
            ""
        );
        let command_json: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(artifact_dir.join("command.json")).unwrap())
                .unwrap();
        assert_eq!(command_json["schema"], "tla2.supremacy.planned_command.v1");
        assert_eq!(command_json["status"], "planned");
        assert_eq!(command_json["repo_relative_artifact_dir"], "artifact");
        assert_eq!(command_json["env_overrides"]["TLA2_LLVM2"], "1");
    }

    #[test]
    fn planned_tla2_run_uses_expected_backend_and_artifact_dir() {
        let dir = tempfile::tempdir().unwrap();
        let spec = BenchmarkSpec {
            name: "Example".to_string(),
            tla_path: dir.path().join("Example.tla"),
            cfg_path: dir.path().join("Example.cfg"),
            category: "example".to_string(),
            expected_states: Some(1),
            expected_generated_states: Some(2),
            timeout_seconds: 3,
            notes: String::new(),
        };

        let run = plan_tla2_run(
            &spec,
            "llvm2",
            7,
            dir.path(),
            &PathBuf::from("target/user/release/tla2"),
            &BTreeMap::new(),
            &dir.path().join("Example"),
        )
        .unwrap();

        assert_eq!(run.mode, "llvm2");
        assert_eq!(run.run_index, 7);
        assert!(run
            .command
            .argv
            .ends_with(&["--backend".to_string(), "llvm2".to_string()]));
        assert_eq!(
            run.command
                .env_overrides
                .get("TLA2_LLVM2")
                .map(String::as_str),
            Some("1")
        );
        assert!(run.artifact_dir.ends_with("llvm2-run7"));
        assert!(run.artifact_dir.join("command.json").is_file());
    }
}
