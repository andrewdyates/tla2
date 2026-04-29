// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use regex::Regex;
use serde::Serialize;
use serde_json::json;

use super::PreparedSupremacy;
use crate::cli_schema::SupremacyOutputFormat;

const COFFEECAN_SAFETY_SPEC_NAME: &str = "CoffeeCan1000BeansSafety";
const COFFEECAN_SAFETY_BEANS: usize = 1000;
const STRICT_SELFTEST_ENV: &str = "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST";
const STRICT_NATIVE_FUSED_ENV: &str = "TLA2_LLVM2_NATIVE_FUSED_STRICT";
const POST_RA_CONTAINMENT_ENV: &str = "TLA2_LLVM2_DISABLE_POST_RA_OPT";
const DEFAULT_BINARY: &str = "target/user/release/tla2";

const FLAT_PRIMARY_REBUILD_MARKER: &str =
    "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: \
     reason=flat_state_primary layout promotion";

const LLVM2_SMOKE_ENV: &[(&str, &str)] = &[
    ("TLA2_LLVM2", "1"),
    ("TLA2_LLVM2_BFS", "1"),
    ("TLA2_LLVM2_EXISTS", "1"),
    ("TLA2_COMPILED_BFS", "1"),
    ("TLA2_FLAT_BFS", "1"),
    ("TLA2_BYTECODE_VM", "1"),
    ("TLA2_BYTECODE_VM_STATS", "1"),
    ("TLA2_AUTO_POR", "0"),
    ("TLA2_SKIP_LIVENESS", "1"),
    ("TLA2_DISABLE_ARTIFACT_CACHE", "1"),
    ("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP", "1"),
    (STRICT_SELFTEST_ENV, "strict"),
    (STRICT_NATIVE_FUSED_ENV, "1"),
    ("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", "O3"),
    ("TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL", "O3"),
    (POST_RA_CONTAINMENT_ENV, "0"),
];

const COMMON_REQUIRED_SUBSTRINGS: &[&str] = &[
    "Search completeness: bounded",
    "[llvm2] LLVM2 native compilation enabled (TLA2_LLVM2=1)",
    "[llvm2] CompiledBfsStep built:",
    "llvm2_bfs_level_active=true",
    "llvm2_native_fused_level_active=true",
    "llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop",
    "llvm2_native_fused_regular_invariants_checked=true",
    "[compiled-bfs] activating compiled BFS loop",
    "flat_state_primary=true",
    "flat_bfs_frontier_active=true",
    "[llvm2-selftest] native fused callout selftest complete",
];

const COMMON_FORBIDDEN_SUBSTRINGS: &[&str] = &[
    "CompiledBfsStep not eligible",
    "CompiledBfsStep requested interpreter fallback",
    "requested interpreter fallback",
    "native fused CompiledBfsLevel unavailable",
    "compiled BFS fallback",
    "compiled BFS requested interpreter fallback",
    "compiled BFS disabled",
    "compiled BFS step available but not enabled",
    "fused level error",
    "step error",
    "native fused fallback",
    "native fused requested interpreter fallback",
    "falling back to prototype",
    "prototype Rust parent loop",
    "compiled_bfs_step_active=false",
    "compiled_bfs_level_active=false",
    "llvm2_native_fused_level_active=false",
    "llvm2_native_fused_regular_invariants_checked=false",
    "llvm2_native_fused_mode=action_only",
    "flat_state_primary=false",
    "flat_bfs_frontier_active=false",
    "native fused CompiledBfsLevel using action-only fallback",
    "native fused level checks invariants in Rust after flat dedup",
    "state constraints require LLVM2 native fused constraint support",
    "state constraints require native fused constraint pruning",
    "native fused CompiledBfsLevel not eligible for state constraints",
    "native fused level does not report active state constraints",
    "constrained native fused BFS not eligible",
    "state constraints missing native entries",
    "failed to compile action",
    "failed to compile invariant",
    "failed to compile state constraint",
    "missing bytecode for state constraint",
    "missing native code",
    "unsupported opcode for tMIR backend",
    "register allocation failed",
    "native BFS level generation is blocked",
];

const COMMON_FORBIDDEN_FULL_OUTPUT_SUBSTRINGS: &[&str] = &[
    "[llvm2-selftest] native fused callout selftest failed",
    "[llvm2-selftest] failing closed",
];

#[derive(Clone)]
struct SmokeSpec {
    name: &'static str,
    tla_path: Cow<'static, str>,
    cfg_path: Cow<'static, str>,
    bound_args: &'static [&'static str],
    native_fused_action_count: usize,
    native_fused_invariant_count: usize,
    required_substrings: &'static [&'static str],
    native_fused_state_constraint_count: Option<usize>,
    native_fused_mode: &'static str,
    native_fused_loop_label: &'static str,
    min_transitions: usize,
    expected_native_state_len: Option<usize>,
}

impl SmokeSpec {
    fn absolute_paths(&self, examples_dir: &Path) -> (PathBuf, PathBuf) {
        let tla_path = Path::new(self.tla_path.as_ref());
        let cfg_path = Path::new(self.cfg_path.as_ref());
        let tla_path = if tla_path.is_absolute() {
            tla_path.to_path_buf()
        } else {
            examples_dir.join(tla_path)
        };
        let cfg_path = if cfg_path.is_absolute() {
            cfg_path.to_path_buf()
        } else {
            examples_dir.join(cfg_path)
        };
        (tla_path, cfg_path)
    }
}

#[derive(Serialize)]
struct CommandResult {
    argv: Vec<String>,
    cwd: String,
    returncode: i32,
    elapsed_seconds: f64,
    stdout: String,
    stderr: String,
    env_overrides: BTreeMap<String, String>,
}

#[derive(Serialize)]
struct SmokeRun {
    spec: String,
    artifact_dir: String,
    returncode: i32,
    elapsed_seconds: f64,
    failures: Vec<String>,
    command: Vec<String>,
    cwd: String,
    env_overrides: BTreeMap<String, String>,
    stderr_tail: Vec<String>,
    compiled_bfs_level_loop_initial_states: Option<usize>,
    compiled_bfs_level_loop_fused: Option<bool>,
    compiled_bfs_levels_completed: Option<usize>,
    compiled_bfs_parents_processed: Option<usize>,
    compiled_bfs_successors_generated: Option<usize>,
    compiled_bfs_successors_new: Option<usize>,
    compiled_bfs_total_states: Option<usize>,
    ok: bool,
}

pub(super) fn run_smoke(prepared: PreparedSupremacy) -> Result<()> {
    if prepared.timeout_seconds == 0 {
        bail!("--timeout must be >= 1");
    }
    let repo_root = env::current_dir().context("resolve current working directory")?;
    let examples_dir = tlaplus_examples_dir()?;
    let binary = resolve_binary(&repo_root, prepared.tla2_bin.as_deref())?;
    let env_overrides = smoke_env_with_overrides(&prepared.env_overrides)?;
    let timeout = Duration::from_secs(prepared.timeout_seconds);

    let mut runs = Vec::new();
    for spec_name in &prepared.specs {
        let spec =
            smoke_spec(spec_name).with_context(|| format!("unknown smoke spec {spec_name:?}"))?;
        let preview = build_check_command(&binary, &spec, &examples_dir);
        print_smoke_start(&prepared, &spec, &preview);
        let run = run_spec(
            spec.clone(),
            &binary,
            timeout,
            &prepared.output_dir,
            &repo_root,
            &examples_dir,
            &env_overrides,
        )?;
        print_smoke_result(&spec, &run);
        runs.push(run);
    }

    let summary = json!({
        "schema": "tla2.llvm2_native_fused_smoke.summary.v1",
        "timestamp": chrono::Local::now().format("%Y-%m-%dT%H%M%S").to_string(),
        "binary": binary,
        "artifact_bundle": repo_relative(&repo_root, &prepared.output_dir),
        "env_overrides": env_overrides,
        "runs": runs,
    });
    let summary_json = serde_json::to_string_pretty(&summary).context("serialize smoke summary")?;
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
        SupremacyOutputFormat::Human => {
            eprintln!(
                "[llvm2-native-fused-smoke] wrote {}",
                prepared.output_dir.display()
            );
        }
        SupremacyOutputFormat::Json => println!("{}", summary),
        SupremacyOutputFormat::Markdown => println!("{markdown}"),
    }

    let any_failed = summary
        .get("runs")
        .and_then(|runs| runs.as_array())
        .is_some_and(|runs| runs.iter().any(|run| run.get("ok") != Some(&json!(true))));
    if any_failed {
        bail!(
            "tla2 supremacy smoke failed; see {}",
            prepared.output_dir.display()
        );
    }
    Ok(())
}

fn smoke_specs() -> &'static [SmokeSpec] {
    &[
        SmokeSpec {
            name: COFFEECAN_SAFETY_SPEC_NAME,
            tla_path: Cow::Borrowed("generated-stage/CoffeeCanSafetyBench.tla"),
            cfg_path: Cow::Borrowed("generated-stage/CoffeeCanSafetyBench.cfg"),
            bound_args: &["--max-depth", "1"],
            native_fused_action_count: 4,
            native_fused_invariant_count: 1,
            native_fused_state_constraint_count: Some(0),
            expected_native_state_len: Some(2),
            native_fused_mode: "invariant_checking",
            native_fused_loop_label: "invariant-checking native fused LLVM2 parent loop",
            required_substrings: &[
                "Model checking stopped: depth limit reached.",
                "Max depth: 1",
                "States found: 2001",
                "Initial states: 1001",
                "Transitions: 2997",
                "[llvm2] executable action coverage: llvm2_actions_compiled=4 llvm2_actions_total=4",
                "[llvm2] compilation complete: 4/4 actions, 1/1 invariants",
            ],
            min_transitions: 1,
        },
        SmokeSpec {
            name: "EWD998Small",
            tla_path: Cow::Borrowed("ewd998/EWD998.tla"),
            cfg_path: Cow::Borrowed("ewd998/EWD998Small.cfg"),
            bound_args: &["--max-depth", "3"],
            native_fused_action_count: 15,
            native_fused_invariant_count: 3,
            native_fused_state_constraint_count: Some(1),
            expected_native_state_len: Some(15),
            native_fused_mode: "state_constraint_checking",
            native_fused_loop_label: "state-constrained native fused LLVM2 parent loop",
            required_substrings: &[
                "Model checking stopped: depth limit reached.",
                "Max depth: 3",
                "States found: 9404",
                "[llvm2] executable action coverage: llvm2_actions_compiled=15 llvm2_actions_total=15",
                "[llvm2] compilation complete: 15/15 actions, 3/3 invariants, 1/1 state constraints compiled",
            ],
            min_transitions: 1,
        },
        SmokeSpec {
            name: "MCLamportMutex",
            tla_path: Cow::Borrowed("lamport_mutex/MCLamportMutex.tla"),
            cfg_path: Cow::Borrowed("lamport_mutex/MCLamportMutex.cfg"),
            bound_args: &["--max-depth", "1"],
            native_fused_action_count: 27,
            native_fused_invariant_count: 3,
            native_fused_state_constraint_count: Some(1),
            expected_native_state_len: Some(89),
            native_fused_mode: "state_constraint_checking",
            native_fused_loop_label: "state-constrained native fused LLVM2 parent loop",
            required_substrings: &[
                "Model checking stopped: depth limit reached.",
                "Max depth: 1",
                "States found: 4",
                "Transitions: 3",
                "[llvm2] executable action coverage: llvm2_actions_compiled=27 llvm2_actions_total=27",
                "[llvm2] compilation complete: 27/27 actions, 3/3 invariants, 1/1 state constraints compiled",
            ],
            min_transitions: 0,
        },
    ]
}

fn smoke_spec(name: &str) -> Option<SmokeSpec> {
    smoke_specs().iter().find(|spec| spec.name == name).cloned()
}

fn tlaplus_examples_dir() -> Result<PathBuf> {
    let home = env::var_os("HOME").context("HOME is not set")?;
    Ok(PathBuf::from(home).join("tlaplus-examples/specifications"))
}

fn resolve_binary(repo_root: &Path, explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(binary) = explicit {
        if binary.is_file() {
            return Ok(binary.to_path_buf());
        }
        bail!("tla2 binary not found: {}", binary.display());
    }
    let binary = repo_root.join(DEFAULT_BINARY);
    if binary.is_file() {
        return Ok(binary);
    }
    bail!(
        "release benchmark binary not found: {}\nBuild it with:\n  ./andrewdyates_scripts/bin/cargo build --profile release -p tla-cli --features llvm2 --target-dir target/user --bin tla2\nor pass --tla2-bin /path/to/tla2",
        binary.display()
    );
}

fn smoke_env_with_overrides(
    cli_overrides: &BTreeMap<String, String>,
) -> Result<BTreeMap<String, String>> {
    let mut env: BTreeMap<String, String> = LLVM2_SMOKE_ENV
        .iter()
        .map(|(key, value)| ((*key).to_string(), (*value).to_string()))
        .collect();
    env.extend(cli_overrides.clone());
    require_env_value(&env, "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", "O3")?;
    require_env_value(&env, "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL", "O3")?;
    require_env_value(&env, POST_RA_CONTAINMENT_ENV, "0")?;
    require_env_value(&env, STRICT_NATIVE_FUSED_ENV, "1")?;
    require_env_value(&env, "TLA2_DISABLE_ARTIFACT_CACHE", "1")?;
    require_env_value(&env, "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP", "1")?;
    Ok(env)
}

fn require_env_value(env: &BTreeMap<String, String>, key: &str, value: &str) -> Result<()> {
    if env.get(key).map(String::as_str) != Some(value) {
        bail!("native fused smoke requires {key}={value}");
    }
    Ok(())
}

fn build_check_command(binary: &Path, spec: &SmokeSpec, examples_dir: &Path) -> Vec<String> {
    let (tla_path, cfg_path) = spec.absolute_paths(examples_dir);
    let mut argv = vec![
        binary.display().to_string(),
        "check".to_string(),
        tla_path.display().to_string(),
        "--config".to_string(),
        cfg_path.display().to_string(),
        "--workers".to_string(),
        "1".to_string(),
        "--force".to_string(),
    ];
    argv.extend(spec.bound_args.iter().map(|arg| (*arg).to_string()));
    argv.extend(["--backend".to_string(), "llvm2".to_string()]);
    argv
}

fn print_smoke_start(prepared: &PreparedSupremacy, spec: &SmokeSpec, command: &[String]) {
    if matches!(prepared.format, SupremacyOutputFormat::Human) {
        eprintln!(
            "[llvm2-native-fused-smoke] {}: {}",
            spec.name,
            shell_join(command)
        );
    }
}

fn print_smoke_result(spec: &SmokeSpec, run: &SmokeRun) {
    let status = if run.ok { "PASS" } else { "FAIL" };
    eprintln!(
        "[llvm2-native-fused-smoke] {}: {} ({})",
        spec.name, status, run.artifact_dir
    );
    for failure in &run.failures {
        eprintln!("  - {failure}");
    }
}

fn run_spec(
    mut spec: SmokeSpec,
    binary: &Path,
    timeout: Duration,
    output_dir: &Path,
    repo_root: &Path,
    examples_dir: &Path,
    env_overrides: &BTreeMap<String, String>,
) -> Result<SmokeRun> {
    let spec_dir = output_dir.join(spec.name);
    fs::create_dir_all(&spec_dir).with_context(|| format!("create {}", spec_dir.display()))?;

    if spec.name == COFFEECAN_SAFETY_SPEC_NAME {
        match stage_coffecan_safety_spec(&spec_dir, examples_dir) {
            Ok(staged) => spec = staged,
            Err(err) => {
                let command = build_check_command(binary, &spec, examples_dir);
                let result = CommandResult {
                    argv: command.clone(),
                    cwd: repo_root.display().to_string(),
                    returncode: 1,
                    elapsed_seconds: 0.0,
                    stdout: String::new(),
                    stderr: err.to_string(),
                    env_overrides: env_overrides.clone(),
                };
                write_artifacts(&spec_dir, &result)?;
                return Ok(smoke_run_from_failure(
                    &spec,
                    &spec_dir,
                    repo_root,
                    result,
                    vec![err.to_string()],
                ));
            }
        }
    }

    let command = build_check_command(binary, &spec, examples_dir);
    let file_failures = validate_spec_files(&spec, examples_dir);
    if !file_failures.is_empty() {
        let result = CommandResult {
            argv: command,
            cwd: repo_root.display().to_string(),
            returncode: 1,
            elapsed_seconds: 0.0,
            stdout: String::new(),
            stderr: file_failures.join("\n"),
            env_overrides: env_overrides.clone(),
        };
        write_artifacts(&spec_dir, &result)?;
        return Ok(smoke_run_from_failure(
            &spec,
            &spec_dir,
            repo_root,
            result,
            file_failures,
        ));
    }

    let result = match run_command(command.clone(), repo_root, timeout, env_overrides) {
        Ok(result) => result,
        Err(err) => CommandResult {
            argv: command,
            cwd: repo_root.display().to_string(),
            returncode: 1,
            elapsed_seconds: 0.0,
            stdout: String::new(),
            stderr: err.to_string(),
            env_overrides: env_overrides.clone(),
        },
    };
    write_artifacts(&spec_dir, &result)?;
    let mut failures = validate_output(&spec, &result.stdout, &result.stderr);
    if result.returncode != 0 {
        failures.insert(0, format!("command exited with {}", result.returncode));
    }
    Ok(smoke_run_from_result(
        &spec, &spec_dir, repo_root, result, failures,
    ))
}

fn stage_coffecan_safety_spec(spec_dir: &Path, examples_dir: &Path) -> Result<SmokeSpec> {
    let generated_dir = spec_dir.join("generated-specs").join("CoffeeCanSafety1000");
    fs::create_dir_all(&generated_dir)
        .with_context(|| format!("create {}", generated_dir.display()))?;
    let source = examples_dir.join("CoffeeCan/CoffeeCan.tla");
    if !source.is_file() {
        bail!("CoffeeCan source not found: {}", source.display());
    }
    fs::copy(&source, generated_dir.join("CoffeeCan.tla"))
        .with_context(|| format!("copy {}", source.display()))?;
    let wrapper_tla = generated_dir.join("CoffeeCanSafetyBench.tla");
    let wrapper_cfg = generated_dir.join("CoffeeCanSafetyBench.cfg");
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
    Ok(SmokeSpec {
        tla_path: Cow::Owned(wrapper_tla.to_string_lossy().into_owned()),
        cfg_path: Cow::Owned(wrapper_cfg.to_string_lossy().into_owned()),
        ..smoke_spec(COFFEECAN_SAFETY_SPEC_NAME).expect("CoffeeCan smoke spec")
    })
}

fn validate_spec_files(spec: &SmokeSpec, examples_dir: &Path) -> Vec<String> {
    let (tla_path, cfg_path) = spec.absolute_paths(examples_dir);
    let mut failures = Vec::new();
    if !tla_path.is_file() {
        failures.push(format!("TLA file not found: {}", tla_path.display()));
    }
    if !cfg_path.is_file() {
        failures.push(format!("config file not found: {}", cfg_path.display()));
    }
    failures
}

fn run_command(
    argv: Vec<String>,
    repo_root: &Path,
    timeout: Duration,
    env_overrides: &BTreeMap<String, String>,
) -> Result<CommandResult> {
    let started = Instant::now();
    let mut command = Command::new(&argv[0]);
    command
        .args(&argv[1..])
        .current_dir(repo_root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command.env_clear();
    for (key, value) in env::vars_os() {
        if !key.to_string_lossy().starts_with("TLA2_") {
            command.env(key, value);
        }
    }
    command.envs(env_overrides);
    let mut child = command
        .spawn()
        .with_context(|| format!("spawn {}", shell_join(&argv)))?;
    let stdout = child.stdout.take();
    let stderr = child.stderr.take();
    let stdout_handle = stdout.map(|mut stream| {
        thread::spawn(move || {
            let mut text = String::new();
            let _ = stream.read_to_string(&mut text);
            text
        })
    });
    let stderr_handle = stderr.map(|mut stream| {
        thread::spawn(move || {
            let mut text = String::new();
            let _ = stream.read_to_string(&mut text);
            text
        })
    });

    let mut timed_out = false;
    let status = loop {
        if let Some(status) = child.try_wait().context("poll smoke subprocess")? {
            break status;
        }
        if started.elapsed() >= timeout {
            timed_out = true;
            let _ = child.kill();
            break child.wait().context("wait for killed smoke subprocess")?;
        }
        thread::sleep(Duration::from_millis(100));
    };

    let stdout = join_reader(stdout_handle);
    let mut stderr = join_reader(stderr_handle);
    let elapsed_seconds = started.elapsed().as_secs_f64();
    let returncode = if timed_out {
        if stderr.is_empty() {
            stderr = format!("Timeout after {} seconds", timeout.as_secs());
        } else {
            stderr.push_str(&format!("\n\nTimeout after {} seconds", timeout.as_secs()));
        }
        124
    } else {
        status.code().unwrap_or(1)
    };

    Ok(CommandResult {
        argv,
        cwd: repo_root.display().to_string(),
        returncode,
        elapsed_seconds,
        stdout,
        stderr,
        env_overrides: env_overrides.clone(),
    })
}

fn join_reader(handle: Option<thread::JoinHandle<String>>) -> String {
    handle
        .and_then(|handle| handle.join().ok())
        .unwrap_or_default()
}

fn write_artifacts(output_dir: &Path, result: &CommandResult) -> Result<()> {
    fs::write(output_dir.join("stdout.txt"), &result.stdout)
        .with_context(|| format!("write {}", output_dir.join("stdout.txt").display()))?;
    fs::write(output_dir.join("stderr.txt"), &result.stderr)
        .with_context(|| format!("write {}", output_dir.join("stderr.txt").display()))?;
    fs::write(
        output_dir.join("command.json"),
        serde_json::to_string_pretty(result).context("serialize smoke command")? + "\n",
    )
    .with_context(|| format!("write {}", output_dir.join("command.json").display()))?;
    Ok(())
}

fn smoke_run_from_failure(
    spec: &SmokeSpec,
    spec_dir: &Path,
    repo_root: &Path,
    result: CommandResult,
    failures: Vec<String>,
) -> SmokeRun {
    smoke_run_from_result(spec, spec_dir, repo_root, result, failures)
}

fn smoke_run_from_result(
    spec: &SmokeSpec,
    spec_dir: &Path,
    repo_root: &Path,
    result: CommandResult,
    failures: Vec<String>,
) -> SmokeRun {
    let combined = format!("{}\n{}", result.stdout, result.stderr);
    let backend_segment = latest_flat_primary_backend_segment(&combined);
    let rebuild_segment = latest_flat_primary_rebuild_segment(&backend_segment);
    let loop_start = compiled_bfs_loop_start(&rebuild_segment);
    let completion = compiled_bfs_completion(&rebuild_segment);
    let ok = result.returncode == 0 && failures.is_empty();
    SmokeRun {
        spec: spec.name.to_string(),
        artifact_dir: repo_relative(repo_root, spec_dir),
        returncode: result.returncode,
        elapsed_seconds: result.elapsed_seconds,
        failures,
        command: result.argv,
        cwd: result.cwd,
        env_overrides: result.env_overrides,
        stderr_tail: evidence_tail(&result.stderr),
        compiled_bfs_level_loop_initial_states: loop_start.map(|value| value.0),
        compiled_bfs_level_loop_fused: loop_start.map(|value| value.1),
        compiled_bfs_levels_completed: completion.map(|value| value.0),
        compiled_bfs_parents_processed: completion.map(|value| value.1),
        compiled_bfs_successors_generated: completion.map(|value| value.2),
        compiled_bfs_successors_new: completion.map(|value| value.3),
        compiled_bfs_total_states: completion.map(|value| value.4),
        ok,
    }
}

fn validate_output(spec: &SmokeSpec, stdout: &str, stderr: &str) -> Vec<String> {
    let combined = format!("{stdout}\n{stderr}");
    let backend_segment = latest_flat_primary_backend_segment(&combined);
    let rebuild_segment = latest_flat_primary_rebuild_segment(&backend_segment);
    let final_summary = final_summary_segment(&combined);
    let mut failures = Vec::new();
    let state_constrained = spec.native_fused_state_constraint_count.unwrap_or(0) > 0;
    let state_constrained_proven = proves_state_constrained_native_fused(spec, &rebuild_segment);

    if !backend_segment.contains(FLAT_PRIMARY_REBUILD_MARKER) {
        failures.push(format!(
            "missing flat-primary rebuild marker required for strict validation: {:?}",
            FLAT_PRIMARY_REBUILD_MARKER
        ));
    }

    for needle in required_needles(spec, state_constrained) {
        if requires_final_summary_result_line(&needle) {
            if Some(needle.trim()) != final_summary_result_line(&final_summary).as_deref() {
                failures.push(format!("missing required substring: {needle:?}"));
            }
            continue;
        }
        if let Some(label) = required_final_summary_count_label(&needle) {
            if Some(needle.trim()) != final_summary_count_line(&final_summary, label).as_deref() {
                failures.push(format!("missing required substring: {needle:?}"));
            }
            continue;
        }
        let haystack =
            required_substring_haystack(&needle, &combined, &backend_segment, &rebuild_segment);
        if !haystack.contains(&needle) {
            failures.push(format!("missing required substring: {needle:?}"));
        }
    }

    validate_compiled_loop(&rebuild_segment, &final_summary, &mut failures);
    failures.extend(forbidden_substring_failures(
        &backend_segment,
        state_constrained_proven,
    ));
    for needle in COMMON_FORBIDDEN_FULL_OUTPUT_SUBSTRINGS {
        if combined.contains(needle) {
            failures.push(format!("found forbidden substring: {needle:?}"));
        }
    }
    validate_selftest(spec, &rebuild_segment, &mut failures);
    validate_level_counts(spec, &rebuild_segment, &mut failures);
    validate_state_constraint_skip(spec, &rebuild_segment, state_constrained, &mut failures);
    validate_exact_telemetry(spec, &rebuild_segment, state_constrained, &mut failures);
    validate_forbidden_patterns(&backend_segment, &rebuild_segment, &mut failures);
    validate_transition_floor(spec, &final_summary, &mut failures);
    validate_flat_frontier(&rebuild_segment, &mut failures);
    failures
}

fn required_needles(spec: &SmokeSpec, state_constrained: bool) -> Vec<String> {
    let mut needles = Vec::new();
    needles.extend(
        COMMON_REQUIRED_SUBSTRINGS
            .iter()
            .copied()
            .filter(|needle| !state_constrained || *needle != "[llvm2] CompiledBfsStep built:")
            .map(str::to_string),
    );
    needles.push(format!(
        "CompiledBfsLevel built ({})",
        spec.native_fused_loop_label
    ));
    needles.push(format!(
        "llvm2_native_fused_mode={}",
        spec.native_fused_mode
    ));
    needles.extend(
        spec.required_substrings
            .iter()
            .map(|needle| (*needle).to_string()),
    );
    needles
}

fn required_substring_haystack<'a>(
    needle: &str,
    combined: &'a str,
    backend_segment: &'a str,
    rebuild_segment: &'a str,
) -> &'a str {
    if needle.starts_with("[llvm2] LLVM2 native compilation enabled") {
        combined
    } else if needle.starts_with("[llvm2-selftest]")
        || needle.starts_with("[compiled-bfs]")
        || needle.starts_with("compiled_bfs_")
        || needle.starts_with("flat_bfs_")
        || needle.starts_with("llvm2_bfs_level_")
        || needle.starts_with("llvm2_native_fused_")
        || needle.starts_with("[llvm2]")
    {
        rebuild_segment
    } else if needle.starts_with("flat_state_primary") {
        backend_segment
    } else {
        combined
    }
}

fn validate_compiled_loop(rebuild_segment: &str, final_summary: &str, failures: &mut Vec<String>) {
    let final_transitions = final_summary_count(final_summary, "Transitions");
    let final_states = final_summary_count(final_summary, "States found");
    match compiled_bfs_loop_start(rebuild_segment) {
        Some((initial_states, fused)) => {
            if initial_states == 0 {
                failures.push(format!(
                    "compiled BFS level loop started without initial work (initial_states={initial_states})"
                ));
            }
            if !fused {
                failures.push("compiled BFS level loop start was not fused".to_string());
            }
        }
        None => failures.push(
            "missing required substring: '[compiled-bfs] starting compiled BFS level loop'"
                .to_string(),
        ),
    }
    match compiled_bfs_completion(rebuild_segment) {
        Some((levels, parents, generated, new, total_states)) => {
            if levels == 0 || parents == 0 || generated == 0 || total_states == 0 {
                failures.push(format!(
                    "compiled BFS loop completed without positive native-fused work \
                     (levels={levels}, parents={parents}, generated={generated}, total_states={total_states})"
                ));
            }
            if new == 0 {
                failures.push(format!(
                    "compiled BFS loop completed with zero new states (new={new}, total_states={total_states})"
                ));
            }
            if final_states.is_some_and(|states| states != total_states) {
                failures.push(format!(
                    "compiled BFS total_states did not match final States found \
                     (total_states={total_states}, states_found={})",
                    final_states.unwrap_or_default()
                ));
            }
            if final_transitions.is_some_and(|transitions| transitions != generated) {
                failures.push(format!(
                    "compiled BFS generated successors did not match final Transitions \
                     (generated={generated}, transitions={})",
                    final_transitions.unwrap_or_default()
                ));
            }
        }
        None => {
            failures.push("missing required substring: '[compiled-bfs] completed:'".to_string())
        }
    }
    let (nanos, seconds) = compiled_bfs_execution_timing(rebuild_segment);
    if !seconds.is_some_and(|seconds| seconds > 0.0) && !nanos.is_some_and(|nanos| nanos > 0) {
        failures.push(format!(
            "compiled BFS execution timing telemetry was missing or non-positive \
             (compiled_bfs_execution_seconds={seconds:?}, compiled_bfs_execution_nanos={nanos:?})"
        ));
    }
}

fn validate_selftest(spec: &SmokeSpec, rebuild_segment: &str, failures: &mut Vec<String>) {
    for (description, pattern) in strict_selftest_marker_patterns(spec) {
        if !pattern.is_match(rebuild_segment) {
            failures.push(format!(
                "missing strict native callout selftest marker: {description}"
            ));
        }
    }
    let missing_expected = Regex::new(r"\bmissing_expected=(\d[\d,]*)\b").unwrap();
    for captures in missing_expected.captures_iter(rebuild_segment) {
        let missing = parse_usize(&captures[1]).unwrap_or_default();
        if missing > 0 {
            failures.push(format!(
                "native fused callout selftest reported missing expected callouts: missing_expected={missing}"
            ));
        }
    }
    failures.extend(strict_selftest_false_result_failures(rebuild_segment));
}

fn validate_level_counts(spec: &SmokeSpec, rebuild_segment: &str, failures: &mut Vec<String>) {
    match compiled_bfs_level_built_counts(rebuild_segment, spec.native_fused_loop_label) {
        Some((actions, invariants, state_len)) => {
            if actions != spec.native_fused_action_count
                || invariants != spec.native_fused_invariant_count
            {
                failures.push(format!(
                    "CompiledBfsLevel built counts did not match expected spec counts: \
                     expected actions={}, invariants={}; observed actions={actions}, invariants={invariants}",
                    spec.native_fused_action_count, spec.native_fused_invariant_count
                ));
            }
            if spec.expected_native_state_len.is_some()
                && state_len != spec.expected_native_state_len
            {
                failures.push(format!(
                    "CompiledBfsLevel built state_len did not match expected spec state length: \
                     expected state_len={}; observed state_len={state_len:?}",
                    spec.expected_native_state_len.unwrap_or_default()
                ));
            }
        }
        None => failures.push(format!(
            "missing exact CompiledBfsLevel built counts: actions={}, invariants={}",
            spec.native_fused_action_count, spec.native_fused_invariant_count
        )),
    }
}

fn validate_state_constraint_skip(
    spec: &SmokeSpec,
    rebuild_segment: &str,
    state_constrained: bool,
    failures: &mut Vec<String>,
) {
    if !state_constrained {
        return;
    }
    let mut saw_expected_skip = false;
    for line in rebuild_segment.lines() {
        if is_allowed_state_constraint_step_skip(line) {
            saw_expected_skip = true;
        }
        if line.contains("CompiledBfsStep not eligible")
            && !is_allowed_state_constraint_step_skip(line)
        {
            failures.push(format!(
                "found non-state-constraint CompiledBfsStep ineligibility: {line:?}"
            ));
        }
        if line.contains("state constraints require native fused constraint pruning")
            && !is_allowed_state_constraint_step_skip(line)
        {
            failures.push(format!(
                "found state-constraint pruning text outside the allowed CompiledBfsStep diagnostic: {line:?}"
            ));
        }
    }
    if !saw_expected_skip {
        failures.push(format!(
            "missing exact state-constraint step skip diagnostic: {:?}",
            "[llvm2] CompiledBfsStep not eligible: state constraints require native fused constraint pruning"
        ));
    }
    if !proves_state_constrained_native_fused(spec, rebuild_segment) {
        failures.push("missing state-constrained native-fused proof telemetry".to_string());
    }
}

fn validate_exact_telemetry(
    spec: &SmokeSpec,
    rebuild_segment: &str,
    state_constrained: bool,
    failures: &mut Vec<String>,
) {
    let mut expected = vec![
        (
            "llvm2_native_fused_mode",
            spec.native_fused_mode.to_string(),
        ),
        (
            "llvm2_native_fused_invariant_count",
            spec.native_fused_invariant_count.to_string(),
        ),
        ("llvm2_native_fused_local_dedup", "false".to_string()),
        (
            "compiled_bfs_step_active",
            if state_constrained { "false" } else { "true" }.to_string(),
        ),
        ("compiled_bfs_level_active", "true".to_string()),
    ];
    if let Some(count) = spec.native_fused_state_constraint_count {
        expected.push((
            "llvm2_native_fused_state_constraint_count",
            count.to_string(),
        ));
    }
    for (key, value) in expected {
        if !has_exact_telemetry(rebuild_segment, key, &value) {
            failures.push(format!("missing exact telemetry: {key}={value}"));
        }
    }
    if has_exact_telemetry(rebuild_segment, "llvm2_native_fused_local_dedup", "true") {
        failures.push(
            "native fused telemetry reported local dedup enabled despite launch env: \
             llvm2_native_fused_local_dedup=true"
                .to_string(),
        );
    }
    if rebuild_segment
        .lines()
        .any(|line| line.contains("[llvm2-native-bfs]") && line.contains("local_dedup=true"))
    {
        failures.push(
            "native BFS trace reported local dedup enabled despite launch env: local_dedup=true"
                .to_string(),
        );
    }
}

fn validate_forbidden_patterns(
    backend_segment: &str,
    rebuild_segment: &str,
    failures: &mut Vec<String>,
) {
    let patterns = [
        Regex::new(r"\b[1-9]\d*\s+fallback\b").unwrap(),
        Regex::new(
            r"(?i)\bcompiled[- ]bfs\b.*\b(fallback|falling back|error|failed|disabled|disabling|not enabled|became unavailable|interpreter path used)\b",
        )
        .unwrap(),
        Regex::new(r"(?i)\bnative[- ]fused\b.*\bfallback\b").unwrap(),
        Regex::new(r"(?i)\bper[- ]parent\b.*\bfallback\b").unwrap(),
        Regex::new(r"(?i)\brequested interpreter fallback\b").unwrap(),
    ];
    for pattern in patterns {
        if let Some(matched) = pattern.find(backend_segment) {
            failures.push(format!(
                "matched forbidden pattern {:?}: {:?}",
                pattern.as_str(),
                matched.as_str()
            ));
        }
    }
    let level_blocker = Regex::new(
        r"(?i)\b(?:CompiledBfsLevel\b.*\b(requested interpreter fallback|falling back|not eligible|skipped|fallback)\b|(requested interpreter fallback|falling back|not eligible|skipped|fallback)\b.*\bCompiledBfsLevel\b)",
    )
    .unwrap();
    for line in rebuild_segment.lines() {
        if let Some(captures) = level_blocker.captures(line) {
            let blocker = captures
                .get(1)
                .or_else(|| captures.get(2))
                .map(|m| m.as_str())
                .unwrap_or("blocker");
            failures.push(format!(
                "found post-rebuild CompiledBfsLevel blocker: {blocker:?}: {line:?}"
            ));
        }
    }
    let zero_work = Regex::new(
        r"(?i)\[compiled-bfs\]\s+completed:\s+0\s+levels,\s+0\s+parents,\s+0\s+generated,\s+0\s+new\b",
    )
    .unwrap();
    if let Some(matched) = zero_work.find(rebuild_segment) {
        failures.push(format!(
            "compiled BFS loop completed without processing work: {:?}",
            matched.as_str()
        ));
    }
}

fn validate_transition_floor(spec: &SmokeSpec, final_summary: &str, failures: &mut Vec<String>) {
    if spec.min_transitions == 0 {
        return;
    }
    match final_summary_count(final_summary, "Transitions") {
        Some(transitions) if transitions >= spec.min_transitions => {}
        Some(transitions) => failures.push(format!(
            "transition count did not exercise work: expected at least {}, observed {transitions}",
            spec.min_transitions
        )),
        None => failures.push(format!(
            "missing transition count telemetry: expected at least {}",
            spec.min_transitions
        )),
    }
}

fn validate_flat_frontier(rebuild_segment: &str, failures: &mut Vec<String>) {
    let active_lines: Vec<&str> = rebuild_segment
        .lines()
        .filter(|line| line.contains("flat_bfs_frontier_active=true"))
        .collect();
    if active_lines.is_empty() {
        failures.push("missing flat-frontier active telemetry line".to_string());
    } else if !active_lines.iter().any(|line| line.contains("0 fallback")) {
        failures
            .push("flat-frontier active telemetry line did not report zero fallback".to_string());
    }
}

fn forbidden_substring_failures(
    backend_segment: &str,
    state_constrained_native_fused_proven: bool,
) -> Vec<String> {
    let mut failures = Vec::new();
    let mut in_rebuild_segment = !backend_segment.contains(FLAT_PRIMARY_REBUILD_MARKER);
    for line in backend_segment.lines() {
        if line.contains(FLAT_PRIMARY_REBUILD_MARKER) {
            in_rebuild_segment = true;
        }
        for needle in COMMON_FORBIDDEN_SUBSTRINGS {
            if !line.contains(needle) {
                continue;
            }
            if is_allowed_state_constraint_forbidden_line(
                line,
                needle,
                in_rebuild_segment,
                state_constrained_native_fused_proven,
            ) {
                continue;
            }
            failures.push(format!("found forbidden substring: {needle:?}: {line:?}"));
        }
    }
    failures
}

fn is_allowed_state_constraint_forbidden_line(
    line: &str,
    needle: &str,
    in_rebuild_segment: bool,
    state_constrained_native_fused_proven: bool,
) -> bool {
    if !in_rebuild_segment || !state_constrained_native_fused_proven {
        return false;
    }
    match needle {
        "CompiledBfsStep not eligible"
        | "state constraints require native fused constraint pruning" => {
            is_allowed_state_constraint_step_skip(line)
        }
        "state constraints require LLVM2 native fused constraint support" => {
            is_allowed_state_constraint_fused_level_skip(line)
        }
        "compiled_bfs_step_active=false" => {
            has_exact_telemetry(line, "compiled_bfs_step_active", "false")
        }
        _ => false,
    }
}

fn strict_selftest_marker_patterns(spec: &SmokeSpec) -> Vec<(&'static str, Regex)> {
    let state_constraint_count = spec.native_fused_state_constraint_count.unwrap_or(0);
    let state_len = spec
        .expected_native_state_len
        .map(|value| value.to_string())
        .unwrap_or_else(|| r"\d+".to_string());
    vec![
        (
            "prepared native fused callout selftest",
            Regex::new(&format!(
                r"\[llvm2-selftest\]\s+prepared native fused callout selftest:\s+actions={},\s+state_constraints={},\s+invariants={},\s+missing_expected=0,\s+fail_closed=true\b",
                spec.native_fused_action_count,
                state_constraint_count,
                spec.native_fused_invariant_count
            ))
            .unwrap(),
        ),
        (
            "running native fused callout selftest on first real parent",
            Regex::new(&format!(
                r"\[llvm2-selftest\]\s+running native fused callout selftest on first real parent:\s+state_len={},\s+actions={},\s+state_constraints={},\s+invariants={},\s+fail_closed=true\b",
                state_len,
                spec.native_fused_action_count,
                state_constraint_count,
                spec.native_fused_invariant_count
            ))
            .unwrap(),
        ),
        (
            "native fused callout selftest complete",
            Regex::new(r"\[llvm2-selftest\]\s+native fused callout selftest complete\b").unwrap(),
        ),
    ]
}

fn strict_selftest_false_result_failures(text: &str) -> Vec<String> {
    let mut failures = Vec::new();
    for line in text.lines() {
        let Some((kind, status, value)) = parse_selftest_callout_result(line) else {
            continue;
        };
        if !matches!(kind.as_str(), "invariant" | "state_constraint") {
            continue;
        }
        if status != "Ok" || value == 0 {
            failures.push(format!(
                "native fused callout selftest reported failed strict check: \
                 kind={kind} status={status} value={value} line={line:?}"
            ));
        }
    }
    failures
}

fn parse_selftest_callout_result(line: &str) -> Option<(String, String, i64)> {
    if !line.contains("[llvm2-selftest]") || !line.contains("status=") || !line.contains("value=") {
        return None;
    }
    let kv = Regex::new(r"(?:^|\s)([A-Za-z_][A-Za-z0-9_]*)=([^,\s]+)").unwrap();
    let mut kind = None;
    let mut status = None;
    let mut value = None;
    for captures in kv.captures_iter(line) {
        match &captures[1] {
            "kind" => kind = Some(captures[2].trim_end_matches(',').to_string()),
            "status" => status = Some(captures[2].trim_end_matches(',').to_string()),
            "value" => value = captures[2].trim_end_matches(',').parse::<i64>().ok(),
            _ => {}
        }
    }
    if kind.is_none() {
        let leading =
            Regex::new(r"^\s*\[llvm2-selftest\]\s+([A-Za-z_][A-Za-z0-9_]*)\s+callout\b").unwrap();
        if let Some(captures) = leading.captures(line) {
            kind = Some(captures[1].to_string());
        }
    }
    Some((kind?, status?, value?))
}

fn latest_flat_primary_backend_segment(combined: &str) -> String {
    let lines: Vec<&str> = combined.lines().collect();
    let Some(marker_line_index) = lines
        .iter()
        .rposition(|line| line.contains(FLAT_PRIMARY_REBUILD_MARKER))
    else {
        return combined.to_string();
    };
    for idx in (0..marker_line_index).rev() {
        if lines[idx].contains("flat_state_primary=true") {
            return lines[idx..].join("\n");
        }
    }
    lines[marker_line_index..].join("\n")
}

fn latest_flat_primary_rebuild_segment(backend_segment: &str) -> String {
    backend_segment
        .rfind(FLAT_PRIMARY_REBUILD_MARKER)
        .map(|idx| backend_segment[idx..].to_string())
        .unwrap_or_default()
}

fn final_summary_segment(combined: &str) -> String {
    let result = Regex::new(r"(?m)^\s*Model checking (?:complete|stopped):").unwrap();
    result
        .find_iter(combined)
        .last()
        .map(|matched| combined[matched.start()..].to_string())
        .unwrap_or_default()
}

fn requires_final_summary_result_line(needle: &str) -> bool {
    Regex::new(r"^Model checking (?:complete|stopped):.+$")
        .unwrap()
        .is_match(needle.trim())
}

fn final_summary_result_line(final_summary: &str) -> Option<String> {
    let result = Regex::new(r"^Model checking (?:complete|stopped):.+$").unwrap();
    final_summary
        .lines()
        .map(str::trim)
        .find(|line| result.is_match(line))
        .map(str::to_string)
}

fn required_final_summary_count_label(needle: &str) -> Option<&'static str> {
    for label in ["Max depth", "States found", "Initial states", "Transitions"] {
        let pattern = Regex::new(&format!(r"^{}:\s+\d[\d,]*$", regex::escape(label))).unwrap();
        if pattern.is_match(needle.trim()) {
            return Some(label);
        }
    }
    None
}

fn final_summary_count_line(final_summary: &str, label: &str) -> Option<String> {
    let prefix = format!("{label}:");
    final_summary
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with(&prefix))
        .last()
        .map(str::to_string)
}

fn final_summary_count(final_summary: &str, label: &str) -> Option<usize> {
    let line = final_summary_count_line(final_summary, label)?;
    let pattern = Regex::new(&format!(r"^{}:\s+(\d[\d,]*)$", regex::escape(label))).unwrap();
    let captures = pattern.captures(&line)?;
    parse_usize(&captures[1])
}

fn compiled_bfs_loop_start(combined: &str) -> Option<(usize, bool)> {
    let pattern = Regex::new(
        r"\[compiled-bfs\]\s+starting compiled BFS level loop \(([\d,]+) initial states in arena, fused=(true|false)\)",
    )
    .unwrap();
    let captures = pattern.captures_iter(combined).last()?;
    Some((parse_usize(&captures[1])?, &captures[2] == "true"))
}

fn compiled_bfs_completion(combined: &str) -> Option<(usize, usize, usize, usize, usize)> {
    let pattern = Regex::new(
        r"(?i)\[compiled-bfs\]\s+completed:\s+(\d[\d,]*)\s+levels,\s+(\d[\d,]*)\s+parents,\s+(\d[\d,]*)\s+generated,\s+(\d[\d,]*)\s+new,\s+(\d[\d,]*)\s+total states\b",
    )
    .unwrap();
    let captures = pattern.captures_iter(combined).last()?;
    Some((
        parse_usize(&captures[1])?,
        parse_usize(&captures[2])?,
        parse_usize(&captures[3])?,
        parse_usize(&captures[4])?,
        parse_usize(&captures[5])?,
    ))
}

fn compiled_bfs_execution_timing(combined: &str) -> (Option<usize>, Option<f64>) {
    let nanos_re = Regex::new(
        r"\b(?:compiled_bfs_execution_nanos|execution_time_ns|execution_time_nanos)\s*[:=]\s*(\d[\d,]*)\b",
    )
    .unwrap();
    let seconds_re = Regex::new(
        r"\b(?:compiled_bfs_execution_seconds|execution_time_seconds)\s*[:=]\s*(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\b",
    )
    .unwrap();
    let completion_re = Regex::new(r"(?i)\[compiled-bfs\]\s+completed:").unwrap();
    let mut nanos = None;
    let mut seconds = None;
    for line in combined.lines() {
        let timing_line =
            line.contains("[compiled-bfs]") && line.contains("compiled_bfs_execution_");
        if !timing_line && !completion_re.is_match(line) {
            continue;
        }
        for captures in nanos_re.captures_iter(line) {
            nanos = parse_usize(&captures[1]);
        }
        for captures in seconds_re.captures_iter(line) {
            seconds = captures[1].parse::<f64>().ok();
        }
    }
    (nanos, seconds)
}

fn compiled_bfs_level_built_counts(
    segment: &str,
    loop_label: &str,
) -> Option<(usize, usize, Option<usize>)> {
    let pattern = Regex::new(
        r"\[llvm2\]\s+CompiledBfsLevel built \(([^)]+)\):\s+(\d[\d,]*)\s+action instances,\s+(\d[\d,]*)\s+invariants(?:,\s+\d[\d,]*\s+state constraints)?(?:,\s+state_len=(\d[\d,]*))?\b",
    )
    .unwrap();
    let captures = pattern
        .captures_iter(segment)
        .filter(|captures| {
            captures
                .get(1)
                .is_some_and(|label| label.as_str() == loop_label)
        })
        .last()?;
    Some((
        parse_usize(&captures[2])?,
        parse_usize(&captures[3])?,
        captures
            .get(4)
            .and_then(|value| parse_usize(value.as_str())),
    ))
}

fn is_allowed_state_constraint_step_skip(line: &str) -> bool {
    let normalized = line.split_whitespace().collect::<Vec<_>>().join(" ");
    Regex::new(
        r"^\[llvm2\] CompiledBfsStep not eligible: state constraints require native fused constraint pruning(?: \(first state constraint: [^)]+\))?$",
    )
    .unwrap()
    .is_match(&normalized)
}

fn is_allowed_state_constraint_fused_level_skip(line: &str) -> bool {
    let normalized = line.split_whitespace().collect::<Vec<_>>().join(" ");
    Regex::new(
        r"(?i)^\[compiled-bfs\] fused level skipped: state constraints require LLVM2 native fused constraint support(?: \(first state constraint: [^)]+\))?$",
    )
    .unwrap()
    .is_match(&normalized)
}

fn proves_state_constrained_native_fused(spec: &SmokeSpec, segment: &str) -> bool {
    let Some(count) = spec.native_fused_state_constraint_count else {
        return false;
    };
    count > 0
        && spec.native_fused_mode == "state_constraint_checking"
        && spec
            .native_fused_loop_label
            .contains("state-constrained native fused")
        && segment.contains(&format!(
            "CompiledBfsLevel built ({})",
            spec.native_fused_loop_label
        ))
        && has_exact_telemetry(
            segment,
            "llvm2_bfs_level_loop_kind",
            "native_fused_llvm2_parent_loop",
        )
        && has_exact_telemetry(segment, "llvm2_native_fused_level_active", "true")
        && has_exact_telemetry(
            segment,
            "llvm2_native_fused_mode",
            "state_constraint_checking",
        )
        && has_exact_telemetry(
            segment,
            "llvm2_native_fused_state_constraint_count",
            &count.to_string(),
        )
}

fn has_exact_telemetry(text: &str, key: &str, value: &str) -> bool {
    let expected = format!("{key}={value}");
    text.split(|ch: char| ch.is_whitespace() || ch == ',' || ch == ';')
        .map(|token| token.trim_matches(|ch: char| matches!(ch, '(' | ')' | '[' | ']')))
        .any(|token| token == expected)
}

fn parse_usize(value: &str) -> Option<usize> {
    value.replace(',', "").parse::<usize>().ok()
}

fn evidence_tail(text: &str) -> Vec<String> {
    let mut lines: Vec<String> = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(str::to_string)
        .collect();
    if lines.len() > 24 {
        lines.drain(0..lines.len() - 24);
    }
    lines
}

fn repo_relative(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root)
        .map(Path::display)
        .map(|display| display.to_string())
        .unwrap_or_else(|_| path.display().to_string())
}

fn shell_join(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| {
            if arg.chars().all(|ch| {
                ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '/' | '.' | ':' | '=')
            }) {
                arg.clone()
            } else {
                format!("'{}'", arg.replace('\'', "'\\''"))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_markdown(summary: &serde_json::Value) -> String {
    let mut lines = vec![
        "# LLVM2 Native-Fused Bounded Smoke".to_string(),
        String::new(),
        format!("**Timestamp:** {}", summary["timestamp"].as_str().unwrap_or("")),
        format!("**Binary:** `{}`", summary["binary"].as_str().unwrap_or("")),
        format!(
            "**Artifact bundle:** `{}`",
            summary["artifact_bundle"].as_str().unwrap_or("")
        ),
        String::new(),
        "## Backend Controls".to_string(),
        String::new(),
        "```json".to_string(),
        serde_json::to_string_pretty(&summary["env_overrides"]).unwrap_or_else(|_| "{}".to_string()),
        "```".to_string(),
        String::new(),
        "| Spec | Result | Seconds | Loop fused | Initial | Levels | Parents | Generated | Total states | Artifact | Failures |".to_string(),
        "|------|--------|---------|------------|---------|--------|---------|-----------|--------------|----------|----------|".to_string(),
    ];
    if let Some(runs) = summary["runs"].as_array() {
        for row in runs {
            let result = if row["ok"].as_bool().unwrap_or(false) {
                "PASS"
            } else {
                "FAIL"
            };
            let failures = row["failures"]
                .as_array()
                .map(|failures| {
                    failures
                        .iter()
                        .filter_map(|failure| failure.as_str())
                        .collect::<Vec<_>>()
                        .join("; ")
                })
                .unwrap_or_default();
            lines.push(format!(
                "| {} | {result} | {:.3} | {} | {} | {} | {} | {} | {} | `{}` | {} |",
                row["spec"].as_str().unwrap_or(""),
                row["elapsed_seconds"].as_f64().unwrap_or(0.0),
                fmt_bool(row["compiled_bfs_level_loop_fused"].as_bool()),
                fmt_usize(row["compiled_bfs_level_loop_initial_states"].as_u64()),
                fmt_usize(row["compiled_bfs_levels_completed"].as_u64()),
                fmt_usize(row["compiled_bfs_parents_processed"].as_u64()),
                fmt_usize(row["compiled_bfs_successors_generated"].as_u64()),
                fmt_usize(row["compiled_bfs_total_states"].as_u64()),
                row["artifact_dir"].as_str().unwrap_or(""),
                failures
            ));
        }
        lines.extend([String::new(), "## Commands".to_string(), String::new()]);
        for row in runs {
            let command = row["command"]
                .as_array()
                .map(|items| {
                    items
                        .iter()
                        .filter_map(|item| item.as_str().map(str::to_string))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            lines.extend([
                format!("### {}", row["spec"].as_str().unwrap_or("")),
                String::new(),
                format!("`cwd: {}`", row["cwd"].as_str().unwrap_or("")),
                String::new(),
                "```sh".to_string(),
                shell_join(&command),
                "```".to_string(),
                String::new(),
                "```json".to_string(),
                serde_json::to_string_pretty(&row["env_overrides"])
                    .unwrap_or_else(|_| "{}".to_string()),
                "```".to_string(),
                String::new(),
            ]);
        }
    }
    lines.join("\n")
}

fn fmt_bool(value: Option<bool>) -> &'static str {
    match value {
        Some(true) => "yes",
        Some(false) => "no",
        None => "n/a",
    }
}

fn fmt_usize(value: Option<u64>) -> String {
    value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "n/a".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke_env_rejects_protected_override() {
        let mut overrides = BTreeMap::new();
        overrides.insert(
            "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP".to_string(),
            "0".to_string(),
        );

        let error = smoke_env_with_overrides(&overrides).unwrap_err();

        assert!(error
            .to_string()
            .contains("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=1"));
    }

    #[test]
    fn latest_segment_starts_at_flat_primary_rebuild() {
        let text = format!(
            "old fallback\nflat_state_primary=true\n{FLAT_PRIMARY_REBUILD_MARKER}\nllvm2_native_fused_level_active=true"
        );

        let segment = latest_flat_primary_backend_segment(&text);

        assert!(!segment.contains("old fallback"));
        assert!(segment.contains("flat_state_primary=true"));
        assert!(segment.contains("llvm2_native_fused_level_active=true"));
    }

    #[test]
    fn parses_loop_completion() {
        let completion = compiled_bfs_completion(
            "[compiled-bfs] completed: 3 levels, 12 parents, 2,997 generated, 1,000 new, 2,001 total states",
        )
        .unwrap();

        assert_eq!(completion, (3, 12, 2997, 1000, 2001));
    }

    #[test]
    fn check_command_forces_llvm2_backend() {
        let spec = smoke_spec("MCLamportMutex").unwrap();
        let command = build_check_command(
            Path::new("target/user/release/tla2"),
            &spec,
            Path::new("/tmp/examples"),
        );

        assert!(command
            .windows(2)
            .any(|window| window[0] == "--backend" && window[1] == "llvm2"));
    }

    #[test]
    fn strict_selftest_non_ok_result_fails() {
        let failures = strict_selftest_false_result_failures(
            "[llvm2-selftest] invariant callout kind=invariant status=Err value=1",
        );

        assert_eq!(failures.len(), 1);
        assert!(failures[0].contains("status=Err"));
    }
}
