// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use std::time::{SystemTime, UNIX_EPOCH};
use tla_core::{lower, parse_to_syntax_tree, FileId};

const SPEC_SRC: &str = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
TypeOK == x \in {0, 1, 2}
====
"#;

const CFG_SRC: &str = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";
const PROGRESS_SPEC_SRC: &str = r#"
---- MODULE ProgressStates ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 1500 /\ x' = x + 1
TypeOK == x \in 0..1500
====
"#;
const PROGRESS_CFG_SRC: &str = "INIT Init\nNEXT Next\nINVARIANT TypeOK\nCHECK_DEADLOCK FALSE\n";

fn parse_module(src: &str) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    lower_result.module.expect("module should lower")
}

fn make_temp_base_dir() -> PathBuf {
    let mut base_dir = std::env::temp_dir();
    let unique_suffix = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after unix epoch")
        .as_nanos();
    base_dir.push(format!(
        "tla-cli-runner-test-{}-{unique_suffix}",
        std::process::id()
    ));
    fs::create_dir_all(&base_dir).expect("create temp base directory");
    base_dir
}

fn write_spec_and_cfg(base_dir: &Path, stem: &str) -> (PathBuf, PathBuf) {
    let spec_path = base_dir.join(format!("{stem}.tla"));
    let cfg_path = base_dir.join(format!("{stem}.cfg"));
    fs::write(&spec_path, SPEC_SRC).expect("write spec");
    fs::write(&cfg_path, CFG_SRC).expect("write cfg");
    (spec_path, cfg_path)
}

fn make_progress_case(base_dir: &Path) -> (tla_core::ast::Module, Config, PathBuf, PathBuf) {
    let module = parse_module(PROGRESS_SPEC_SRC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };
    let spec_path = base_dir.join("ProgressStates.tla");
    let cfg_path = base_dir.join("ProgressStates.cfg");
    fs::write(&spec_path, PROGRESS_SPEC_SRC).expect("write spec");
    fs::write(&cfg_path, PROGRESS_CFG_SRC).expect("write cfg");
    (module, config, spec_path, cfg_path)
}

struct RunCase<'a> {
    file: &'a Path,
    config_path: &'a Path,
    checkpoint_dir: Option<PathBuf>,
    resume_from: Option<PathBuf>,
    max_states: usize,
}

fn run_once(
    module: &tla_core::ast::Module,
    config: &Config,
    case: RunCase<'_>,
) -> Result<(CheckResult, Option<String>)> {
    let no_progress: Box<dyn Fn(&Progress) + Send + Sync> = Box::new(|_| {});
    run_once_with_output(module, config, case, OutputFormat::Json, no_progress)
}

fn run_once_with_output(
    module: &tla_core::ast::Module,
    config: &Config,
    case: RunCase<'_>,
    output_format: OutputFormat,
    progress_callback: Box<dyn Fn(&Progress) + Send + Sync>,
) -> Result<(CheckResult, Option<String>)> {
    let checker_modules: [&tla_core::ast::Module; 0] = [];
    let no_storage: Option<std::sync::Arc<dyn tla_check::FingerprintSet>> = None;
    let resolved_spec: Option<tla_check::ResolvedSpec> = None;
    let fairness: Vec<tla_check::FairnessConstraint> = Vec::new();
    let mut tool_out: Option<tlc_tool::TlcToolOutput> = None;

    run_model_checker(ModelCheckerRunCfg {
        module,
        checker_modules: &checker_modules,
        config,
        workers: 1,
        file: case.file,
        file_paths: Vec::new(),
        resolved_spec: &resolved_spec,
        check_deadlock: false,
        show_coverage: false,
        continue_on_error: false,
        store_states: false,
        no_trace: false,
        fingerprint_storage: &no_storage,
        trace_file: None,
        trace_locs_storage: None,
        resolved_fairness: &fairness,
        max_states: case.max_states,
        max_depth: 0,
        memory_limit: 0,
        disk_limit: 0,
        output_format,
        progress_callback,
        checkpoint_dir: &case.checkpoint_dir,
        checkpoint_interval: 0,
        resume_from: &case.resume_from,
        config_path: case.config_path,
        tool_out: &mut tool_out,
        collision_check_mode: Default::default(),
    })
}

fn run_once_with_workers(
    module: &tla_core::ast::Module,
    config: &Config,
    case: RunCase<'_>,
    workers: usize,
) -> Result<(CheckResult, Option<String>)> {
    let checker_modules: [&tla_core::ast::Module; 0] = [];
    let no_storage: Option<std::sync::Arc<dyn tla_check::FingerprintSet>> = None;
    let resolved_spec: Option<tla_check::ResolvedSpec> = None;
    let fairness: Vec<tla_check::FairnessConstraint> = Vec::new();
    let mut tool_out: Option<tlc_tool::TlcToolOutput> = None;
    let no_progress: Box<dyn Fn(&Progress) + Send + Sync> = Box::new(|_| {});

    run_model_checker(ModelCheckerRunCfg {
        module,
        checker_modules: &checker_modules,
        config,
        workers,
        file: case.file,
        file_paths: Vec::new(),
        resolved_spec: &resolved_spec,
        check_deadlock: false,
        show_coverage: false,
        continue_on_error: false,
        store_states: false,
        no_trace: false,
        fingerprint_storage: &no_storage,
        trace_file: None,
        trace_locs_storage: None,
        resolved_fairness: &fairness,
        max_states: case.max_states,
        max_depth: 0,
        memory_limit: 0,
        disk_limit: 0,
        output_format: OutputFormat::Json,
        progress_callback: no_progress,
        checkpoint_dir: &case.checkpoint_dir,
        checkpoint_interval: 0,
        resume_from: &case.resume_from,
        config_path: case.config_path,
        tool_out: &mut tool_out,
        collision_check_mode: Default::default(),
    })
}

#[test]
fn resume_only_mode_still_validates_checkpoint_metadata_paths() {
    let module = parse_module(SPEC_SRC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let base_dir = make_temp_base_dir();
    let (spec_a, cfg_a) = write_spec_and_cfg(&base_dir, "SpecA");
    let (spec_b, cfg_b) = write_spec_and_cfg(&base_dir, "SpecB");
    let checkpoint_dir = base_dir.join("checkpoint");

    let save_result = run_once(
        &module,
        &config,
        RunCase {
            file: &spec_a,
            config_path: &cfg_a,
            checkpoint_dir: Some(checkpoint_dir.clone()),
            resume_from: None,
            max_states: 1,
        },
    )
    .expect("checkpoint save run should succeed");
    assert!(
        matches!(
            save_result.0,
            CheckResult::LimitReached {
                limit_type: tla_check::LimitType::States,
                ..
            }
        ),
        "expected checkpoint-producing limit run, got {:?}",
        save_result.0
    );

    let err = run_once(
        &module,
        &config,
        RunCase {
            file: &spec_b,
            config_path: &cfg_b,
            checkpoint_dir: None,
            resume_from: Some(checkpoint_dir),
            max_states: 0,
        },
    )
    .expect_err("resume-only run must reject mismatched checkpoint metadata paths");
    let msg = format!("{err:#}");
    assert!(
        msg.contains("checkpoint spec path mismatch"),
        "expected spec-path mismatch in error chain, got: {msg}"
    );

    let _ = fs::remove_dir_all(base_dir);
}

#[test]
fn workers_one_fp_only_path_runs_liveness_without_store_states() {
    let module = parse_module(
        r#"
---- MODULE FpOnlyLiveness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Progress".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let base_dir = make_temp_base_dir();
    let spec_path = base_dir.join("FpOnlyLiveness.tla");
    let cfg_path = base_dir.join("FpOnlyLiveness.cfg");
    fs::write(
        &spec_path,
        r#"
---- MODULE FpOnlyLiveness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    )
    .expect("write spec");
    fs::write(
        &cfg_path,
        "INIT Init\nNEXT Next\nPROPERTY Progress\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("write cfg");

    let result = run_once(
        &module,
        &config,
        RunCase {
            file: &spec_path,
            config_path: &cfg_path,
            checkpoint_dir: None,
            resume_from: None,
            max_states: 0,
        },
    )
    .expect("workers=1 fp-only liveness run should complete");

    assert!(
        matches!(result.0, CheckResult::LivenessViolation { .. }),
        "expected workers=1 fp-only path to report LivenessViolation, got {:?}",
        result.0
    );

    let _ = fs::remove_dir_all(base_dir);
}

#[test]
fn human_output_wires_progress_callback_without_cli_flag() {
    let base_dir = make_temp_base_dir();
    let (module, config, spec_path, cfg_path) = make_progress_case(&base_dir);
    let progress_hits = Arc::new(AtomicUsize::new(0));
    let progress_hits_clone = Arc::clone(&progress_hits);
    let result = run_once_with_output(
        &module,
        &config,
        RunCase {
            file: &spec_path,
            config_path: &cfg_path,
            checkpoint_dir: None,
            resume_from: None,
            max_states: 0,
        },
        OutputFormat::Human,
        Box::new(move |_| {
            progress_hits_clone.fetch_add(1, Ordering::Relaxed);
        }),
    )
    .expect("human-output run should succeed");

    assert!(
        matches!(result.0, CheckResult::Success(_)),
        "expected successful counter exploration, got {:?}",
        result.0
    );
    assert!(
        progress_hits.load(Ordering::Relaxed) > 0,
        "expected human output to wire progress callback without --progress"
    );

    let _ = fs::remove_dir_all(base_dir);
}

/// Part of #3706: POR is now accepted in auto mode (routed to sequential or parallel).
#[test]
fn auto_mode_accepts_por_flag() {
    let module = parse_module(SPEC_SRC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        por_enabled: true,
        ..Default::default()
    };

    let base_dir = make_temp_base_dir();
    let (spec_path, cfg_path) = write_spec_and_cfg(&base_dir, "AutoPor");

    let (result, _strategy) = run_once_with_workers(
        &module,
        &config,
        RunCase {
            file: &spec_path,
            config_path: &cfg_path,
            checkpoint_dir: None,
            resume_from: None,
            max_states: 0,
        },
        0,
    )
    .expect("auto POR run should reach the checker");

    assert!(
        matches!(result, CheckResult::Success(_)),
        "auto mode with --por should succeed, got: {result:?}",
    );

    let _ = fs::remove_dir_all(base_dir);
}

/// Part of #3706: POR is now accepted in parallel mode.
#[test]
fn parallel_mode_accepts_por_flag() {
    let module = parse_module(SPEC_SRC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        por_enabled: true,
        ..Default::default()
    };

    let base_dir = make_temp_base_dir();
    let (spec_path, cfg_path) = write_spec_and_cfg(&base_dir, "ParallelPor");

    let (result, _strategy) = run_once_with_workers(
        &module,
        &config,
        RunCase {
            file: &spec_path,
            config_path: &cfg_path,
            checkpoint_dir: None,
            resume_from: None,
            max_states: 0,
        },
        2,
    )
    .expect("parallel POR run should reach the checker");

    assert!(
        matches!(result, CheckResult::Success(_)),
        "parallel mode with --por should succeed, got: {result:?}",
    );

    let _ = fs::remove_dir_all(base_dir);
}

#[test]
fn parallel_mode_runs_on_the_fly_liveness() {
    let module = parse_module(
        r#"
---- MODULE ParallelOnTheFly ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Progress".to_string()],
        liveness_execution: tla_check::LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };

    let base_dir = make_temp_base_dir();
    let spec_path = base_dir.join("ParallelOnTheFly.tla");
    let cfg_path = base_dir.join("ParallelOnTheFly.cfg");
    fs::write(
        &spec_path,
        r#"
---- MODULE ParallelOnTheFly ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    )
    .expect("write spec");
    fs::write(
        &cfg_path,
        "INIT Init\nNEXT Next\nPROPERTY Progress\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("write cfg");

    let (result, _strategy) = run_once_with_workers(
        &module,
        &config,
        RunCase {
            file: &spec_path,
            config_path: &cfg_path,
            checkpoint_dir: None,
            resume_from: None,
            max_states: 0,
        },
        2,
    )
    .expect("parallel on-the-fly liveness should run");
    match result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(property, "Progress");
        }
        other => panic!("expected parallel on-the-fly liveness violation, got: {other:?}"),
    }

    let _ = fs::remove_dir_all(base_dir);
}
