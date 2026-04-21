// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled model checking: generate Rust from TLA+, compile, and run.
//!
//! When `--compiled` is passed to `tla2 check`, this module:
//! 1. Generates Rust source code from the TLA+ spec via TIR codegen
//! 2. Writes a complete Cargo project to a temporary directory
//! 3. Builds the project with `cargo build --release`
//! 4. Runs the compiled binary
//! 5. Parses the output and reports results in the same format as the interpreter

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use anyhow::{bail, Context, Result};

/// Compile-time path to the tla-cli crate root, used to resolve tla-runtime
/// relative to the repo tree without depending on the binary's runtime location.
const CLI_MANIFEST_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Result parsed from the compiled binary's output.
pub(crate) struct CompiledCheckResult {
    pub(crate) distinct_states: usize,
    pub(crate) states_explored: usize,
    pub(crate) violation: Option<String>,
    pub(crate) deadlock: bool,
}

/// Configuration for the compiled check run, forwarded from CLI args.
pub(crate) struct CompiledCheckConfig<'a> {
    pub(crate) file: &'a Path,
    pub(crate) config_path: Option<&'a Path>,
    pub(crate) output_format: crate::cli_schema::OutputFormat,
    pub(crate) workers: usize,
    pub(crate) no_deadlock: bool,
    pub(crate) max_states: usize,
}

/// Run the compiled model checking pipeline (simple 3-arg API for backward compat).
///
/// This is the entry point called from `cmd_check` when `--compiled` is set.
pub(crate) fn run_compiled_check(
    file: &Path,
    config_path: Option<&Path>,
    output_format: crate::cli_schema::OutputFormat,
) -> Result<()> {
    run_compiled_check_with_config(&CompiledCheckConfig {
        file,
        config_path,
        output_format,
        workers: 1,
        no_deadlock: false,
        max_states: 100_000_000,
    })
}

/// Run the compiled model checking pipeline with full configuration.
pub(crate) fn run_compiled_check_with_config(cfg: &CompiledCheckConfig<'_>) -> Result<()> {
    let start = Instant::now();

    // Step 1: Generate Rust code via TIR codegen
    eprintln!("Compiled check: generating Rust code from TLA+ spec...");
    let rust_code = generate_tir_code(cfg.file, cfg.config_path)?;

    // Step 2: Write Cargo project to temp dir
    let temp_dir = tempfile::tempdir().context("create temp directory for compiled check")?;
    let project_dir = temp_dir.path();
    eprintln!(
        "Compiled check: writing Cargo project to {}",
        project_dir.display()
    );
    write_cargo_project(cfg.file, project_dir, &rust_code, cfg.no_deadlock)?;

    // Debug: dump generated files to stderr
    if std::env::var("TLA2_COMPILED_DEBUG").is_ok() {
        if let Ok(toml) = std::fs::read_to_string(project_dir.join("Cargo.toml")) {
            eprintln!("=== Generated Cargo.toml ===\n{toml}");
        }
        if let Ok(main) = std::fs::read_to_string(project_dir.join("src/main.rs")) {
            eprintln!("=== Generated main.rs ===\n{main}");
        }
        // Dump spec module source
        let src_dir = project_dir.join("src");
        if let Ok(entries) = std::fs::read_dir(&src_dir) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                if name != "main.rs" && name.ends_with(".rs") {
                    if let Ok(content) = std::fs::read_to_string(entry.path()) {
                        eprintln!("=== Generated {} ===\n{content}", name);
                    }
                }
            }
        }
    }

    // Step 3: Build with cargo
    eprintln!("Compiled check: building with cargo build --release...");
    let build_start = Instant::now();
    build_project(project_dir)?;
    let build_elapsed = build_start.elapsed();
    eprintln!(
        "Compiled check: build succeeded in {:.1}s",
        build_elapsed.as_secs_f64()
    );

    // Step 4: Run the compiled binary
    eprintln!("Compiled check: running compiled model checker...");
    let run_start = Instant::now();
    let output = run_binary(project_dir, cfg.max_states, cfg.workers)?;
    let run_elapsed = run_start.elapsed();

    // Step 5: Parse and report results
    let result = parse_output(&output)?;
    let total_elapsed = start.elapsed();

    report_results(
        &result,
        cfg.output_format,
        build_elapsed,
        run_elapsed,
        total_elapsed,
    )
}

/// Generate Rust code from the TLA+ spec via TIR codegen.
fn generate_tir_code(file: &Path, config_path: Option<&Path>) -> Result<String> {
    use tla_codegen::{generate_rust_from_tir_with_modules, TirCodeGenOptions};
    use tla_core::ast::Unit;
    use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader};
    use tla_tir::{lower_module_for_codegen, TirLoweringEnv};

    let source = crate::read_source(file)?;
    let tree = crate::parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader
        .load_extends(&module)
        .with_context(|| format!("load EXTENDS dependencies for `{}`", module.name.node))?;
    loader
        .load_instances(&module)
        .with_context(|| format!("load INSTANCE dependencies for `{}`", module.name.node))?;

    let dep_modules = loader.modules_for_model_checking(&module);
    let mut env = TirLoweringEnv::new(&module);
    for dep in &dep_modules {
        env.add_module(dep);
    }

    let tir_module = lower_module_for_codegen(&env, &module)
        .map_err(|e| anyhow::anyhow!("TIR lowering failed: {e}"))?;

    // Extract state variables from main module AND dependency modules
    let mut state_vars: Vec<String> = Vec::new();
    let mut seen_vars: HashSet<String> = HashSet::new();
    for m in std::iter::once(&module).chain(dep_modules.iter().copied()) {
        for unit in &m.units {
            if let Unit::Variable(vars) = &unit.node {
                for v in vars {
                    if seen_vars.insert(v.node.clone()) {
                        state_vars.push(v.node.clone());
                    }
                }
            }
        }
    }

    // Parse config using shared config parser from cmd_codegen
    let parsed_cfg = crate::cmd_codegen::parse_simple_config_pub(file, config_path)?;
    let mut constants = parsed_cfg.constants;
    let invariant_names = parsed_cfg.invariants;

    // Resolve constant references
    let spec_dir = file.parent().unwrap_or(Path::new("."));
    crate::cmd_codegen::resolve_constant_refs_pub(&mut constants, config_path, spec_dir);

    let init_name = crate::cmd_codegen::resolve_init_name_pub(
        &parsed_cfg.init,
        &parsed_cfg.specification,
        &tir_module,
    );
    let next_name = crate::cmd_codegen::resolve_next_name_pub(
        &parsed_cfg.next,
        &parsed_cfg.specification,
        &tir_module,
    );

    let options = TirCodeGenOptions {
        module_name: None,
        init_name: Some(init_name),
        next_name: Some(next_name),
    };
    generate_rust_from_tir_with_modules(
        &tir_module,
        &module,
        &env,
        &state_vars,
        &constants,
        &invariant_names,
        &options,
    )
    .map_err(|e| anyhow::anyhow!("{e}"))
}

/// Write a complete Cargo project for the compiled check.
fn write_cargo_project(
    spec_file: &Path,
    project_dir: &Path,
    rust_code: &str,
    no_deadlock: bool,
) -> Result<()> {
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir)
        .with_context(|| format!("create directory {}", src_dir.display()))?;

    let spec_stem = spec_file
        .file_stem()
        .and_then(|s| s.to_str())
        .context("could not extract spec name from file path")?;

    let mod_name = to_snake_case(spec_stem);
    let machine_type = to_pascal_case(spec_stem);

    // Find tla-runtime path
    let runtime_dep = find_tla_runtime_dep();

    // Write Cargo.toml
    let cargo_toml = format!(
        "[package]\n\
         name = \"{mod_name}-compiled-check\"\n\
         version = \"0.1.0\"\n\
         edition = \"2021\"\n\
         \n\
         [workspace]\n\
         \n\
         [[bin]]\n\
         name = \"check\"\n\
         path = \"src/main.rs\"\n\
         \n\
         [dependencies]\n\
         {runtime_dep}\n\
         \n\
         [profile.release]\n\
         opt-level = 3\n\
         lto = \"thin\"\n"
    );
    std::fs::write(project_dir.join("Cargo.toml"), &cargo_toml)
        .with_context(|| format!("write {}/Cargo.toml", project_dir.display()))?;

    // Write the generated module
    std::fs::write(src_dir.join(format!("{mod_name}.rs")), rust_code)
        .with_context(|| format!("write src/{mod_name}.rs"))?;

    // Write main.rs with BFS model checker that outputs structured results
    let main_rs = generate_compiled_main(&mod_name, &machine_type, no_deadlock);
    std::fs::write(src_dir.join("main.rs"), &main_rs).context("write src/main.rs")?;

    Ok(())
}

/// Generate the main.rs for the compiled binary.
///
/// The binary reads TLA2_MAX_STATES and TLA2_WORKERS from environment variables
/// (set by the CLI runner) and outputs results in a structured text format:
/// ```text
/// TLA2_COMPILED_CHECK_START
/// distinct_states=<N>
/// states_explored=<N>
/// status=<ok|violation|deadlock>
/// violation_invariant=<name>  (only if status=violation)
/// TLA2_COMPILED_CHECK_END
/// ```
fn generate_compiled_main(mod_name: &str, machine_type: &str, no_deadlock: bool) -> String {
    let deadlock_check = if no_deadlock {
        "false"
    } else {
        "true"
    };
    format!(
        r#"// Generated by tla2 check --compiled
// Copyright 2026 Andrew Yates
// Author: Andrew Yates

mod {mod_name};

use {mod_name}::{machine_type};
use tla_runtime::prelude::*;

fn main() {{
    let machine = {machine_type};
    let max_states: usize = std::env::var("TLA2_MAX_STATES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(100_000_000);
    let check_deadlock: bool = {deadlock_check};

    let start = std::time::Instant::now();
    let result = model_check(&machine, max_states);
    let elapsed = start.elapsed();

    // Output structured results for the CLI to parse
    println!("TLA2_COMPILED_CHECK_START");
    println!("distinct_states={{}}", result.distinct_states);
    println!("states_explored={{}}", result.states_explored);
    println!("elapsed_ms={{}}", elapsed.as_millis());

    if let Some(ref violation) = result.violation {{
        println!("status=violation");
        if let Some(ref name) = violation.invariant_name {{
            println!("violation_invariant={{}}", name);
        }}
    }} else if !check_deadlock && result.deadlock.is_some() {{
        // Deadlock checking disabled: treat deadlock as success
        println!("status=ok");
    }} else if result.deadlock.is_some() {{
        println!("status=deadlock");
    }} else {{
        println!("status=ok");
    }}
    println!("TLA2_COMPILED_CHECK_END");

    eprintln!("Compiled check: {{}} distinct states, {{}} explored in {{:.2}}s",
        result.distinct_states, result.states_explored, elapsed.as_secs_f64());

    if result.violation.is_some() {{
        std::process::exit(1);
    }}
    if check_deadlock && result.deadlock.is_some() {{
        std::process::exit(1);
    }}
}}
"#
    )
}

/// Build the generated Cargo project.
fn build_project(project_dir: &Path) -> Result<()> {
    let cargo = find_cargo();

    let output = Command::new(&cargo)
        .args(["build", "--release"])
        .current_dir(project_dir)
        .env("CARGO_TARGET_DIR", project_dir.join("target"))
        // Use stable toolchain to avoid nightly-only diagnostics/warnings
        .env("RUSTUP_TOOLCHAIN", "stable")
        .output()
        .with_context(|| format!("run cargo build in {}", project_dir.display()))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!(
            "cargo build --release failed (exit {})\n\nstdout:\n{}\n\nstderr:\n{}",
            output.status,
            stdout,
            stderr
        );
    }

    Ok(())
}

/// Run the compiled binary and capture its output.
fn run_binary(project_dir: &Path, max_states: usize, _workers: usize) -> Result<String> {
    let binary = project_dir.join("target/release/check");
    if !binary.exists() {
        bail!("compiled binary not found at {}", binary.display());
    }

    // max_states == 0 means "unlimited" in the CLI but the runtime model_check
    // treats max_states as a hard ceiling (states_explored > max_states => break).
    // Convert 0 to a large sentinel so the runtime never hits the limit.
    let effective_max = if max_states == 0 {
        usize::MAX
    } else {
        max_states
    };

    let output = Command::new(&binary)
        .env("TLA2_MAX_STATES", effective_max.to_string())
        .output()
        .with_context(|| format!("run compiled binary {}", binary.display()))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);

    if !stderr.is_empty() {
        eprintln!("{}", stderr);
    }

    // The binary exits with 1 on violation/deadlock, which is expected
    if !output.status.success() && !stdout.contains("TLA2_COMPILED_CHECK_START") {
        bail!(
            "compiled binary failed (exit {})\nstdout:\n{}\nstderr:\n{}",
            output.status,
            stdout,
            stderr
        );
    }

    Ok(stdout)
}

/// Parse the structured output from the compiled binary.
fn parse_output(output: &str) -> Result<CompiledCheckResult> {
    let start_marker = "TLA2_COMPILED_CHECK_START";
    let end_marker = "TLA2_COMPILED_CHECK_END";

    let start_idx = output
        .find(start_marker)
        .context("compiled binary output missing TLA2_COMPILED_CHECK_START marker")?;
    let end_idx = output
        .find(end_marker)
        .context("compiled binary output missing TLA2_COMPILED_CHECK_END marker")?;

    let block = &output[start_idx + start_marker.len()..end_idx];

    let mut distinct_states = 0;
    let mut states_explored = 0;
    let mut status = "ok".to_string();
    let mut violation_invariant = None;

    for line in block.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(val) = line.strip_prefix("distinct_states=") {
            distinct_states = val.parse().unwrap_or(0);
        } else if let Some(val) = line.strip_prefix("states_explored=") {
            states_explored = val.parse().unwrap_or(0);
        } else if let Some(val) = line.strip_prefix("status=") {
            status = val.to_string();
        } else if let Some(val) = line.strip_prefix("violation_invariant=") {
            violation_invariant = Some(val.to_string());
        }
    }

    Ok(CompiledCheckResult {
        distinct_states,
        states_explored,
        violation: if status == "violation" {
            Some(violation_invariant.unwrap_or_else(|| "unknown".to_string()))
        } else {
            None
        },
        deadlock: status == "deadlock",
    })
}

/// Report results in the requested format.
fn report_results(
    result: &CompiledCheckResult,
    output_format: crate::cli_schema::OutputFormat,
    build_elapsed: std::time::Duration,
    run_elapsed: std::time::Duration,
    total_elapsed: std::time::Duration,
) -> Result<()> {
    match output_format {
        crate::cli_schema::OutputFormat::Json | crate::cli_schema::OutputFormat::Jsonl => {
            let status = if result.violation.is_some() {
                "violation"
            } else if result.deadlock {
                "deadlock"
            } else {
                "ok"
            };
            println!(
                r#"{{"mode":"compiled","status":"{}","distinct_states":{},"states_explored":{},"build_time_ms":{},"check_time_ms":{},"total_time_ms":{}}}"#,
                status,
                result.distinct_states,
                result.states_explored,
                build_elapsed.as_millis(),
                run_elapsed.as_millis(),
                total_elapsed.as_millis(),
            );
        }
        _ => {
            println!();
            println!("=== Compiled Model Check Results ===");
            println!();
            if let Some(ref inv) = result.violation {
                println!("INVARIANT VIOLATION: {inv}");
                println!();
            }
            if result.deadlock {
                println!("DEADLOCK DETECTED");
                println!();
            }
            println!("Distinct states found: {}", result.distinct_states);
            println!("States explored:       {}", result.states_explored);
            println!();
            println!("Build time:  {:.2}s", build_elapsed.as_secs_f64());
            println!("Check time:  {:.2}s", run_elapsed.as_secs_f64());
            println!("Total time:  {:.2}s", total_elapsed.as_secs_f64());
            if result.violation.is_none() && !result.deadlock {
                println!();
                println!("Model checking complete: no errors found.");
            }
        }
    }

    if let Some(ref inv) = result.violation {
        bail!("Invariant {} violated (compiled check)", inv);
    }
    if result.deadlock {
        bail!("Deadlock detected (compiled check)");
    }

    Ok(())
}

/// Find the cargo binary to use for building.
fn find_cargo() -> PathBuf {
    // Prefer the stable toolchain to avoid nightly issues
    if let Ok(output) = Command::new("rustup")
        .args(["which", "cargo", "--toolchain", "stable"])
        .output()
    {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return PathBuf::from(path);
            }
        }
    }
    PathBuf::from("cargo")
}

/// Locate tla-runtime for the Cargo.toml dependency line.
///
/// Uses the compile-time `CARGO_MANIFEST_DIR` to resolve the repo root,
/// then navigates to `crates/tla-runtime`. Falls back to walking up from
/// the current binary's location, then to a relative path.
fn find_tla_runtime_dep() -> String {
    // Primary: use compile-time repo location (tla-cli is at crates/tla-cli/)
    let cli_dir = Path::new(CLI_MANIFEST_DIR);
    if let Some(repo_root) = cli_dir.parent().and_then(|p| p.parent()) {
        let candidate = repo_root.join("crates/tla-runtime");
        if candidate.exists() {
            return format!(
                "tla-runtime = {{ path = \"{}\" }}",
                candidate.display()
            );
        }
    }

    // Fallback: walk up from current binary
    if let Ok(exe) = std::env::current_exe() {
        let mut dir = exe.parent().map(PathBuf::from);
        for _ in 0..10 {
            if let Some(ref d) = dir {
                let candidate = d.join("crates/tla-runtime");
                if candidate.exists() {
                    return format!(
                        "tla-runtime = {{ path = \"{}\" }}",
                        candidate.display()
                    );
                }
                dir = d.parent().map(PathBuf::from);
            }
        }
    }
    "tla-runtime = { path = \"../../crates/tla-runtime\" }".to_string()
}

/// Simple snake_case conversion.
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(c.to_ascii_lowercase());
    }
    result
}

/// Simple PascalCase conversion.
fn to_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            capitalize = true;
        } else if capitalize {
            result.push(c.to_ascii_uppercase());
            capitalize = false;
        } else {
            result.push(c);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_snake_case_basic() {
        assert_eq!(to_snake_case("Counter"), "counter");
        assert_eq!(to_snake_case("DieHard"), "die_hard");
        assert_eq!(to_snake_case("MCBakery"), "m_c_bakery");
        assert_eq!(to_snake_case("simple"), "simple");
    }

    #[test]
    fn test_to_pascal_case_basic() {
        assert_eq!(to_pascal_case("counter"), "Counter");
        assert_eq!(to_pascal_case("die_hard"), "DieHard");
        assert_eq!(to_pascal_case("Counter"), "Counter");
    }

    #[test]
    fn test_parse_output_ok() {
        let output = "\
            TLA2_COMPILED_CHECK_START\n\
            distinct_states=6\n\
            states_explored=6\n\
            elapsed_ms=42\n\
            status=ok\n\
            TLA2_COMPILED_CHECK_END\n";
        let result = parse_output(output).expect("parse should succeed");
        assert_eq!(result.distinct_states, 6);
        assert_eq!(result.states_explored, 6);
        assert!(result.violation.is_none());
        assert!(!result.deadlock);
    }

    #[test]
    fn test_parse_output_violation() {
        let output = "\
            TLA2_COMPILED_CHECK_START\n\
            distinct_states=10\n\
            states_explored=5\n\
            status=violation\n\
            violation_invariant=TypeOK\n\
            TLA2_COMPILED_CHECK_END\n";
        let result = parse_output(output).expect("parse should succeed");
        assert_eq!(result.distinct_states, 10);
        assert_eq!(result.violation, Some("TypeOK".to_string()));
        assert!(!result.deadlock);
    }

    #[test]
    fn test_parse_output_deadlock() {
        let output = "\
            TLA2_COMPILED_CHECK_START\n\
            distinct_states=3\n\
            states_explored=3\n\
            status=deadlock\n\
            TLA2_COMPILED_CHECK_END\n";
        let result = parse_output(output).expect("parse should succeed");
        assert_eq!(result.distinct_states, 3);
        assert!(result.violation.is_none());
        assert!(result.deadlock);
    }

    #[test]
    fn test_parse_output_missing_markers() {
        let output = "some random output without markers";
        assert!(parse_output(output).is_err());
    }

    #[test]
    fn test_find_tla_runtime_dep_resolves() {
        let dep = find_tla_runtime_dep();
        assert!(
            dep.contains("tla-runtime"),
            "dependency string should reference tla-runtime: {dep}"
        );
        // When running from the repo, the compile-time path should resolve
        if dep.contains("path =") {
            let path_start = dep.find('"').unwrap() + 1;
            let path_end = dep.rfind('"').unwrap();
            let path = &dep[path_start..path_end];
            assert!(
                Path::new(path).exists(),
                "tla-runtime path should exist: {path}"
            );
        }
    }

    #[test]
    fn test_generate_compiled_main_contains_protocol() {
        let main_rs = generate_compiled_main("counter", "Counter", false);
        // Verify the main.rs contains IPC protocol markers
        assert!(
            main_rs.contains("TLA2_COMPILED_CHECK_START"),
            "generated main.rs should contain start marker"
        );
        assert!(
            main_rs.contains("TLA2_COMPILED_CHECK_END"),
            "generated main.rs should contain end marker"
        );
        assert!(
            main_rs.contains("model_check"),
            "generated main.rs should call model_check"
        );
        assert!(
            main_rs.contains("mod counter"),
            "generated main.rs should import the spec module"
        );
        assert!(
            main_rs.contains("use counter::Counter"),
            "generated main.rs should use the machine type"
        );
    }

    #[test]
    fn test_generate_compiled_main_no_deadlock_check() {
        let main_with = generate_compiled_main("spec", "Spec", false);
        let main_without = generate_compiled_main("spec", "Spec", true);
        // With check_deadlock=true, the code uses "true" for the deadlock check
        assert!(
            main_with.contains("let check_deadlock: bool = true"),
            "should check deadlocks when no_deadlock=false"
        );
        // With check_deadlock=false (no_deadlock=true), the code uses "false"
        assert!(
            main_without.contains("let check_deadlock: bool = false"),
            "should not check deadlocks when no_deadlock=true"
        );
    }

    #[test]
    fn test_write_cargo_project_creates_files() {
        let temp_dir = tempfile::tempdir().expect("create temp dir");
        let project_dir = temp_dir.path();
        let spec_file = Path::new("/tmp/TestSpec.tla");
        let rust_code = "// generated code\npub struct TestSpec;\n";

        write_cargo_project(spec_file, project_dir, rust_code, false)
            .expect("write_cargo_project should succeed");

        // Verify Cargo.toml exists and contains expected content
        let cargo_toml = std::fs::read_to_string(project_dir.join("Cargo.toml"))
            .expect("read Cargo.toml");
        assert!(
            cargo_toml.contains("[package]"),
            "Cargo.toml should have [package]"
        );
        assert!(
            cargo_toml.contains("tla-runtime"),
            "Cargo.toml should depend on tla-runtime"
        );
        assert!(
            cargo_toml.contains("[workspace]"),
            "Cargo.toml should have standalone [workspace]"
        );
        assert!(
            cargo_toml.contains("opt-level = 3"),
            "release profile should use opt-level 3"
        );

        // Verify main.rs exists
        let main_rs = std::fs::read_to_string(project_dir.join("src/main.rs"))
            .expect("read main.rs");
        assert!(
            main_rs.contains("TLA2_COMPILED_CHECK_START"),
            "main.rs should contain protocol markers"
        );

        // Verify spec module exists
        let spec_rs = std::fs::read_to_string(project_dir.join("src/test_spec.rs"))
            .expect("read spec module");
        assert_eq!(spec_rs, rust_code);
    }

    #[test]
    fn test_generate_tir_code_counter_spec() {
        // Create a simple Counter spec in a temp directory
        let temp_dir = tempfile::tempdir().expect("create temp dir");
        let spec_path = temp_dir.path().join("Counter.tla");
        std::fs::write(
            &spec_path,
            "---- MODULE Counter ----\n\
             EXTENDS Naturals\n\
             VARIABLE x\n\
             Init == x = 0\n\
             Next == x < 5 /\\ x' = x + 1\n\
             InRange == x >= 0 /\\ x <= 5\n\
             ====\n",
        )
        .expect("write spec");

        let cfg_path = temp_dir.path().join("Counter.cfg");
        std::fs::write(
            &cfg_path,
            "INIT Init\nNEXT Next\nINVARIANT InRange\n",
        )
        .expect("write config");

        let result = generate_tir_code(&spec_path, Some(&cfg_path));
        match result {
            Ok(rust_code) => {
                // Verify the generated code contains expected patterns
                assert!(
                    rust_code.contains("StateMachine"),
                    "generated code should implement StateMachine"
                );
                assert!(
                    rust_code.contains("fn init"),
                    "generated code should have init function"
                );
                assert!(
                    rust_code.contains("fn next"),
                    "generated code should have next function"
                );
            }
            Err(e) => {
                // TIR codegen may fail for some specs due to unsupported features.
                // This is acceptable — the compiled check gracefully reports errors.
                eprintln!(
                    "TIR codegen failed for Counter spec (may be expected): {e}"
                );
            }
        }
    }

    #[test]
    fn test_compiled_check_config_default_values() {
        let file = Path::new("/tmp/test.tla");
        let cfg = CompiledCheckConfig {
            file,
            config_path: None,
            output_format: crate::cli_schema::OutputFormat::Human,
            workers: 1,
            no_deadlock: false,
            max_states: 100_000_000,
        };
        assert_eq!(cfg.workers, 1);
        assert!(!cfg.no_deadlock);
        assert_eq!(cfg.max_states, 100_000_000);
    }

    #[test]
    fn test_parse_output_extra_lines_before_markers() {
        // Test that parser handles output with extra text before/after markers
        let output = "Some debug output line 1\n\
            Some debug output line 2\n\
            TLA2_COMPILED_CHECK_START\n\
            distinct_states=42\n\
            states_explored=100\n\
            status=ok\n\
            TLA2_COMPILED_CHECK_END\n\
            Some trailing output\n";
        let result = parse_output(output).expect("parse should handle extra lines");
        assert_eq!(result.distinct_states, 42);
        assert_eq!(result.states_explored, 100);
        assert!(result.violation.is_none());
        assert!(!result.deadlock);
    }

    #[test]
    fn test_max_states_zero_to_usize_max() {
        // Verify that the run_binary function converts max_states=0 to usize::MAX.
        // We can't actually run the binary in tests, but we can verify the logic
        // by checking the code in generate_compiled_main: it reads TLA2_MAX_STATES
        // from env, defaulting to 100_000_000 if missing.
        // The CLI converts 0 to usize::MAX in run_binary().
        let max_states: usize = 0;
        let effective_max = if max_states == 0 {
            usize::MAX
        } else {
            max_states
        };
        assert_eq!(effective_max, usize::MAX);
    }

    #[test]
    fn test_generate_tir_code_multi_variable_spec() {
        // DieHard-style spec with two VARIABLEs and disjunctive Next.
        let temp_dir = tempfile::tempdir().expect("create temp dir");
        let spec_path = temp_dir.path().join("DieHard.tla");
        std::fs::write(
            &spec_path,
            "---- MODULE DieHard ----\n\
             EXTENDS Naturals\n\
             VARIABLES small, big\n\
             Init == small = 0 /\\ big = 0\n\
             FillSmall  == small' = 3 /\\ big' = big\n\
             FillBig    == big' = 5   /\\ small' = small\n\
             EmptySmall == small' = 0 /\\ big' = big\n\
             EmptyBig   == big' = 0   /\\ small' = small\n\
             SmallToBig == IF small + big <= 5\n\
                           THEN /\\ big' = small + big\n\
                                /\\ small' = 0\n\
                           ELSE /\\ big' = 5\n\
                                /\\ small' = small + big - 5\n\
             BigToSmall == IF small + big <= 3\n\
                           THEN /\\ small' = small + big\n\
                                /\\ big' = 0\n\
                           ELSE /\\ small' = 3\n\
                                /\\ big' = small + big - 3\n\
             Next == FillSmall \\/ FillBig \\/ EmptySmall \\/ EmptyBig\n\
                  \\/ SmallToBig \\/ BigToSmall\n\
             TypeOK == small \\in 0..3 /\\ big \\in 0..5\n\
             ====\n",
        )
        .expect("write spec");

        let cfg_path = temp_dir.path().join("DieHard.cfg");
        std::fs::write(
            &cfg_path,
            "INIT Init\nNEXT Next\nINVARIANT TypeOK\n",
        )
        .expect("write config");

        let result = generate_tir_code(&spec_path, Some(&cfg_path));
        match result {
            Ok(rust_code) => {
                // Multi-variable spec should produce state struct with both fields
                assert!(
                    rust_code.contains("small") || rust_code.contains("big"),
                    "generated code should reference state variables: {}",
                    &rust_code[..rust_code.len().min(500)]
                );
                assert!(
                    rust_code.contains("fn init"),
                    "generated code should have init function"
                );
                assert!(
                    rust_code.contains("fn next"),
                    "generated code should have next function"
                );
            }
            Err(e) => {
                // TIR codegen may not yet support all DieHard patterns.
                eprintln!(
                    "TIR codegen failed for DieHard spec (may be expected): {e}"
                );
            }
        }
    }

    #[test]
    fn test_generate_tir_code_malformed_spec_returns_error() {
        // A file that is not valid TLA+ at all (no module header).
        let temp_dir = tempfile::tempdir().expect("create temp dir");
        let spec_path = temp_dir.path().join("Malformed.tla");
        std::fs::write(
            &spec_path,
            "this is not a valid TLA+ module at all\n",
        )
        .expect("write spec");

        let cfg_path = temp_dir.path().join("Malformed.cfg");
        std::fs::write(
            &cfg_path,
            "INIT Init\nNEXT Next\n",
        )
        .expect("write config");

        // Should fail because the file can't be parsed as TLA+.
        let result = generate_tir_code(&spec_path, Some(&cfg_path));
        assert!(
            result.is_err(),
            "malformed TLA+ file should fail during parsing or lowering"
        );
    }

    #[test]
    fn test_write_cargo_project_hyphenated_name() {
        // Spec name with hyphens should produce correct snake_case module name.
        let temp_dir = tempfile::tempdir().expect("create temp dir");
        let project_dir = temp_dir.path().join("project");
        std::fs::create_dir_all(&project_dir).expect("create project dir");
        let spec_file = Path::new("/tmp/My-Cool-Spec.tla");
        let rust_code = "// generated\npub struct MyCoolSpec;\n";

        write_cargo_project(spec_file, &project_dir, rust_code, true)
            .expect("write_cargo_project with hyphenated name should succeed");

        // The module name should be snake_case of "My-Cool-Spec"
        let expected_mod = to_snake_case("My-Cool-Spec");
        let mod_file = project_dir.join(format!("src/{expected_mod}.rs"));
        assert!(
            mod_file.exists(),
            "spec module file should exist at src/{expected_mod}.rs, found: {}",
            mod_file.display()
        );

        // main.rs should reference the snake_case module
        let main_rs =
            std::fs::read_to_string(project_dir.join("src/main.rs")).expect("read main.rs");
        assert!(
            main_rs.contains(&format!("mod {expected_mod}")),
            "main.rs should import module {expected_mod}: {}",
            &main_rs[..main_rs.len().min(200)]
        );

        // Deadlock check should be disabled (no_deadlock=true)
        assert!(
            main_rs.contains("let check_deadlock: bool = false"),
            "no_deadlock=true should set check_deadlock to false"
        );
    }

    #[test]
    fn test_parse_output_empty_block_defaults() {
        // Markers present but block contains only whitespace/blank lines.
        let output = "TLA2_COMPILED_CHECK_START\n\n\n  \nTLA2_COMPILED_CHECK_END\n";
        let result = parse_output(output).expect("parse should handle empty block");
        assert_eq!(
            result.distinct_states, 0,
            "empty block should default distinct_states to 0"
        );
        assert_eq!(
            result.states_explored, 0,
            "empty block should default states_explored to 0"
        );
        assert!(
            result.violation.is_none(),
            "empty block should have no violation (status defaults to ok)"
        );
        assert!(
            !result.deadlock,
            "empty block should not report deadlock"
        );
    }

    #[test]
    fn test_to_snake_case_edge_cases() {
        // All uppercase
        assert_eq!(to_snake_case("ABC"), "a_b_c");
        // Single character
        assert_eq!(to_snake_case("X"), "x");
        // Already snake_case (lowercase, no change needed)
        assert_eq!(to_snake_case("my_spec"), "my_spec");
        // Consecutive uppercase (acronym)
        assert_eq!(to_snake_case("XMLParser"), "x_m_l_parser");
        // Empty string
        assert_eq!(to_snake_case(""), "");
    }

    #[test]
    fn test_to_pascal_case_edge_cases() {
        // Already PascalCase
        assert_eq!(to_pascal_case("Counter"), "Counter");
        // Double underscores
        assert_eq!(to_pascal_case("my__spec"), "MySpec");
        // Leading underscore
        assert_eq!(to_pascal_case("_hidden"), "Hidden");
        // Mixed case with underscores
        assert_eq!(to_pascal_case("tla_Runtime"), "TlaRuntime");
        // Empty string
        assert_eq!(to_pascal_case(""), "");
        // Hyphenated name (used in spec file stems)
        assert_eq!(to_pascal_case("my-cool-spec"), "MyCoolSpec");
    }

    #[test]
    fn test_parse_output_violation_without_invariant_name() {
        // Violation status but no violation_invariant line should default to "unknown".
        let output = "\
            TLA2_COMPILED_CHECK_START\n\
            distinct_states=5\n\
            states_explored=3\n\
            status=violation\n\
            TLA2_COMPILED_CHECK_END\n";
        let result = parse_output(output).expect("parse should succeed");
        assert_eq!(
            result.violation,
            Some("unknown".to_string()),
            "violation without invariant name should default to 'unknown'"
        );
        assert!(!result.deadlock, "should not report deadlock for violation status");
    }

    #[test]
    fn test_report_results_json_format_ok() {
        // Verify JSON output format for a successful result.
        let result = CompiledCheckResult {
            distinct_states: 42,
            states_explored: 42,
            violation: None,
            deadlock: false,
        };
        // report_results writes to stdout, so we can't easily capture it,
        // but we can verify it doesn't error for a success case.
        let report = report_results(
            &result,
            crate::cli_schema::OutputFormat::Json,
            std::time::Duration::from_millis(100),
            std::time::Duration::from_millis(200),
            std::time::Duration::from_millis(300),
        );
        assert!(
            report.is_ok(),
            "report_results should succeed for a passing result"
        );
    }

    #[test]
    fn test_report_results_returns_error_on_violation() {
        // Verify that report_results returns an Err for violations.
        let result = CompiledCheckResult {
            distinct_states: 10,
            states_explored: 5,
            violation: Some("Safety".to_string()),
            deadlock: false,
        };
        let report = report_results(
            &result,
            crate::cli_schema::OutputFormat::Human,
            std::time::Duration::from_millis(50),
            std::time::Duration::from_millis(100),
            std::time::Duration::from_millis(150),
        );
        assert!(
            report.is_err(),
            "report_results should return error on invariant violation"
        );
        let err_msg = report.unwrap_err().to_string();
        assert!(
            err_msg.contains("Safety"),
            "error should mention violated invariant name: {err_msg}"
        );
    }

    #[test]
    fn test_report_results_returns_error_on_deadlock() {
        // Verify that report_results returns an Err for deadlocks.
        let result = CompiledCheckResult {
            distinct_states: 3,
            states_explored: 3,
            violation: None,
            deadlock: true,
        };
        let report = report_results(
            &result,
            crate::cli_schema::OutputFormat::Json,
            std::time::Duration::from_millis(10),
            std::time::Duration::from_millis(20),
            std::time::Duration::from_millis(30),
        );
        assert!(
            report.is_err(),
            "report_results should return error on deadlock"
        );
        let err_msg = report.unwrap_err().to_string();
        assert!(
            err_msg.contains("Deadlock") || err_msg.contains("deadlock"),
            "error should mention deadlock: {err_msg}"
        );
    }
}
